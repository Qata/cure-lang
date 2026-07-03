# Postponed/Suspended Unification Constraints (#11) — Design Spec

**Date:** 2026-07-03
**Roadmap row:** #11 (Inference unification — postponed/suspended constraints)
**Layer:** E (untrusted elaborator) — `lib/cure/elab/unify.ex` + the elaborator's
per-definition kernel-handoff boundary. **No `lib/cure/core/*` change; no TCB.**
**Reference:** Abel & Pientka, "Extensions to Miller's Pattern Unification for
Dependent Types and Records," MSCS 2018 (`~/Downloads/unif_miller60.pdf`), plus a
cross-read of Idris2, Agda, and Lean4 constraint solvers (findings in §7).

---

## 1. Problem & goal

Cure's unifier (`Cure.Elab.Unify`) is **eager**: `unify/4` either solves a
metavariable now or fails (`{:ok, ctx} | {:error, reason}`). Two situations that
Idris/Agda *postpone and later solve* are today hard-rejected:

1. **Flex-flex** — both sides are metavariable-headed and neither is a Miller
   pattern (`?a =? ?b`, or `?a x =? ?b y` off-pattern). The correct solution may
   become determined once some *other* constraint pins one side; eager failure
   loses that input.
2. **Weakly-rigid occurs** — a metavariable occurs in its own candidate solution,
   but only under another metavariable application or an eliminable position
   (`?a =? f(?a)` where `f` may cancel, `?a =? fst(?a, c)`). Such a constraint is
   *solvable* once the eliminable reduces away; only **strongly-rigid**
   occurrences (`?a =? S(?a)`, under a data constructor / type former) are truly
   cyclic. Cure's `Unify.occurs?` (unify.ex:382) rejects **any** occurrence — it
   is sound but over-rejects, costing reach.

**Goal.** Add a *constraint-postponement queue* with *retry-on-progress* so the
unifier can suspend a not-yet-solvable constraint, keep elaborating, retry the
queue to a fixpoint as metavariables get solved, and reject only if the queue
cannot be fully drained. Refine the occurs-check to postpone weakly-rigid
occurrences instead of failing them. This reaches inputs Idris accepts via
postponement.

**Non-goal for soundness.** All of this is E-layer. The trusted kernel re-checks
every elaborated term (`Unify.zonk/2` must produce a `{:meta,_}`-free term before
handoff), so optimistic postponement is a **completeness** concern only — a wrong
suspension/solve is caught downstream by the kernel. This mirrors the
conservative-fallthrough stance of the landed Miller solver (#10).

---

## 2. Success criterion & risk gate (FIRST task, gates everything)

The very first implementation task authors a **failing differential-oracle probe**:
a surface Cure program that `idris2 --check` **accepts** (via postponement) and
that Cure **currently rejects**. Concretely `postpone01_flex_flex` (§5).

- If such a probe is constructed and Cure rejects it while Idris accepts → the
  gap is real and oracle-measurable; proceed with the build.
- **If no surface Cure program can be made to trigger genuine flex-flex or
  weakly-rigid-occurs** that Idris accepts → the feature has **no
  oracle-measurable reach**. **HALT** and report (write `AUTOPILOT-STATE.md`),
  reconsidering scope, rather than building machinery no probe exercises.

This gate exists because earlier probing in this problem area was repeatedly
*confounded* (arity errors, general elaboration failures masquerading as the
target). The probe reason must be **verified** (dump the actual Cure rejection
reason via the throwaway-test pattern — `mix run` cannot be used because it
throws `unknown registry: Cure.Pipeline.Events.Registry`; a test-env module that
calls `Cure.Elab.Program.elaborate/1` and `IO.inspect`s the error works), and the
Idris verdict must come from the oracle, never hand-written.

---

## 3. Architecture — Option (A): MetaCtx queue + retry-all fixpoint drain

Chosen after cross-reading the three reference systems (§7). Rationale: Cure's
`MetaCtx` is **already an immutable threaded state** (a functional analogue of
Idris's global `UState`). Idris and Lean both store constraints in their threaded
state and drain at a definition boundary — Option (A). This needs **no 3-valued
`unify` result threaded through every caller** (Cure has many `unify` call sites);
callers stay `{:ok, ctx} | {:error, reason}`.

### 3.1 Storage — a queue field on `MetaCtx`

`MetaCtx` (unify.ex:12) today: `defstruct next: 0, solutions: %{}, types: %{}`.
Add a `constraints: []` field holding suspended equations:

```
constraints :: [ {a :: uterm(), b :: uterm(), depth :: non_neg_integer(),
                  sig :: term() | nil, reason :: atom()} ]
```

Each entry is a deferred `unify_d(a, b, ctx, sig, depth)` — the exact arguments
needed to retry it verbatim, plus a `reason` tag (`:flex_flex` |
`:weak_rigid_occurs`) for diagnostics. `depth` is captured because the two terms
were forced under `depth` binders; retry must re-enter at that depth (§3.4).

New `MetaCtx` helpers (all pure, alongside `put_solution/3`):
- `postpone(ctx, a, b, depth, sig, reason)` — append a constraint.
- `constraints(ctx)` — list them.
- `clear_constraints(ctx)` — return `{ctx_without, list}` for the drain loop.
- `put_constraints(ctx, list)` — replace the queue (drain writes back the
  still-unsolved remainder).

### 3.2 Postponement triggers (where `unify` suspends instead of failing)

Both live in `do_unify`/`do_unify_struct` (unify.ex:136–241) and in the two solve
paths. In every case the trigger **appends a constraint and returns `{:ok, ctx}`**
(Idris's optimistic model) rather than `{:error, …}`:

1. **Flex-flex.** In `do_unify_struct`, when both `t1` and `t2` are
   metavariable-headed (`{:meta,_}`-applied spines) and the Miller dispatch
   already fell through (neither side is a solvable pattern) → `postpone(…,
   :flex_flex)` instead of the structural mismatch error. Guard: at least one side
   must be genuinely a metavariable head (a solved meta is `force`d away first, so
   this only fires on *unsolved* metas).
2. **Weakly-rigid occurs.** `occurs?/3` (unify.ex:382) is refined into
   `occurs_rigidity/3 → :strong | :weak | :none` (§3.3). The two callers change:
   - `miller_solve` (unify.ex:159, occurs at :166): `:none` → solve as today;
     `:weak` → **fall through** to structural (which then postpones as flex-rigid,
     see below); `:strong` → `:fallthrough` (cyclic; ultimately unsolved).
   - `solve_strengthened` (unify.ex:334): `:none` → `put_solution`; `:weak` →
     `postpone(…, :weak_rigid_occurs)` returning `{:ok, ctx}`; `:strong` →
     `{:error, {:occurs_check, id, t}}` (unchanged hard failure).

   A **flex-rigid weak occurrence** (metavar vs rigid term where the metavar
   occurs weakly-rigidly in the rigid side) is postponed, not solved: it may
   become solvable after the interfering metavar resolves.

### 3.3 Occurs-check rigidity classification (`occurs_rigidity/3`)

Replaces the boolean `occurs?`. Walk `force(t, ctx)` tracking a rigidity mode
(`:strong` at entry, per Agda's `occursCheck` starting `StronglyRigid`):

- Hit `{:meta, ^id}` → return current mode (`:strong` or `:weak`).
- Hit `{:meta, _other}` → occurrences *inside its arguments* are `:weak`
  (metavar application is a flexible position — Agda `Flexible`/`WeaklyRigid`).
- Descend under a **data constructor** `{:ctor,_,args}` / **type former**
  `{:data,_,_,_}` / `{:pi,…}` / `{:sigma,…}` → arguments stay `:strong`
  (Agda `strongly`: under an inductive constructor stays StronglyRigid).
- Descend under an **eliminable / neutral** head — `{:app, f, x}` where `f` is
  **not** a constructor/data spine (application of a variable, global, or
  metavar), `{:fst,_}`, `{:snd,_}`, `{:prim,_,_}` → arguments become `:weak`
  (Agda `weakly`: args to variables/definitions are WeaklyRigid).
- Combine results by **strength**: `:strong` beats `:weak` beats `:none`
  (`:strong` if any strongly-rigid occurrence exists, else `:weak` if any weak
  occurrence, else `:none`).

The mapping to the Core term shapes must be verified against the actual
constructors used in `zonk`/`escapes?` (unify.ex:354–377 enumerates them:
`:var :meta :pi :lam :sigma :app :pair :fst :snd :eq :refl :prim :data :ctor`).
Classification of each shape as constructor/type-former (strong-preserving) vs
eliminable/neutral (weak-inducing) is fixed by that enumeration and pinned in the
plan; **no shape may be silently defaulted** — an unlisted shape is treated as
`:strong`-preserving (conservative: never under-reject into unsoundness, and the
kernel backstops regardless).

### 3.4 Retry driver — `drain_constraints/1` (retry-all fixpoint)

Idris/Lean style: **retry-all-while-progress**, no blocker-keying (Agda's
selective wakeup is deferred as premature at Cure's scale — §7, all three readers
concur). Signature `drain_constraints(ctx) :: {:ok, ctx} | {:error, reason}`:

```
drain(ctx):
  {ctx0, pending} = clear_constraints(ctx)
  if pending == []: return {:ok, ctx0}
  # retry each once; each may re-postpone (re-append) or solve or hard-fail
  ctx1 = ctx0
  for {a,b,depth,sig,_} in pending:
    case unify_d(a, b, ctx1, sig, depth):
      {:ok, ctx1'} -> ctx1 = ctx1'          # solved OR re-postponed (into queue)
      {:error, e}  -> return {:error, e}     # strong-rigid cycle / genuine mismatch
  {_, still} = clear_constraints(ctx1)  # peek remainder produced this round
  progress? = solved_count(ctx1) > solved_count(ctx0)   # ≥1 metavar newly solved
  cond:
    still == []          -> {:ok, ctx1}                  # fully drained
    progress?            -> drain(put_constraints(ctx1, still))  # loop
    true                 -> {:error, {:unsolved_constraints, still}}  # stalled
```

- **Progress metric.** A round makes progress iff the count of solved
  metavariables strictly increased (`map_size(solutions)`), i.e. a re-attempt
  pinned at least one meta. Re-postponing the same constraint with no new solution
  is *not* progress.
- **Termination.** Metavariables are finite and monotonically solved (a solution
  is never retracted). Each non-halting round solves ≥1, so the loop runs at most
  (number of metavariables) times. Guaranteed terminating — an explicit unit test
  asserts termination on a deliberately-stalled queue (`postpone04`).
- **Stall = reject.** A non-empty stalled queue is a clean `{:error,
  {:unsolved_constraints, …}}` (Lean's final strict no-postpone pass; Idris's
  `checkUserHolesAfter` → `CantSolveEq`). No optimistic acceptance of unsolved
  constraints.

### 3.5 Integration point — the per-definition boundary

`drain_constraints/1` runs **once per top-level definition, after all its
unifications, immediately before the terminal `zonk`/`has_meta?` kernel-handoff
gate**. Candidate call sites (exact one pinned in the plan by tracing where a
definition's elaborated body is finalized):
- `lib/cure/elab/elaborator.ex:651` (`if Unify.has_meta?(expected_core)` — the
  checked-expression gate), and/or
- the per-declaration finalize in `lib/cure/elab/program.ex` /
  `lib/cure/elab/declarations.ex` where each function's Core term is zonked before
  kernel check.

Requirement: after `drain_constraints/1` returns `{:ok, ctx}`, the existing
`has_meta?` gate still runs (a metavar with no constraint but never solved is
still an error, exactly as today). `drain` only converts "suspended constraints"
into either solutions (which `zonk` then substitutes) or a clean rejection. If
`drain` returns `{:error, …}`, that becomes the definition's elaboration error.

**Idempotence/order:** draining before `zonk` guarantees `zonk` sees a queue-free
ctx; `zonk` itself is unchanged. Nested/local unify calls within one definition do
**not** drain — only the definition boundary does — so a constraint suspended
early can be solved by a unification arising later in the same definition.

---

## 4. Data & control-flow summary

- `unify/4` public contract **unchanged**: `{:ok, ctx} | {:error, reason}`.
  Internally it may now enqueue constraints into `ctx` and still return `{:ok,
  ctx}`.
- New internal surface: `MetaCtx.{postpone,constraints,clear_constraints,
  put_constraints}` + `Unify.occurs_rigidity/3` (replacing `occurs?/3`) +
  `Unify.drain_constraints/1`.
- One elaborator call site gains a `drain_constraints/1` step before the
  definition's `has_meta?` gate.

---

## 5. Oracle probes (`test/oracle/postpone/`)

Red-green plus soundness guards. Each is a faithful paired transliteration
(`.cure` + `.idr` with `%default total`, no `module` line); verdicts come from
`mix cure.oracle postpone`, never hand-written; the fixture is frozen into
`verdicts.json` and replayed by `test/oracle_replay_test.exs`.

1. **`postpone01_flex_flex`** — *the verdict-flip probe* (accept/accept). An
   implicit whose value is determined only by a later use, so the first constraint
   is flex-flex and gets pinned on retry. Before the feature: Cure **reject**,
   Idris **accept** (relation `cure_stricter` transiently → becomes `same` after
   the fix). The concrete program is authored in Task 1 and its pre-fix Cure
   rejection reason is verified; if it cannot be made to reject-for-the-right-reason,
   the risk gate (§2) fires.
2. **`postpone02_weak_rigid_occurs`** — (accept/accept). A metavar occurs
   weakly-rigidly in its candidate solution (under a metavar app / eliminable),
   solvable after another meta pins the eliminable away. Exercises §3.3 `:weak`.
3. **`postpone03_strong_rigid_cycle_neg`** — (reject/reject). Genuinely cyclic
   (`?a =? S(?a)` under a constructor). Guards against the occurs-refinement
   **over-accepting**: `:strong` must still hard-fail. Idris rejects
   (`OccursCheck`/cyclic); Cure rejects (`:occurs_check`).
4. **`postpone04_unsolved_neg`** — (reject/reject). Flex-flex that is **never**
   pinned by any later constraint. Both reject: Idris `UnsolvedMetas`, Cure
   `{:unsolved_constraints, …}`. Also serves as the driver **termination** witness
   (the stalled queue must terminate-then-reject, not loop).

If a probe's intended pre-fix verdict cannot be reproduced (e.g. Idris also
rejects `postpone01`, or Cure already accepts it), that probe is **not** frozen as
a divergence; the discrepancy is investigated first (skill's triage contract — a
general bug must be ruled out before labeling anything `cure_stricter`).

---

## 6. Testing discipline (strict red-green, immutable once green)

Per task, in order, one build at a time (never two `mix` suites concurrently):

- **Unit (ExUnit) tests** for the pure pieces, each written **failing first**:
  - `occurs_rigidity/3` classification table: strong/weak/none on hand-built Core
    terms (constructor-nested, meta-app-nested, projection-nested, none).
  - `MetaCtx` queue helpers (postpone/clear/put round-trips).
  - `drain_constraints/1`: solves a pinnable queue; **terminates and rejects** a
    stalled queue (asserts no infinite loop — bounded via the finite-metavar
    argument, tested with an explicit stalled fixture).
- **Oracle probes** (§5) as the behavioral red-green: author probe → run oracle →
  confirm pre-fix divergence → implement → confirm verdict flips → **no other
  probe regresses** → `mix test test/oracle_replay_test.exs` green before commit.
- Tests are behavioral (assert verdicts/classifications, not internal call
  shapes) and immutable once green.
- **Full suite** (`mix test`) run **once, alone**, at the Stage-5 gate.

---

## 7. Reference-system findings (design provenance)

Cross-read of the three mature dependent-type unifiers (Idris2 vendored-pinned;
Agda/Lean live clones, unpinned — inspiration, not oracle ground truth):

| | Idris2 | Agda | Lean4 |
|---|---|---|---|
| Store | global `UState.constraints` (IntMap) + `guesses` | awake/sleeping queues, blocker-keyed | `syntheticMVars`+`pendingMVars`+`dAssignment` |
| Retry | **retry-ALL fixpoint** while progress (`solveConstraints`, Unify.idr:1514) | **selective** blocker-keyed wakeup (`wakeupConstraints`, Constraints.hs:249) | **progress-flag fixpoint** + final strict pass (`synthesizeSyntheticMVars`, SyntheticMVars.lean:611) |
| Weak-rigid occurs | postpone (`failOnStrongRigid`, Unify.idr:387) | postpone (`abort` soft via `FlexRig'`, Occurs.hs:384) | **fail immediately** (`checkMVar`, ExprDefEq.lean:878) |
| Leftover | `checkUserHolesAfter`→`CantSolveEq` | `UnsolvedConstraints` | `reportStuckSyntheticMVars` |

**Adopted:** Idris/Lean retry-all-while-progress fixpoint; Agda/Idris
weak-vs-strong-rigid occurs split (Agda's `FlexRig'` is the canonical match to
Abel & Pientka); Idris/Lean threaded-state storage drained at a definition
boundary (→ Cure Option A). **Deferred:** Agda's blocker-keyed selective wakeup
(premature at Cure's scale — all three readers concur). Lean's occurs-fails-
immediately path was **not** adopted (it loses the reach we want; Idris/Agda
postpone, and the kernel backstops us either way).

---

## 8. Scope boundaries

**In scope:** techniques (A) postponement/constraint-queue + (B) weak-rigid
occurs refinement, together (they are coupled — §1: B flips no verdict without A).

**Out of scope (deferred, on-demand):**
- (C) Σ-flattening / projection elimination (`?m (fst y) (snd y)` → pattern form).
  Do when a projection-inference oracle probe actually fails.
- Blocker-keyed selective wakeup (Agda). Add only if profiling shows O(n²)
  re-solving at realistic scale.
- Contextual-metavariable representation (`u[σ]` closures). Skipped per roadmap
  (a representation rewrite, not a capability).

## 9. Definition of done

- Risk gate (§2) passed: `postpone01` reproduced pre-fix divergence.
- All four oracle probes at intended verdicts; frozen; replay green.
- Unit tests (occurs_rigidity, queue helpers, drain incl. termination) green.
- Full `mix test` green (run once, alone).
- Roadmap §2 row #11 updated from open → landed, with the four probe names and the
  no-TCB / kernel-backstop note.
- No `lib/cure/core/*` diff (verified: `git diff --stat` touches only
  `lib/cure/elab/*`, `test/**`, `docs/**`).
