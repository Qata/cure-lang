# Surface dependent matching: impossible clauses + full index refinement — design

**Status:** approved design (autopilot Stage 0). Sub-project ④ of the
case-refinement initiative. Kernel case-refinement unification is complete
(Task 1+2, `5646c63`/`f16d008`) and probed by Antigen (injectivity, no-confusion,
discharge). This surfaces that power into the `.cure` language, aligned with
Idris2.

## 1. Problem

The trusted kernel supports dependent `case` with full first-order index
unification: solution, deletion, injectivity, occurs-check, no-confusion, and
impossible-branch discharge. The **untrusted elaborator** (`Cure.Elab`) does not
surface any of it:

1. **No impossible clauses.** `check_coverage` (`kernel.ex:648`) requires
   `declared ⊆ covered`, so a user must write a branch for every constructor —
   even one that cannot occur at the scrutinee's index. There is no syntax to
   omit or mark such a branch, and `constructor_pattern/1` (`elaborator.ex:470`)
   crashes on any non-`function_call` pattern.
2. **Incomplete per-branch refinement.** The elaborator computes each branch's
   expected type with its OWN one-directional `branch_index_subst`
   (`elaborator.ex:491,536`) and generalizes the motive only over index
   positions that are *bare variables* (`build_motive`/`generalize`,
   `elaborator.ex:314,331` — `{_non_var, _} -> acc` drops the rest). A scrutinee
   whose index is *constructor-headed* (e.g. `Vec a (S m)`), with a result type
   depending on the inner variable, does not refine — even though the kernel
   would accept the fully-built term. The elaborator's comment concedes it:
   "`S(n) := m` refinement is not invertible in this minimal pass"
   (`elaborator.ex:533`).

Both are the same root cause: **the elaborator carries a weaker private copy of
index unification** than the kernel now has.

## 2. Goal / acceptance

A `.cure` program can:

- **(A) Omit impossible branches** — a `match` that lists only the reachable
  constructors elaborates and compiles; a `match` that omits a *reachable*
  constructor is rejected with a clear "missing branch" diagnostic.
- **(A) Mark a branch impossible** — `C(args) -> impossible` elaborates when the
  branch is genuinely unreachable and is rejected (`:reachable_impossible`) when
  it is not (Idris' verified `impossible`).
- **(Completeness) Refine constructor-headed indices** — a dependent `match`
  whose scrutinee index is constructor-headed and whose per-branch result type
  depends on the refined inner variable elaborates and type-checks.

Idris alignment references (from the study): unification verdict taxonomy
`Core/Unify.idr:85`; injectivity/no-confusion `Unify.idr:1148`; case motive
`CaseTree.idr:20` + per-branch refinement `CaseBuilder.idr:909`; verified
`impossible` `ProcessDef.idr:999`; surface `lhs impossible`
(`tests/typedd-book/chapter08/Void.idr`).

## 3. Architecture — one kernel query, elaborator delegates

The kernel keeps ALL unification logic (TCB stays minimal). We add exactly one
public wrapper over the existing private `unify_indices/4`:

```elixir
# lib/cure/core/kernel.ex — the ONLY TCB addition (no new logic)
@spec branch_unify(Env.t(), atom(), atom()) :: {:solved, map()} | :trivial | :impossible
def branch_unify(env, dname, cname)
```

It rebuilds the scrutinee/constructor index vectors exactly as
`check_case_branches` does and returns the same verdict `unify_indices` produces
— `{:solved, subst} | :trivial | :impossible` — where `subst` is the branch
refinement in the branch's de Bruijn frame (`params ++ ctor-args ++ outer`,
identical to how the kernel and `extend_context`/`extend_with_telescope` build
the branch context; the frame-alignment invariant is §8).

The **elaborator delegates** to this query and stops using its own
`branch_index_subst`:

- **Impossibility (A):** `:impossible` ⇒ the branch is discharged (synthesized)
  / an explicit `-> impossible` is accepted; `{:solved,_}|:trivial` on an
  omitted constructor ⇒ "missing branch" error.
- **Refinement (completeness):** use the returned `subst` to compute
  `branch_expected` and to specialize the branch context — replacing the
  incomplete local `branch_index_subst`. `build_motive`/`generalize` is likewise
  extended to abstract each scrutinee index *term* (not only bare vars) into its
  motive binder (whole-subterm replacement up to shifting).

**Soundness stays in the kernel.** The elaborator's use of the query is a
convenience for producing a well-typed Core term; the kernel independently
re-checks (and independently discharges) the final `{:case,…}`. A wrong
elaborator decision cannot produce an accepted-but-ill-typed program — at worst
a spurious elaboration error, never unsoundness. This is the same trust boundary
as the rest of `Cure.Elab`.

## 4. Surface syntax

Reuse the existing `match`/arm grammar (`parser.ex:1362,1432`). Two additions:

1. **Omission** — no grammar change; a `match` may list a subset of
   constructors. Coverage of the *reachable* set is enforced by the elaborator
   (§5), the kernel remains the backstop.
2. **Explicit impossible arm** — `pattern -> impossible`, where `impossible` is a
   keyword body. Parsed as a normal arm with an `impossible: true` marker in the
   arm meta (no new statement form). Chosen over Idris' post-LHS `impossible`
   because Cure `match` is expression-arm-based, not clause-based; `-> impossible`
   is the natural fit and needs only a keyword check in `parse_match_arm`.

`_` / variable / literal patterns are out of scope here (constructor patterns
only, as today) EXCEPT that `constructor_pattern/1` must stop crashing on them —
it returns a clean `{:error, {:unsupported_pattern, …}}` instead (§5).

## 5. Elaborator behavior (untrusted)

`elaborate_match` gains a coverage/discharge pass:

1. Elaborate the scrutinee; get `dname`, params, indices (as today).
2. Partition declared constructors into **matched** (a surface arm), **explicit
   impossible** (`-> impossible` arm), and **omitted** (no arm).
3. For each **matched** constructor: elaborate its body against `branch_expected`
   computed from `branch_unify`'s `subst` (not the old local subst).
4. For each **explicit-impossible** constructor: require
   `branch_unify(env,dname,cname) == :impossible`; else
   `{:error, {:reachable_impossible, cname}}`. Emit a discharged branch.
5. For each **omitted** constructor: if `branch_unify == :impossible`, synthesize
   a discharged branch; else `{:error, {:missing_branch, cname}}`.
6. Assemble `{:case, scrut, motive, branches}` with a branch for EVERY declared
   constructor (matched + discharged), so the kernel's `check_coverage` passes
   unchanged. The kernel then re-validates: it independently discharges the
   impossible ones and checks the reachable bodies.

**Discharged-branch body.** A synthesized/impossible branch needs a
structurally-valid placeholder body the kernel will not check (it discharges the
branch). Use a canonical marker term `{:absurd}` (new Core leaf, evaluated
never — it only ever sits in a discharged branch). The kernel's
`check_case_branches` already skips the body for `:impossible`; `{:absurd}`
requires no kernel typing rule. *Alternative considered and rejected:* reuse
`{:hole,_}` — rejected because the kernel accepts holes at any type
(`kernel.ex` hole rule), which would let a *reachable* omitted branch slip
through if the elaborator's verdict ever disagreed with the kernel's; a body the
kernel canNOT accept when checked is the safer backstop. `{:absurd}` has no
`check` rule, so a reachable branch carrying it is rejected by the kernel — the
belt to the elaborator's suspenders.

**`{:absurd}` surface cost (must be handled in Slice 2).** A new Core leaf is
touched by more than the kernel: `Serialize` (C2 encode/decode — discharged
branches appear in serialized terms), and codegen/erase (a discharged branch is
never reached at runtime but still needs an emitted body — lower it to an
`error/1`-style unreachable stub). These are enumerated so the plan covers them;
none add a *typing* rule. NOTE: because the elaborator only synthesizes a
discharged branch when `branch_unify == :impossible` — the SAME function the
kernel discharges on — the elaborator and kernel cannot disagree, so even the
`{:hole,_}` alternative would never actually be checked; `{:absurd}` is chosen
purely for defense-in-depth (a body the kernel rejects if the invariant ever
broke). If the review judges the new-leaf surface not worth that margin, falling
back to `{:hole,_}` is sound given the same-function invariant — this is the one
open decision for Stage-1 review.

## 6. Slices (implementation order)

- **Slice 1 — kernel query.** `branch_unify/3` + unit tests (mirrors the
  `case_soundness_index_test` fixtures). No behavior change yet.
- **Slice 2 — impossible clauses (A).** Parser `-> impossible`; elaborator
  coverage/discharge pass; `{:absurd}` Core leaf (elaborator-only, kernel
  discharge already handles it); harden `constructor_pattern`. Surface tests:
  omit-impossible compiles, omit-reachable errors, explicit-impossible verified,
  mis-marked-impossible rejected.
- **Slice 3 — refinement completeness.** Elaborator consumes `branch_unify`'s
  `subst` for `branch_expected`/context specialization; extend
  `build_motive`/`generalize` to abstract constructor-headed index terms. Surface
  test: a dependent match on a constructor-headed index whose result type depends
  on the refined inner variable elaborates + runs.

Each slice is independently green + committed. Slices 2 and 3 both depend on
Slice 1.

## 7. Testing

- Kernel: `branch_unify/3` unit tests (impossible / solved / trivial), reusing
  the Ix/Foo/IW fixtures already in `case_soundness_index_test.exs`.
- Surface (`.cure` source through `Cure.Elab.Program.elaborate`): positive +
  negative programs per Slice 2/3 acceptance in §2. Negatives assert the exact
  error atom (`:missing_branch`, `:reachable_impossible`).
- Antigen: the existing indexed-case vertical (injectivity/discharge antibodies)
  and ③ `rewrite/eq` MUST stay green — they guard the kernel the elaborator now
  leans on. No new Antigen vertical required (this is surface/elaborator work,
  outside the TCB); a `.cure`-level regression corpus is the surface analogue.
- Full suite once per slice; baseline 2173, zero regressions.

## 8. Invariants / soundness boundary

1. **TCB delta = one wrapper.** `branch_unify/3` adds no unification logic; it
   reuses `unify_indices/4`. `{:absurd}` is an elaborator-only leaf with no
   kernel typing rule (so it is only ever valid in a discharged position).
2. **Kernel is the backstop.** Every emitted `{:case,…}` is fully re-checked and
   re-discharged by the kernel; the elaborator's coverage/impossibility decisions
   are ergonomic, never trusted for soundness. A disagreement yields an
   elaboration or kernel error, never an accepted ill-typed program.
3. **Frame alignment.** `branch_unify`'s `subst` is in the branch de Bruijn frame
   the elaborator's `extend_context` builds (`params ++ ctor-args ++ outer`);
   Slice 1 tests pin this against a hand-built branch context before Slice 3
   consumes it.
4. **No coverage weakening in the kernel.** `check_coverage` is unchanged; the
   elaborator always emits a full constructor set (matched + discharged).
5. Ghost-written commits; one build at a time; OTP 26–28.

## 9. Out of scope (future)

- Non-constructor patterns (`_`, literals, nested) — only cleaner rejection here.
- Nested/deep pattern compilation to a case tree (Cure matches one level today).
- Metavariable/postponed-constraint unification at the surface (Idris'
  flex-flex) — the elaborator's separate `Cure.Elab.Unify` already covers
  inference metas; branch refinement is first-order and complete without it.
