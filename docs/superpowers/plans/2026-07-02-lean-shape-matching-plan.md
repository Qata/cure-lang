# Lean-Shape Dependent Pattern Matching (Safe FRP) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: use `superpowers:executing-plans` (autopilot Stage 4, inline on Opus) with the `cure-porting` domain skill. Steps use checkbox (`- [ ]`) syntax. This plan is **oracle-driven**: for kernel/elaborator phases the exact diff emerges from a named failing probe — each task fixes its red test by diagnosis, never by a pre-guessed patch. Do NOT fabricate "complete code" for a diff that must be discovered; the red test + procedure + gate ARE the task contract.

**Goal:** Give Cure one unification-driven, context-generalizing `match`/`with` equation-compiler that subsumes today's A/B/C `with` paths and is strong enough to type-check the Sculthorpe–Nilsson Safe-FRP `SF` family (computed `++`/`∧` indices) in Cure.

**Architecture:** Elaborator equation-compiler (E) emitting kernel-checked `{:case}` trees over Cure's existing five-rule `unify_indices` (already landed); carried stuck-index equalities discharged by Cure's existing `rewrite` + a type-level lemma stock; TCB touched only where a phase proves an E-only route impossible (expected: Phase 5 signature-aware `reify`). Governing spec: `docs/superpowers/specs/2026-07-02-lean-shape-matching-design.md`.

**Tech Stack:** Elixir (Cure compiler); differential oracle (`mix cure.oracle <cluster>`, `idris2` at `~/Develop/Idris2/build/exec/idris2`); Antigen (StreamData property assays under `mix test`); Lean reference at `~/Develop/lean4`.

## Global Constraints (verbatim from spec §8 — every task inherits these)

- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no `Co-Authored-By`, no Claude signature.
- **Explicit-pathspec staging only:** `git add -- <path>`; never `git add -A`/`.`. Work on the isolated worktree `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/lean-shape-matching` (branch `autopilot/lean-shape-matching`).
- **One build at a time.** Never two concurrent `mix` suites (a past concurrent full-suite run panicked the kernel). Scoped `mix test <file>`; full suite once, alone, at a gate.
- **Tests immutable once green**; behavioral, not implementation-coupled.
- **Reference-grounded:** verify against vendored Idris2/Agda AND `~/Develop/lean4`, never memory. Dump real normal forms when reasoning about conversion.
- **TCB gate (any `lib/cure/core/*` diff):** HARD-STOP-and-review — red-green + a new Antigen antibody proving the change terminates and equates no distinct normal forms + full Antigen + full suite + an **independent adversarial-verification subagent** (fresh context, tries to break soundness). Per `elaborator-hard-stop-principle`, first prove no E-only term closes the gap. **No auto-merge.**
- **Baseline:** capture `mix test` pass count at Phase 0 start; "0 regressions" is measured against it at every gate.

---

## Phase 0 — Acceptance oracle (E/none; non-TCB)

**Goal:** A minimal faithful `SF` probe that is **red in Cure for the stuck-`++`-index reason** and green in Idris — the anchor for "done."

### Task 0.1: Baseline + faithful minimal SF probe (Idris green, Cure red)

**Files:**
- Create: `test/oracle/frp/frp01_par_assoc.cure`, `test/oracle/frp/frp01_par_assoc.idr`
- Create: `test/oracle/frp/frp02_seq_meet.cure`, `test/oracle/frp/frp02_seq_meet.idr`
- Touch (regen): `test/oracle/frp/verdicts.json`

**Interfaces:**
- Produces: the `frp` oracle cluster; the concrete Cure error id for the stuck-`++` case (recorded in the task note — consumed by Phases 2/3/4 as the red target).

- [ ] **Step 1: record baseline.** Run `mix test 2>&1 | tail -3`; note the pass count in the task note (the regression baseline).
- [ ] **Step 2: write the Idris probe** (`frp01_par_assoc.idr`), `%default total`, no `module` line. Minimal faithful core:
  ```idris
  %default total
  data Sig = SigC | SigE
  data Dec = DDec | DCau
  dmeet : Dec -> Dec -> Dec
  dmeet DDec DDec = DDec
  dmeet _ _ = DCau
  data SF : List Sig -> List Sig -> Dec -> Type where
    Prim : SF as bs DCau
    Seq  : SF as bs d1 -> SF bs cs d2 -> SF as cs (dmeet d1 d2)
    Par  : SF as bs d1 -> SF cs ds d2 -> SF (as ++ cs) (bs ++ ds) (dmeet d1 d2)
  -- acceptance driver: re-associating parallel composition needs (as ++ bs) ++ cs = as ++ (bs ++ cs)
  parAssoc : SF ((as ++ bs) ++ cs) ((xs ++ ys) ++ zs) d
          -> SF (as ++ (bs ++ cs)) (xs ++ (ys ++ zs)) d
  parAssoc sf = ?assoc_hole   -- Idris: the rewrite is via `rewrite appendAssociative ...`
  ```
  Refine until `idris2 --check` passes (fill `parAssoc` with the real `rewrite appendAssociative` proof so it is genuinely total-accepted, not a hole). The point: a function whose well-typedness *requires* `++` associativity.
- [ ] **Step 3: write the faithful Cure transliteration** (`frp01_par_assoc.cure`) — same `SF` family (Cure `type … indices (…)`), same `parAssoc` signature and intended `rewrite` body. Same signature, faithful — not a different proof.
- [ ] **Step 4: run the oracle.** `mix cure.oracle frp` — writes `verdicts.json`. Expect `frp01`: Cure `reject`, Idris `accept` → a reach input.
- [ ] **Step 5: confirm red-for-the-right-reason.** Elaborate `frp01_par_assoc.cure` directly (a scoped `iex`/`mix run` snippet or `Cure.Elab.Program.elaborate/1`); confirm the error is the **stuck computed-index / rewrite-through-`++`** failure, NOT a parse/kind/unrelated error. Record the exact error id in the task note. If it fails for an unrelated reason, fix the probe until the failure is the intended one.
- [ ] **Step 6: add `frp02_seq_meet`** — a `Seq` composition needing only `dmeet` (∧) refinement, no `++`. This one may already be `accept/accept` (isolates the Dec-index path from the list-index path); record which.
- [ ] **Step 7: set relations + commit.** In `verdicts.json`, mark `frp01` `cure_stricter` with reason `"reach: stuck ++-index rewrite (the Phase-4 acceptance target); flips to same when the lemma stock + rewrite composition land"`; `frp02` per its actual verdict. Run `mix test test/oracle_replay_test.exs` (green replay). Commit `test(oracle): frp acceptance cluster — minimal SF, stuck-++-index reach (frp01) + Dec-meet (frp02)`.

**Gate:** oracle_replay green; `frp01` red-for-the-right-reason with its error id recorded; baseline pass count recorded.

---

## Phase 1 — Unifier audit (TCB only if a real gap is found)

**Goal:** Confirm the already-landed five-rule `unify_indices` (`kernel.ex:787-885`) exposes what the Phase-3 front-end needs; open a TCB diff only if the audit finds a real gap.

### Task 1.1: Audit `unify_indices` against the front-end's needs

**Files:** Read-only audit of `lib/cure/core/kernel.ex:787-885`, `2026-07-01-case-index-unification-design.md`, `~/Develop/lean4/src/Lean/Meta/Tactic/UnifyEq.lean`. Create: `docs/superpowers/notes/2026-07-02-unifier-audit.md`.

- [ ] **Step 1: Lean re-check.** Read `UnifyEq.lean` + `Meta/Tactic/Cases.lean`; note (in the audit doc) how Lean's `unifyEq?` classifies solution/injectivity/conflict/cycle and what it returns for a stuck non-injective application. Ground the audit against this.
- [ ] **Step 2: enumerate the front-end's demands.** For each of the five rules, write in the audit doc: does `unify_indices` expose the outcome the generalizing front-end (Phase 3) needs — specifically (a) does it return the branch substitution *and* a stuck-residual (the equations it could NOT solve) so Phase 2 can carry them? (b) does conflict yield `:impossible` for `{:absurd}`? (c) does occurs/cycle degrade to `:undecided` (never `:impossible`)?
- [ ] **Step 3: probe the stuck-residual question** with a scoped throwaway test: call `unify_indices` on `[as ++ cs]` vs `[fresh_var]` and inspect the return. Record whether the stuck equation is surfaced or swallowed.
- [ ] **Step 4: decide.** If the unifier already surfaces stuck residuals usably → Phase 1 closes with **no TCB diff** (audit doc committed). If it swallows them (Phase 2 can't get at the carried equation) → that is the real gap: define the minimal change (return the residual), and **escalate to the TCB gate** (red-green + antibody: "unifier terminates + never equates distinct NFs + conflict⇒`:impossible` (never cycle) + stuck residual surfaced faithfully" + full suites + independent adversarial verification). Antibody must NOT require cycle⇒`:impossible`.
- [ ] **Step 5: commit** the audit doc (`docs(notes): unifier audit — <gap|no-gap> for the generalizing front-end`), plus the kernel diff + antibody as a **separate** commit only if Step 4 found a gap.

**Gate:** audit doc committed with an explicit no-gap/gap verdict; if a gap, the TCB gate fully green.

---

## Phase 2 — Carried equalities (E-first; escalate to TCB only on a proven wall)

**Goal:** Stuck unification carries an `Eq` into the motive instead of falling through unrefined — via the E-only generalization of capability B, escalating only on a named blocked kernel judgement.

### Task 2.1: E-only carried-index-equality (red → green on a non-indexed carrier)

**Files:** Modify `lib/cure/elab/elaborator.ex` (the with/match motive path). Test: `test/cure/elab/carried_index_eq_test.exs`.

**Interfaces:**
- Consumes: capability-B Eq-arrow motive `λw. Eq(T,e,w) → G[e↦w]` (existing); `unify_indices` stuck residual (Phase 1).
- Produces: `elaborate_*` emits, for a stuck index equation over a **non-indexed carrier** (`SVDesc = List Sig`, `Dec`), a branch motive `Π(Eq(carrier, lhs, rhs), G)` the kernel accepts.

- [ ] **Step 1: Lean re-check.** Re-read spec §2's correction + `Match.lean:210-284`: confirm this is a Cure-specific automation of opt-in `match h : e`, NOT inherited Lean auto-behavior. Note it in the task.
- [ ] **Step 2: red test.** A minimal Cure def that pattern-matches a value whose type carries a stuck `List`-index equation (a shrunk `frp01`, non-indexed carrier), asserting the body type-checks using the carried `Eq`. Confirm it FAILS today (`mix test test/cure/elab/carried_index_eq_test.exs` — red), with the error recorded.
- [ ] **Step 3: implement E-only.** Generalize capability B's Eq-arrow motive construction from scrutinee-*value* equations to the stuck-*index* equation surfaced by Phase 1 — carrier type = the index's (non-indexed) type. Reuse `check_motive_wf`'s existing acceptance of `Π(Eq(ty,a,b),G)` (`kernel.ex:597-689`, the `defc6cb` fix). **No `lib/cure/core/*` edit** in this step.
- [ ] **Step 4: green.** `mix test test/cure/elab/carried_index_eq_test.exs` passes; the carried `Eq` is load-bearing (toggle it off → fails).
- [ ] **Step 5: escalation check.** If Step 3 hits a concrete blocked kernel judgement — the expected candidate is *an Eq endpoint that is itself an indexed-family value* (the `Quote.reify` collapse) — STOP: that is Phase 5's territory. Per the spec ordering contingency, **pull Phase 5 forward** (do Task 5.1 now), then resume. Only if Phase 5's fix still doesn't close it, open a Phase-2 TCB gate with the antibody "a carried-eq branch is sound iff the kernel independently re-derives the equation use-site well-typedness."
- [ ] **Step 6: regression + commit.** Scoped: `with_abstraction_test`, `with_rematch_elab_test`, `dependent_match_surface_test` (each alone). Commit `feat(elab): carry stuck computed-index equalities into the branch motive (E-only)`. If Phase 2 closed E-only, note "Phase-2 TCB listing (spec §3) removed" and drop it from the spec in the same commit.

**Gate:** carried-index-eq test green + load-bearing; no regressions; Phase-2 layer classification (E-only vs escalated) recorded.

---

## Phase 3 — Generalizing match front-end (E) + retire A/B/C

**Goal:** One equation-compiler path composing (1a) dependency-reversion + (1b) occurrence-abstraction, running the per-branch unifier + carried eqs, emitting nested case trees; retire A, then B, then C as each is provably subsumed.

### Task 3.1: The composed generalizing motive ((1a)+(1b) together)

**Files:** Modify `lib/cure/elab/elaborator.ex`. Test: `test/cure/elab/generalizing_match_test.exs`.

- [ ] **Step 1: Lean re-check.** Read `Match.lean:879-916` (automatic `generalize` / dependency reversion) + the occurrence-abstraction idiom; note how Lean composes reverting dependent hyps with the discriminant. Ground the composition against it.
- [ ] **Step 2: red test.** A case needing BOTH mechanisms at once — an indexed with-rematch (capability C) whose goal ALSO names the scrutinee value directly (capability A), in one clause. Confirm it fails today (today's `elaborate_with_rematch` takes no such combined motive). Record the error.
- [ ] **Step 3: implement the combined motive** — (1a) revert sibling context entries whose type depends on the scrutinee's free vars (existing `specialize_branch_context`/convoy) AND (1b) occurrence-abstract the scrutinee expression in the goal (existing `abstract_term`/`motive_for`), composed into one motive. Emit the nested `{:case}`; kernel re-checks. E-only.
- [ ] **Step 4: green** + load-bearing (each mechanism independently necessary — toggling either off fails).

### Task 3.2: Subsume + retire capability A

- [ ] **Step 1:** route capability-A (`elaborate_with_value`) surface through the unified front-end. **Step 2:** `mix test test/cure/elab/with_abstraction_test.exs` (A's suite) green under the unified path. **Step 3:** delete the special-case A code. **Step 4:** suite still green + `mix cure.oracle with` still `same`. **Step 5:** commit `refactor(elab): subsume+retire capability-A with under the generalizing front-end`.

### Task 3.3: Subsume + retire capability B — with the HEq decision

- [ ] **Step 1: Lean re-check.** Read `Meta/Match/Match.lean:128-143` (`mkEqHEq`): confirm Lean uses `HEq` exactly where a branch's pattern value has a refined-index type. **Step 2: decide the boundary (spec §4 completeness check).** Determine from the Phase-6 `SF` port whether any *named* proof-equation (`with … proof`) is ever needed over an **indexed** `SF`-scrutinee. (a) If capability C's convoy already covers every indexed case the paper needs → scope B's subsumption to **non-indexed scrutinees, permanently**; document it; retire B for that scope. (b) If an indexed named-proof is needed → adding `HEq` to the kernel is a **new TCB item**: STOP and open its own HARD-STOP gate (antibody: `HEq` intro/elim terminates + equates no distinct NFs + collapses to `Eq` on equal types) before claiming subsumption. **Step 3:** retire B for the decided scope; suites green; commit (E-only for case (a); TCB-gated for case (b)).

### Task 3.4: Subsume + retire capability C

- [ ] Route `elaborate_with_rematch` through the unified path; `with_rematch_match_test` + `with_rematch_elab_test` green; delete special-case C code; `mix cure.oracle with` (wi01–wi07) all `same`; commit `refactor(elab): subsume+retire capability-C rematch under the generalizing front-end`.

**Gate:** `generalizing_match_test` green; A/B/C special-case code deleted (or B explicitly scoped non-indexed-permanent); `with_abstraction`/`with_rematch_*`/`dependent_match_surface`/`match` suites green; `mix cure.oracle with` all `same`; full suite 0-regress (once, alone).

---

## Phase 4 — Type-level lemma stock + `rewrite` composition (E/C)

**Goal:** `++`/`∧`/`∨`/`<:` lemmas that let `rewrite` discharge the carried stuck-index equalities; flip `frp01` to `same`.

### Task 4.1: Lemma stock + single-occurrence discharge

**Files:** Create `test/oracle/frp/lib_frp.cure` (or stdlib module) with `++` assoc/right-identity, `∧`/`∨` laws as total functions + refl-bodied bridge lemmas. Modify elaborator only if `rewrite`↔carried-eq composition needs it.

- [ ] **Step 1: Lean re-check.** Read `UnifyEq.lean:60-136`: confirm Lean's equation solving is single-shot discharge-or-fail and multi-step algebraic rewriting is always human-composed — set the expectation that multi-occurrence is NOT automatic.
- [ ] **Step 2:** write the lemma stock; unit-test each lemma type-checks (refl-bodied, total).
- [ ] **Step 3:** make `frp01`'s `parAssoc` discharge via the assoc lemma + `rewrite`. Re-run `mix cure.oracle frp`. If `frp01` needs only a single reducible occurrence → it flips to `accept`; update `verdicts.json` relation to `same`, reason cleared.

### Task 4.2: Multi-occurrence reach (only if frp01/∗∗/loop needs it)

- [ ] **Step 1:** if Task 4.1 shows `_∗∗_`/`loop` goals need MORE than one occurrence rewritten (interchange-law shape), STOP — this is the separately reach-pinned multi-occurrence gap, **new work, not an rw07 corollary** (spec §Phase-4 caveat). **Step 2:** scope it: either (a) a multi-occurrence rewrite driver in the elaborator (E; red-green against a multi-occurrence probe), or (b) if it needs a kernel conversion change, the TCB gate. **Step 3:** record the decision in the task note; this gates Phase 6. **Step 4:** commit lemma stock + discharge `feat(frp): type-level lemma stock; frp01 ++-assoc discharge`.

**Gate:** `frp01` `same` (accept/accept) OR the multi-occurrence gap explicitly scoped as gating Phase 6; oracle_replay green; full suite 0-regress.

---

## Phase 5 — Signature-aware `Quote.reify` (TCB; gated) — may be pulled forward

**Goal:** Recover the params/indices split from the signature (Agda/Lean-style), closing the residual Eq-endpoint incompleteness. **Pull forward if Phase 2/3 hits the indexed-Eq-endpoint wall** (spec ordering contingency).

### Task 5.1: Signature-aware reify

**Files:** Modify `lib/cure/core/quote.ex` (+ minimal callers). Test: migrate `test/antigen/reach_reify_split.sexp` / `reify_split_gap_reach_test`. New antibody in `lib/antigen/generators/indexed.ex` + corpus.

- [ ] **Step 1: Lean/Agda re-check.** Confirm both recover the split from the signature (Lean `inductive_val.get_nparams/nindices`; Agda `getNumberOfParameters`) — reify should consult the family signature, not reconstruct blindly. Note in task.
- [ ] **Step 2: red.** Drive the value path: `Eq(Type, SNat x, SNat x)` reflexive motive → `:bad_motive` today. Assert it SHOULD accept (the reach test flips to green-forcing).
- [ ] **Step 3: implement** signature-aware split in `reify` (thread the signature; split `{:vdata,name,args}` into params/indices via `Inductive.param_count`/family kind). **Step 4:** TCB gate — new antibody ("signature-aware reify: split faithful, terminates, equates no distinct NFs"); full Antigen; full suite; **independent adversarial-verification subagent**. **Step 5:** commit kernel diff + antibody + migrated reach test as one reviewed unit; present the diff (no auto-merge).

**Gate:** reach test migrated red→green-forcing; TCB gate fully green incl. independent adversarial verification; full suite 0-regress.

---

## Phase 6 — FRP capstone (E + probes)

**Goal:** Port the real `SF` + `≫`/`∗∗`/`loop`/`switch` + `Dec` + `Init` indices; oracle confirms well-formed nets accept, instantaneous cycles + uninitialised escapes reject.

### Task 6.1: Re-derive `Init`/`switch` index algebra (scope-expansion gate)

- [ ] **Step 1:** from the paper (§4.1 `Dec`, §5.1 `Init`, §3.3.2/§4.2.1 `switch`/`rswitch`/`dswitch`), re-derive — the same way spec §2 did for `≫`/`∗∗`/`loop` — `Init`'s index algebra and `switch`'s computed-index/constructor shape, into `docs/superpowers/notes/2026-07-02-frp-index-algebra.md`. **Step 2:** confirm Phases 1–5's mechanisms generalize to the 4-index family with NO new gap; if a new gap appears (e.g. `Init` arity-change needs machinery beyond carried-eq), scope it explicitly as gating work here. Commit the note.

### Task 6.2: FRP acceptance/rejection probes

- [ ] **Step 1:** paired `.cure`/`.idr` for (a) a well-formed net using `≫`/`∗∗`/`loop` with correct decoupledness → accept/accept; (b) an instantaneous (undecoupled) `loop` → reject/reject; (c) an uninitialised-signal escape through a `switch` → reject/reject. Faithful transliterations. **Step 2:** `mix cure.oracle frp`; every entry `same` (or sound written `cure_stricter`). **Step 3:** oracle_replay green; commit `test(oracle): FRP capstone — well-formed nets accept, cycles + uninitialised escapes reject`.

**Gate:** `frp` cluster all `same`; the paper's safety property demonstrated in Cure; full suite green (once, alone) — this is the Stage 5 gate.

---

## Phase→Stage-5 handoff

At Phase 6 completion: full suite ONCE; completion report (per-phase commits, each TCB gate's antibody + independent-verification outcome, the A/B/C-retirement proof, the `frp` cluster table); push notification `autopilot done — review & merge autopilot/lean-shape-matching`; **do NOT auto-merge** — operator reviews all TCB diffs (Phase 1 if any, Phase 2 if escalated, Phase 3.3 if HEq, Phase 5) and merges.
