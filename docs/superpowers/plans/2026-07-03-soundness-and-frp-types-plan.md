# Soundness-for-Current-Surface + FRP-Critical Type Support — Consolidated Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans (this
> run executes INLINE per operator directive) to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** (Track A) close every known gap between what the current Cure surface
*claims* and what is actually *checked* — headlined by the missing `{0,ω}`
relevance check ("checked erasure" is currently marking + dropping with no
check) — then (Track B) complete full type support for the FRP-critical
dependent types (the Sculthorpe–Nilsson `SF` family with computed indices),
which is the remaining Phases 3–6 of the lean-shape-matching plan plus an
end-to-end BEAM acceptance that Track A's checked erasure licenses.

**Architecture:** Track A is elaborator-side (E) except one kernel-hardening
task (A5, TCB-gated); it adds a post-kernel-check relevance pass
(`lib/cure/elab/relevance.ex`, the 0/ω slice of Idris2 `Core/LinearCheck.idr`)
between `Kernel.check` and `Erase.erase`, plus a generative Antigen vertical
pinning it. Track B rides the existing lean-shape-matching plan (its Phases 3–6
remain the detailed execution doc; this plan is the governing roadmap and adds
the BEAM end-to-end acceptance the founding spec's §8 promises).

**Tech stack:** Elixir (Cure compiler), ExUnit, Antigen, differential oracle
(`mix cure.oracle` + `idris2 --check`), vendored references
(`~/Develop/esp32-beam/reference/idris2/src/Core/LinearCheck.idr`,
`~/Develop/lean4`, `~/Develop/Idris2`).

## Global constraints (verbatim house rules — every task inherits these)

- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO `Co-Authored-By`, no Claude signature.
- **Explicit-pathspec staging only:** `git add -- <path>`; NEVER `git add -A`/`git add .`.
- **One build at a time.** Scoped `mix test <file>` per step; the full suite once, alone, at each gate. Never concurrent suites.
- **TCB changes (`lib/cure/core/*`) are HARD-STOP-and-review:** red-green + new Antigen antibody (terminates, equates no distinct normal forms) + full Antigen + full suite + INDEPENDENT adversarial-verification subagent; operator reviews the diff at merge; no auto-merge.
- **Elaborator hard-stop principle:** before accepting any TCB-required stop, prove NO untrusted term works (bridge lemma / motive reshaping).
- **Reference-grounded:** every task opens by re-checking the named Lean/Idris/Agda source (operator directive); never from memory. Never hand-write oracle verdicts.
- **Tests immutable once green** (behavioral); strict red-green (named failing test first, run it red, implement, run it green, commit).
- **Worktree:** all work stays on `.claude/worktrees/lean-shape-matching`, branch `autopilot/lean-shape-matching` (operator worktree preference).

## Layer map recap

K = TCB `lib/cure/core/*` · E = elaborator `lib/cure/elab/*` · A = Antigen
`lib/antigen/*` · P = parser · C = eval/codegen/erase-emit.

---

# Track A — Soundness for the current surface

**The claim being repaired.** The founding spec (§3.1/§8,
`2026-06-30-cure-dependent-types-frp-design.md`) commits to **checked** `{0,ω}`
erasure: a `0`-marked binder is *verified* never used in a computationally
relevant position, so dropping it is "sound rather than a positional guess."
What exists today: **marking** (ctor telescopes + fn implicits carry
`:erased`/`:present`, `erasure_marking_test.exs`) and **dropping**
(`erase.ex` M9.1: erased ctor args + erased global-app args; `emit.ex` treats
erased binders as dead `_e<pos>` slots). What does NOT exist: the **check**
(`{:error, {:erased_used_relevantly, _}}` appears nowhere; founding-plan Task
M8.3's check steps were never executed; no `LinearCheck` port exists). Erased
*constructor fields* are structurally unnameable (`branch_scope` binds them
`"_erased"`), but **fn-level erased implicits are bound under their real names
and nothing stops a body from using one relevantly** — the kernel is
quantity-blind, so `fn f({n: Nat}, v: NV(n)) -> Nat = n` type-checks, and
erasure then drops `n` from call sites while the body still references it: a
miscompile class, not a rejection. That is the implicits-soundness hole this
track closes, plus the two kernel trust-marker exposures flagged (pre-existing)
by the Phase-4a adversarial verification, plus whatever the in-flight 8019e67
verification returns.

### Task A1: Characterize the erased-implicit relevant-use hole (red probes) — DONE (071b5e5)

Red probes committed; (a)/(b)/(c) elaborated `{:ok}` (the hole), controls (d)/(e)
accepted. Idris 0/ω slice grounded in the test moduledoc.

**Files:** Create `test/cure/elab/erasure_relevance_test.exs`. No lib changes.
**Interfaces:** Consumes `Cure.Elab.Program.elaborate/1` and (for the
end-to-end probe) the elaborate→erase→emit path used by
`test/cure/elab/erase_test.exs` / `emit` tests — copy the harness those tests
already use rather than inventing one.

- [ ] **Step 1: Idris grounding.** Read
  `~/Develop/esp32-beam/reference/idris2/src/Core/LinearCheck.idr` — extract the
  0/ω slice ONLY (per the manifest caveat: read Idris core as ω-except-erased;
  do NOT port `1`). Record in the test's moduledoc: which usages Idris counts as
  relevant for a `0` binder (returned, scrutinised, passed in a `ω` position,
  applied) and which are exempt (type positions, erased argument positions,
  `Eq`/proof positions).
- [ ] **Step 2: write the red probes.** One test per relevant-use class, each
  asserting `{:error, {:erased_used_relevantly, _}}`:
  (a) body RETURNS an erased implicit: `fn f({n: Nat}, v: NV(n)) -> Nat = n`;
  (b) body passes an erased implicit in a PRESENT argument position:
  `fn g(m: Nat) -> Nat = m` … `fn f({n: Nat}, v: NV(n)) -> Nat = g(n)`;
  (c) body SCRUTINISES an erased implicit: `match n` inside `f`;
  plus two green controls that must pass BEFORE and AFTER the fix:
  (d) erased implicit used only in a TYPE/index position (the normal case —
  `fn f({n: Nat}, v: NV(n)) -> NV(n) = v`) accepts;
  (e) erased implicit used only inside an `Eq` proof / `rewrite` proof
  position accepts.
- [ ] **Step 3: run them — record the CURRENT verdicts.** Expected: (a)–(c)
  FAIL the assertion (today they elaborate `{:ok, _}` — the hole), (d)–(e)
  controls pass. If any of (a)–(c) already errors for an unrelated reason,
  record the actual error and adjust the characterization note — do not
  hand-wave it into "already checked."
- [ ] **Step 4: end-to-end miscompile witness (documentation of severity).** In
  the same file, one `@tag :characterization` test that runs probe (a) through
  elaborate→erase→emit and records what actually happens (arity mismatch /
  unbound var / silently-kept binder). This test asserts only "elaboration
  accepts today" and is REPLACED by the A2 rejection (it is the one test in
  this plan explicitly born to be superseded — mark it with a comment saying
  A2 deletes it).
- [ ] **Step 5: commit** `test(elab): red — erased implicits usable relevantly ({0,ω} check missing, M8.3)`.

### Task A2: Implement the `{0,ω}` relevance check (the LinearCheck 0/ω slice) — DONE (67395a2)

**Operator-ratified design decision (locked).** The relevance criterion is spec
§2 ("no computationally-relevant use of an erased binder": returned / present-arg
/ scrutinised / applied — all rejected), NOT the §8 shorthand "scrutinised."
Rationale: returning or passing an erased binder is equally unsound; only "make
the param present" preserves Cure's zero-footprint guarantee (vs. Idris-style
auto-promotion, which would silently retain index data and hide runtime cost).
Consequence: the §6 conformance program's `forget_dec` takes `d` as an explicit
PRESENT parameter (it materialises `d` into a runtime Σ for `recover`/`step` to
inspect — `d` genuinely has runtime footprint). Fixture + `sigma_surface` +
`with_rematch` corrected; spec §8 wording aligned to §2. Oracle `erasure` cluster:
er01/er02 `cure_stricter` (Idris keeps runtime-used implicits at ω), er03 `same`.
Full suite 2359 passed, zero regressions.

**Files:** Create `lib/cure/elab/relevance.ex`; modify
`lib/cure/elab/declarations.ex` (call site: after `Kernel.check` succeeds,
before the def is registered/erased — same seam where quantities are recorded).
Test: `test/cure/elab/erasure_relevance_test.exs` (from A1).
**Interfaces:** Produces `Relevance.check(env, name, quantities, body_term) ::
:ok | {:error, {:erased_used_relevantly, %{def: name, binder: idx_or_name,
site: :returned | :present_arg | :scrutinee | :applied}}}`. Consumed by
`declarations.ex` only; NOT by the kernel (this is E-layer — the kernel stays
quantity-blind, exactly like Idris where LinearCheck sits outside the core
checker's conversion).

- [ ] **Step 1: re-check Idris source** (`LinearCheck.idr`) at the top of the
  task — confirm the traversal shape: usage-count walk over the checked term,
  where a `0` binder contributes usage only through relevant positions; type
  annotations, erased applications, and proof terms do not count.
- [ ] **Step 2: implement the walk** over Core terms ({:var}, {:lam}, {:app}
  spines with per-position quantities from `Env.get_def`/`Inductive.
  ctor_quantities`, {:case} scrutinee+branches, {:pair}/{:fst}/{:snd},
  {:eq}/{:refl}/{:rewrite} — proof positions exempt, {:pi}/{:sigma} domains
  exempt (type positions), motive exempt). Every A1 probe (a)–(c) must now
  reject with the exact error shape; controls (d)–(e) stay green.
- [ ] **Step 3: delete the A1 Step-4 characterization test** (its replacement
  is the rejection) — this deletion is pre-authorized by A1 Step 4's comment.
- [ ] **Step 4: regression sweep (scoped, one at a time):**
  `mix test test/cure/elab/` then `mix test test/cure/stdlib/ test/cure/e2e/`
  (or the nearest existing integration dirs) — the check must NOT reject any
  currently-green program; if it does, the walk is over-counting (fix the walk;
  the suite is the spec of "current surface").
- [ ] **Step 5: oracle cross-check.** Add paired `.cure`/`.idr` probes to a new
  `test/oracle/erasure/` cluster: Idris rejects `0`-binder relevant use with
  its own linearity error — the relation must be `same` (reject/reject).
  `mix cure.oracle erasure`; commit verdicts. Never hand-write them.
- [ ] **Step 6: full suite once, alone.** Then commit
  `feat(elab): checked {0,ω} erasure — relevance check (LinearCheck 0/ω slice, M8.3 completed)`.

### Task A3: Erasure-seam consistency audit (the other three seams)

**Files:** Extend `test/cure/elab/erasure_relevance_test.exs` (new describe
block) + `test/cure/elab/erase_test.exs` if a seam test naturally lives there.
**Interfaces:** Read-only over `erase.ex`, `emit.ex`, `elaborator.ex`
`branch_scope`; produces tests only.

- [ ] **Step 1:** pin the ctor-field structural protection as a TEST (today it
  is only an implementation accident): a branch body that names an erased ctor
  field gets an unbound-variable/unknown-name error, never a silent bind.
- [ ] **Step 2:** pin call-site/def-head consistency: for a def with erased
  params, elaborate→erase→emit produces matching arities between the emitted
  head and every emitted call site (use A1's harness; assert on the emitted
  forms, not on runtime execution).
- [ ] **Step 3:** pin proof irrelevance: `rewrite` proofs and `Eq` values are
  dropped by erasure (`rewrite e _ t ⇝ t` at eval; erased at emit) — a
  program computing through a rewrite runs identically with the proof term
  swapped for another valid proof (proof-irrelevance smoke test on BEAM).
- [ ] **Step 4:** commit `test(elab): pin erasure seams — ctor-field unnameability, arity consistency, proof irrelevance`.

### Task A4: Antigen `elab/erasure` vertical (generative pin)

**Files:** Create `lib/antigen/generators/elab_erasure.ex`,
extend `lib/antigen/assays/elab.ex` (new assay id `elab/erasure`),
`lib/antigen/runner.ex` (registry entry), `lib/antigen/challenge.ex` only if a
new payload key is needed (reuse `:elab_program` kind + string scaffold).
Test: `test/antigen/elab_erasure_test.exs`.
**Interfaces:** Follows the exact pattern of `elab_complete.ex` /
`Assays.Elab` from Phase 2½ (catalog of construction-guaranteed programs +
metamorphic transforms; assay `run/1 :: :ok | {:violation, term}`).

- [ ] **Step 1: catalog.** Base programs parameterised on WHERE an erased
  binder is used: type-only (must ACCEPT), Eq-proof-only (ACCEPT), returned
  (REJECT), present-arg (REJECT), scrutinised (REJECT). Labels carry the
  expected verdict — this vertical, unlike `elab/completeness`, is
  two-sided.
- [ ] **Step 2: metamorphic transform** `relevance_injection`: take an
  accepting base and inject a single relevant use of the erased binder — the
  verdict MUST flip to reject (the check is load-bearing, not vacuous).
  Reuse `prepend_unused_param` and `alpha_rename` from `elab_complete.ex` for
  invariance (verdict must NOT flip under those).
- [ ] **Step 3:** assay + registry + discrimination tests (red-green the
  vertical itself, as `elab_completeness_test.exs` does), corpus round-trip.
- [ ] **Step 4:** full Antigen suite once. Commit
  `feat(antigen): elab/erasure vertical — two-sided relevance-check pin`.

### Task A5: Kernel trust-marker hardening (TCB; HARD-STOP gate)

The two PRE-EXISTING exposures flagged out-of-scope by the Phase-4a adversarial
verification (a9962257), now brought in scope:
(1) `unfold_certified_head` (`normalise.ex:204`) evals a certified body in the
EMPTY env — a malformed signature with an *open* certified body could alias
context vars at low de Bruijn levels (currently rests on `check_def` rejecting
open bodies, an invariant enforced elsewhere and assumed here);
(2) `Env.certify/2` is an unchecked trust marker (`kernel.ex:386` is the only
legitimate producer) — a forged cert for a non-total global makes no-fuel
`conv?` diverge (never mis-answer, but divergence is a DoS-shaped kernel
defect).

**Files:** Modify `lib/cure/core/env.ex` and/or `lib/cure/core/normalise.ex`
(smallest sufficient diff). Test: `test/cure/core/certify_hardening_test.exs`.
Antibody: new corpus entries under the existing certificate/stuck-elim family.

- [ ] **Step 1: re-check prior art.** Lean: certificates don't exist as a
  mutable env marker — `type_checker.cpp` unfolds only declarations already
  checked into the environment; Idris: totality flags are set by the checker
  post-verification (`Core/Termination` call sites). Confirm the invariant to
  enforce: *certification is producible only from a kernel-validated
  certificate, and a certified body is closed.*
- [ ] **Step 2: red.** (a) `Env.certify` (or a raw-struct forgery of the same
  marker) on a def whose body is OPEN → `unfold_certified_head` path must
  refuse to unfold (error or stays-stuck), not eval the open body; (b) a forged
  cert on a non-total def → `conv?` must stay fuel-bounded/stuck rather than
  diverge (assert via the existing fuel counter, bounded iterations).
- [ ] **Step 3: implement** the smallest kernel diff: `Env.certify/2` gains a
  closed-body assertion (reuse the existing free-var scan; reject open) and the
  certify seam is restricted to the validated-certificate path (make the
  public constructor take the certificate, or check it). Do NOT redesign the
  certificate system.
- [ ] **Step 4: TCB gate (full):** antibody banked (forged/open-cert entries:
  positive flips pre-fix, controls stay `:ok` — prove red-green by stashing);
  full Antigen; full suite once; **independent adversarial-verification
  subagent** (fresh context, opens with the Lean/Idris re-check, attacks the
  new seam). HARD STOP: operator reviews this diff at merge.
- [ ] **Step 5: commit** kernel diff + red-green test + antibody as one
  reviewed unit `fix(kernel): certify requires closed body + validated certificate (4a-flagged exposures)`.

### Task A6: Disposition of the 8019e67 verification findings (contingent)

**Files:** determined by findings. The adversarial verifier on the
scrutinee-refinement fix is in flight (highest-value attack:
`replace_term`'s syntactic replacement has no shift adjustment under binders;
plus capture/shadow/duplicate-name guards and erased-quantity interaction).

- [x] **Step 1 — DONE. Verdict: SOUND (SOUND-WITH-NOTES).** No CONFIRMED unsound
  accept; none was constructible or is statically reachable. The `replace_term`/
  `replace_branch_vars` binder-shift gap is confirmed **latent, not live**:
  kernel recomputes each branch goal from motive-at-ctor (`check_case_branches`,
  kernel.ex:702-746) and re-checks the whole term (declarations.ex:43), and every
  Pi-in-goal shape is rejected at `check_motive_wf` (`:bad_motive`) on the parent
  commit too — so the non-binder-aware helpers are unreachable via plain match.
  **No red-green fix needed.** (Standing note carried to B1: when the Pi-in-goal
  motive gap is fixed in Phase 3, `replace_term`/`replace_branch_vars` must gain
  de Bruijn shift in the SAME change — the backstop keeps it sound but it will
  emit confusing spurious rejects otherwise. Recorded as a B1 precondition.)
- [x] **Step 2 — DONE. Five completeness corners reach-pinned** (all pre-existing,
  no regressions; each an Antigen must-eventually-accept, Idris accepts each):
  1. **Nested match on a telescope var** (chained two-level refinement) →
     `:index_mismatch`/`:branch_type`. Squarely a Phase 3 (B1) target.
  2. **Scrutinee occurrence nested inside another application in the goal**
     (`Eq(Wrap(n), wk(v), wk(v))`) rejects even for a VAR scrutinee; only flat
     occurrences (`Eq(NV(n), v, v)`) land. B1 generalizing-motive target.
  3. **Goal index is a ctor application over the scrutinee's index**
     (`-> NV(S(m))` matching `u : SNat(m)`) → `:branch_type`; basic view shape.
     B1 target.
  4. **Any Pi/arrow-containing goal under plain match** → `:bad_motive`. This is
     also what currently shields the latent binder-shift gap (Step 1) — the B1
     precondition binds them together.
  5. **`binds_any?` knows only `{:match_arm}`** — `{:with_rematch_arm}` / `proof
     <name>` binders in meta would be missed; currently unreachable (nested
     `with` rejected, P9), a tripwire for when nested `with`/`let`/lambda enter
     the elaborator surface fragment. Guard-hardening pin, revisit at B2/B3.
- [x] **Step 3 — DONE.** Verdict sealed in the lean-shape plan's Phase 2½ section
  (final checkbox now `[x]`, SOUND) and here; docs committed.

**Track A gate:** A1–A4 green (relevance check live, two-sided vertical
healthy, seams pinned); A5's TCB gate fully green incl. independent
verification; A6 dispositioned; full suite once, alone, zero regressions.
After this gate the sentence "erasure is licensed by the `{0,ω}` check" in the
founding spec §8 is TRUE for the first time.

---

# Track B — Full type support for the FRP-critical dependent types

**What "FRP-critical" means (from the founding spec §6–§8 + paper):** the
4-index family `SF (as: SVDesc) (bs: SVDesc) (d: Dec)` (+ `Init` in the wider
slice), descriptor types `SVDesc`/`Sig`/`Dec` with **computed indices**
(`++`/append, `∧`/`∨` on `Dec`), the combinator family `≫`/`∗∗`/`loop`/
`switch`, dependent matching over all of it (the lean-shape machinery), `Σ`
results (`step` returns a dependent pair), and zero runtime footprint for
descriptors — now *checked*, via Track A.

Tasks B1–B4 are the remaining phases of
`docs/superpowers/plans/2026-07-02-lean-shape-matching-plan.md` — that document
remains the detailed step-by-step execution doc (fully specified there; not
duplicated here per DRY). This plan governs sequencing and adds B5. Execution
notes discovered since it was written are repeated here so B1 does not start on
a stale premise.

### Task B1: Generalizing match front-end + retire A/B/C (= lean-shape Phase 3)

- [ ] Execute lean-shape Tasks 3.1–3.4 exactly as written there, with the
  Phase-2½ amendment: **capability-A GOAL refinement is already subsumed by
  plain `match`** (commit 8019e67 — computed-scrutinee kabstract + body
  scrutinee substitution). Task 3.1's red test must therefore be re-verified
  red via its SIBLING-refinement half before implementing; Task 3.2's
  `need_eq == false` routing may be a near-no-op — if `wi01` already passes
  through plain match, the task reduces to deleting the special case (still
  red-green: the deletion's test is "with_abstraction suite green + oracle
  `with` cluster all `same` post-deletion").
- [ ] Task 3.3's HEq decision stays the analytical derivation as written
  (case (b) opens a TCB HARD-STOP gate).
- [ ] **Gate** (unchanged from lean-shape): A/B/C special-case code deleted or
  B explicitly scoped; `with_*`/`dependent_match_surface`/`match` suites green;
  `mix cure.oracle with` all `same`; full suite once.

### Task B2: Demand-driven lemma stock + multi-occurrence decision (= Phase 4, post-4a shape)

- [ ] Execute lean-shape Tasks 4.1–4.2 as amended by the 4a finding: `frp01`
  already flipped `same` via the conversion fix (09a80f3), so the lemma stock
  is DEMAND-DRIVEN from B4's capstone (build only the `++`/`Dec`-lattice
  lemmas the `∗∗`/`loop`/`switch` goals actually require).
- [ ] The multi-occurrence question (Task 4.2) is decided when B4's `∗∗`
  interchange-shaped goals are attempted; if it needs kernel conversion work,
  that is a TCB HARD-STOP gate, else an E-layer rewrite driver. Record the
  decision; it gates B4.

### Task B3: Signature-aware `Quote.reify` (= Phase 5; TCB; HARD-STOP gate)

- [ ] Execute lean-shape Task 5.1 as written: recover the params/indices split
  from the family signature (Lean `inductive_val.get_nparams`; Agda
  `getNumberOfParameters`), migrating the reach-pinned
  `reach_reify_split.sexp` red→green-forcing. Full TCB gate + independent
  adversarial verification; operator reviews the kernel diff.
- [ ] **Pull-forward trigger** (unchanged): if B1 hits the indexed-Eq-endpoint
  wall (`infer_type_value_sort` Eq-endpoint false-rejection), B3 runs before
  B1 completes.

### Task B4: FRP capstone probes (= Phase 6)

- [ ] Execute lean-shape Tasks 6.1–6.2 as written: re-derive `Init`/`switch`
  index algebra into `docs/superpowers/notes/2026-07-02-frp-index-algebra.md`
  (scope-expansion gate — a new mechanism gap discovered here is scoped
  explicitly, not improvised); then paired `.cure`/`.idr` probes — well-formed
  `≫`/`∗∗`/`loop` net accept/accept; instantaneous `loop` reject/reject;
  uninitialised-signal escape through `switch` reject/reject. `mix cure.oracle
  frp` all `same` (or sound written `cure_stricter`).

### Task B5: End-to-end BEAM acceptance — the FRP types RUN, checked-erased (new)

The founding spec §8 promises: descriptors have zero runtime footprint, `SF`'s
value-relevant structure survives as tagged tuples, `step` pattern-matches it
at runtime, and the drop is *licensed by the `{0,ω}` check*. After Track A +
B1–B4 every ingredient exists; this task proves the composition end-to-end,
which no current test does.

**Files:** Create `test/cure/e2e/frp_beam_test.exs`; a small self-contained
`.cure` program embedded in the test (Nat/Bool events, 2-signal descriptors —
NOT the full paper library).
**Interfaces:** Consumes `Program.elaborate/1`, `Erase.erase/2`, the emit
path from `emit.ex`'s existing tests, and BEAM execution the way
`test/cure/elab/emit`-adjacent tests already load modules.

- [ ] **Step 1: red.** The probe program: `SVDesc`/`Sig`/`Dec` descriptors;
  `SF` with `prim` and `seq` (computed `∧` index); a `step`-like eliminator
  matching `SF` and returning a `Σ` pair; a tiny net `seq(prim…, prim…)`
  driven one step from `start/0`, printing an observable value. Assert:
  elaborates, relevance-check passes (erased indices used only in types),
  erases, emits, loads, and RUNS printing the expected value. Red today at
  whichever stage first fails — record the stage.
- [ ] **Step 2:** fix only integration seams this exposes (each its own
  red-green micro-cycle within the task; any would-be kernel change is a
  HARD-STOP per the global constraints — expected NONE, the kernel is done by
  B3).
- [ ] **Step 3: erasure-footprint assertion.** Inspect the emitted forms: no
  `SVDesc`/`Dec` argument survives in the emitted `SF` constructor calls
  (descriptor zero-footprint, asserted structurally, not assumed).
- [ ] **Step 4:** full suite once, alone. Commit
  `feat(e2e): FRP slice runs on BEAM under checked {0,ω} erasure`.

**Track B gate:** B1–B4 gates each green (B3's and any B2(b)/B1-HEq TCB gates
independently verified, operator-reviewed); B5 green — the paper's safety
property demonstrated AND executed. This is the Stage-5 handoff condition of
the autopilot run.

---

## Sequencing (dependency-ordered)

1. **A6** disposition happens first chronologically (verifier already
   running); any CONFIRMED unsoundness pre-empts everything.
2. **A1 → A2 → A3 → A4** — the relevance chain (E-only, closes the live
   miscompile class; cheap; also a prerequisite for B5's "checked" claim).
3. **A5** — its own reviewed TCB run (independent of the A1–A4 chain; may
   interleave after A2 if the build is free).
4. **B1 → B2/B3 (B3 pulls forward on the Eq-endpoint trigger) → B4 → B5.**
   B5 is last: it needs A2 (checked erasure), B1 (matching), B4 (the types).
5. Every phase commits before the next begins (autopilot resilience rule).

## Explicitly out of scope (unchanged decisions, restated so this plan is total)

- Linear `1` multiplicity / usage counting (locked out by founding spec §3.1;
  the lattice stays 2-point but extensible).
- Named/auto-bound implicits as surface features (parity roadmap §4) — Track A
  fixes the *soundness* of the implicits we have, not their ergonomics.
- Universe polymorphism, SMT-for-indices, `%default total` surface modes.
- Multi-`with`, forced/arithmetic restated patterns (#5), guards in rematch
  arms — reach items tracked in the parity ledger, not FRP-critical.
