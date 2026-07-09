# Autopilot completion report — kernel-parity-batch

**Branch:** `autopilot/kernel-parity-batch` · **Status:** ALL SEVEN INITIATIVES LANDED · **Final gate at HEAD:** full suite 3291 passed / 0 failed (6 pre-existing skips), Antigen 503/503, oracle replay 65/65 zero divergence.

**Do not auto-merge — operator merges.** Review this branch and merge into `main` when satisfied.

Every initiative ran the full chain: scout → spec → recursive-skeptical-review (Sonnet, 2 consecutive clean passes) → plan → plan review → Opus execution, each stage committed before the next. All commits ghost-authored (`Made In Heaven`), no trailers.

---

## #10 — Global-def collision fix (A)

Cross-module same-named functions no longer silently overwrite: globals gained the same collision protection families/ctors already had. Landed and gated earlier in the batch.

## #11 — Identity-type-as-inductive kernel surgery (B)

Primitive `{:eq}`/`{:refl}`/`{:rewrite}` retired to a genuine inductive `Eq` with refl-matching and rewrite-as-sugar (Agda/Lean/Idris-aligned, K/UIP adopted). Validator-ratcheted (`no_eq_node`/`no_rewrite_node: :reject`).

## #12 — Parity queue C

Dot syntax, match constructor guards, Nat→Int erasure — the operator-queued parity items, landed with oracle verification.

## #13 — Sigma retirement (D1 enabler + D2)

- **D1/D1b:** napp motive sort via reify+infer kernel clause + type-position implicit insertion (adjudicated mid-run scope extension, spec §7).
- **D2:** primitive Sigma family (`{:sigma}/{:pair}/{:fst}/{:snd}`) fully retired to stdlib `Std.Sigma` (`@builtin(:sigma)` inductive + `mk_pair` + projection-`:case`). Bare-2-tuple BEAM ABI preserved. `no_sigma_node: :reject`. Adjudicated core_bridge carve-out (spec §8), behavior-pinned by classic tests.
- Spec/plan: `docs/superpowers/specs/2026-07-09-sigma-retirement-design.md` (b66cb2f → 466fd36, §8 8a6505d), plan 4479318 → 773eb60. Landed 5707a00…77be1af.

## #14 — Kernel infer/check coherence

`check`'s ctor clause restructured to an ordered `cond` (foreign-ctor → fields-only → params-on-spine → `check_via_infer` fallback), Lean-aligned (check = infer + def-eq). Fixed reflexive params-on-spine accepted by infer but rejected by check.
Spec a723931/5b7b46e, plan 3706d55/1983558. **Filed, not fixed:** ledger #28 ctor-spelling value dichotomy (spine vs fields-only diverge below the typing judgement — Conv length-strict, case ι shift, Erase spine params) — an operator design fork (Lean params-always vs Agda fields-only), see memory `ctor-spelling-value-dichotomy`.

## #16 — Antigen source-level vertical (F)

Elaboration-entry challenge family (carried-eq dispatch coverage) added to the Antigen soundness engine.

## #15 — prim → delta-globals (K2) + K4 closure (E) — the class-closing item

**The last kernel primitive is retired: Core's term grammar is now application spines only** (Pi/lam/app, data/ctor/case, Type/var/global + machine literals). Lean/Idris-aligned: arithmetic is ordinary globals with literal acceleration in the signature-carrying evaluator (Lean `reduce_nat` precedent, Idris2 Builtin-op def-records).

- **Spec** 045cedd → hardened 8de233b → **Amendment A1** 72994f4; **plan** 222e9aa → hardened d7fe402 (13 passes, 28 findings) → A1 deltas 41ac1a2.
- **Execution** b520176 (Phase 1: 23 builtin-op def-kind globals, registry marker, `unfold_certified_head` compute hook via the audited `Eval.fold` table, R4 nil-body kernel guards) → 65fbc35 (A1 extension) → 922f93d/9523f7a (Phase 2 consumers-first: GuardLint + emit spine recognition, then elaborator 4-way `==`/`!=` dispatch, core_bridge shape-dispatched spines + ordered from_core reverses, Reduce via sig-carrying kernel normalization) → 767140a (Phase 3: full `{:prim}`/`{:nprim}` strip incl. `infer_prim`, `no_prim_node: :reject` wave0+release, §J docs-drift fix, Antigen retargets + new `builtin_op_coherence_test` antibody, K4 absurd closed-as-landed bookkeeping) → bed397f (banked corpus records) → ac473d6 (comment tidy).
- **Mid-run adjudication (Amendment A1):** the executor's corpus survey found live Nat-`==` ctor guards (`ctor_guard_test.exs`) that the locked monomorphic op set would newly reject — a designated STOP. Verified in source; adjudicated on the parity criterion (Idris2/Lean accept ADT `==`): added polymorphic `struct_eq`/`struct_ne : Pi(a: Type). a -> a -> Bool` builtin-op globals reproducing today's semantics verbatim (kernel-neutral on ADTs — the compute hook reuses `Eval.fold`, which only folds int/float; emit drops the type arg and lowers to BEAM `==`). Op set = 25. `ctor_guard_test` 4/4 byte-identical (no pin flip). Zero programs newly rejected.
- **One substantive verdict flip, documented in-test:** `unify_meta_completeness_test:60-65` — a meta buried under a prim was walker-opaque (had to refuse); as a spine it decomposes structurally and the meta is soundly SOLVED. Strictly stronger.
- **New capabilities:** first-class/partial application of ops (curried wrappers), op-argument metavariable solving, minimal Core grammar, Lean-bridge export path unblocked (encoder retarget is future work).
- **Verified structurally by the orchestrator:** zero `{:prim`/`{:nprim` constructors under `lib/cure/core/`, `lib/cure/elab/`, `lib/antigen/`, `lib/cure/types/core_bridge.ex` (excepted validator predicate + one comment); `lib/cure/types/` diff = exactly `core_bridge.ex` + `reduce.ex`; `lib/cure/compiler/` untouched; ghost authorship on all 9 commits; full suite re-run once at final HEAD by the orchestrator: 3291/0.

**Honest residuals (flagged, not fixed):** core_bridge float free-index defaults to `int_*` (stuck-not-wrong, no live case); GuardLint float ops + `struct_eq` always uninterpreted (sound direction); `seed_ops` Bool-codomain nil on Bool-excluding envs (unreachable, mirrors existing contract); `connective_inline` bare-atom keying (pre-existing, spec §5 follow-up); Lean `module_encoder` still rejects the legacy tuple (export coverage is future work).

---

## Filed for operator decision (not tasks, no code changed)

1. **Ledger #28 — ctor-spelling value dichotomy** (from #14): pick ONE canonical value-level ctor spelling (Lean params-always vs Agda fields-only); the divergence sits below the typing judgement (Conv/ι/Erase). Memory: `ctor-spelling-value-dichotomy`.
2. **`connective_inline` bare-atom keying** in emit — pre-existing smell for user-plausible names (`and`/`or`/`not`/`eq`/`ne`).
3. **Pre-existing `Equivalent(int,x,y)` nf-idempotence infection** in the coverage fuzzer (predates this batch; queued in `builtin-inductive-foundation` memory).

## Where things live

- Specs/plans: `docs/superpowers/specs/2026-07-09-*.md`, `docs/superpowers/plans/2026-07-09-*.md` (this batch: sigma-retirement, infer-check-coherence, prim-delta-globals).
- Memory updated: `kernel-primitive-endgame` → **CLASS CLOSED** (all retirements landed, never-candidates locked, don't re-survey).
- The previous run's report (antigen-pre-port-banking) that this file replaces remains in git history.
