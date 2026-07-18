# Verified LIA Reflection Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking. This is a **cure-porting** task (type-theory algorithm into Cure with a differential Idris oracle) — also load the `cure-porting` and `cure-language` skills before starting.

**Goal:** Build the trusted core of a verified linear-integer-arithmetic (LIA) decision procedure — a total Cure checker `check_lia` plus its kernel-checked soundness theorem `check_lia_sound` — so open LIA refinement obligations can later be discharged by computational reflection with no solver in the TCB.

**Architecture:** SMTCoq / Rocq-Micromega design "A": an (out-of-scope-for-this-plan) untrusted producer emits a Farkas certificate; a total Cure function `check_lia` validates it by forming the nonnegative linear combination and checking for a manifest contradiction; the kernel re-runs `check_lia` by computation, and `check_lia_sound` proves that a passing certificate implies the goal holds. Because primitive `Int` admits no structural induction, the proof-relevant arithmetic runs over a **new inductive integer type `Zed`** (mirroring Micromega's inductive `Z` and Idris's `Integer`) with a small proven ordered-ring lemma kit; the primitive-`Int` boundary is left to the follow-on #4 bridge.

**Tech Stack:** Cure (dependently-typed, `lib/std/*.cure`), the differential Idris oracle (`test/oracle/otp/*.{cure,idr}`, `mix cure.oracle` + replay), Idris2 at `~/Develop/Idris2/build/exec/idris2`.

**Scope:** This plan implements spec **P1 only** (the trusted metatheory core — checker + soundness, over explicit witnesses). Spec P2 (untrusted Elixir producer) and P3 (E-layer reflection seam) are **follow-on plans**, not built here. Reference spec: `docs/superpowers/specs/2026-07-18-verified-lia-reflection-design.md`.

## Global Constraints

- **TCB discipline — no kernel rules, no axioms.** Everything is ordinary Cure proof terms the existing kernel checks. No `@extern`/primitive is added to stand in for an arithmetic law — that would grow the TCB. If a proof *seems* to require a kernel change or an axiom, **STOP and write `AUTOPILOT-STATE.md`** (elaborator-hard-stop principle): prove no untrusted term works before escalating.
- **Descriptive naming** (standing directive): spell names out — `Zed`, `NegativeSuccessor`, `is_less_or_equal`, `check_lia_sound`; never `Z`-for-integer (that collides with `Nat`'s `Z`), `leq`, `refl`.
- **Layer:** all new code in `lib/std/*.cure` (checker + kit) and `test/oracle/otp/*.{cure,idr}` (probe). Do NOT touch `lib/cure/compiler/*` (non-dependent decoy) or the kernel (`lib/cure/core/*`, `lib/cure/elab/*`) — this plan is pure stdlib metatheory. `lib/cure/smt/process.ex` stays untouched.
- **Oracle discipline:** every `.cure` proof file has a mirrored `.idr`; a brand-new pair defaults to `relation: same`; `mix cure.oracle` regenerates verdicts and `replay` must be green before the task commits. Keep each probe self-contained and under the 30s per-probe Cure budget. **Cluster vs. probe name:** `Cure.Oracle.clusters/0` are immediate subdirectories of `test/oracle/`, not individual probe basenames (`lib/cure/oracle.ex`). Every probe in this plan lives in the existing `test/oracle/otp/` directory, so `mix cure.oracle`'s argument throughout this plan is always the cluster `otp` (which reruns every probe already in that directory alongside the new one) — never a probe's own basename like `integer_ops`. The offline replay command is `mix test test/oracle_replay_test.exs`.
- **Ghost commits:** author as the user only — `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no `Co-Authored-By`, explicit-pathspec staging only.
- **One build at a time:** never run concurrent full builds/suites.
- **Red-green for proofs:** for a proof task, "red" = the module fails to compile (an unfilled hole or a type error at the theorem's signature) and, where applicable, the paired oracle probe is absent or failing; "green" = the module compiles (the kernel accepted the proof term) and the oracle replays `rel=same`. The theorem's *type* is the test. Once a probe's expected outcome is fixed it is **immutable** — reach green by fixing the proof, never by weakening the statement, unless the statement is shown wrong (state why first).

---

### Task 1: Inductive integer type `Zed` and its computable operations

**Files:**
- Create: `lib/std/integer.cure` (module `Std.Integer`)
- Test: `test/oracle/otp/integer_ops.cure` + `test/oracle/otp/integer_ops.idr`

**Interfaces:**
- Produces:
  - `type Zed = FromNat(Nat) | NegativeSuccessor(Nat)` — `FromNat(n)` is `+n`; `NegativeSuccessor(n)` is `-(n+1)`. Unique representation (zero is only `FromNat(Z())`), so structural equality is decidable.
  - `fn negate(a: Zed) -> Zed`
  - `fn add(a: Zed, b: Zed) -> Zed`
  - `fn multiply(a: Zed, b: Zed) -> Zed`
  - `fn is_less_or_equal(a: Zed, b: Zed) -> Bool`
  - `fn is_less(a: Zed, b: Zed) -> Bool`
  - `zed_zero = FromNat(Z())`, `zed_one = FromNat(S(Z()))`, `zed_negative_one = NegativeSuccessor(Z())`

- [ ] **Step 1: Write the failing oracle probe** (`integer_ops.cure` + mirror `.idr`). Assert closed computations via `Equivalent`. **The probe imports the real `Std.Integer` module (`use Std.Integer`) rather than locally redeclaring `Zed`/`add`/`is_less_or_equal`** — unlike a self-contained probe re-deriving its own throwaway fragment (e.g. `mailbox_pattern.cure`'s local `plus`), Task 1's entire purpose is to produce a *reusable* `Std.Integer` that Task 2 depends on by name, so the probe must exercise that actual module or the red/green gate proves nothing about the real deliverable. (Precedent for probes importing real stdlib modules: `test/oracle/otp/bag.cure` etc. `use Std.Equivalent`, `test/oracle/otp/reply_conservation.cure` `use Std.Nat`.)

```cure
mod IntegerOps
  use Std.Equivalent
  use Std.Nat
  use Std.Integer   # Zed / add / is_less_or_equal come from lib/std/integer.cure (Task 1) —
                     # unresolved until Step 3, which is exactly the red signal below.

  fn add_pos_pos() -> Equivalent(Zed, add(FromNat(S(S(Z()))), FromNat(S(Z()))), FromNat(S(S(S(Z()))))) =
    reflexive(FromNat(S(S(S(Z())))))                       # 2 + 1 = 3
  fn add_pos_neg_cancels() -> Equivalent(Zed, add(FromNat(S(Z())), NegativeSuccessor(Z())), FromNat(Z())) =
    reflexive(FromNat(Z()))                                # 1 + (-1) = 0
  fn neg_one_leq_zero_true() -> Equivalent(Bool, is_less_or_equal(NegativeSuccessor(Z()), FromNat(Z())), True()) =
    reflexive(True())                                      # -1 ≤ 0
  fn zero_leq_neg_one_false() -> Equivalent(Bool, is_less_or_equal(FromNat(Z()), NegativeSuccessor(Z())), False()) =
    reflexive(False())                                     # ¬(0 ≤ -1) — the contradiction atom
```

  Mirror each in `integer_ops.idr` with Idris `data Zed = FromNat Nat | NegativeSuccessor Nat` and `Refl`-based equalities (`%default total`) — the Idris side has no shared stdlib to import from, so it stays self-contained; only the Cure side must import the real module.

- [ ] **Step 2: Run it red.** `cd <worktree> && mix cure.oracle otp` → expect failure on the `integer_ops` probe (`use Std.Integer` unresolved — `lib/std/integer.cure` doesn't exist yet). Record the red output.

- [ ] **Step 3: Implement `Std.Integer`.** Create `lib/std/integer.cure` opening with `@group(:core)` above `mod Std.Integer` (the `:core` preload-group tag read by `lib/cure/stdlib/preload.ex`'s `filter_by_groups`/`stdlib_modules(:core)` — matches the sibling proof modules `proof_math.cure`/`proof_int_math.cure`, both of which open with `@group(:core)`; do this now rather than deferring it to Task 5, since Task 5 only verifies it's present). Define `Zed` and the operations. Define `add`/`multiply`/`is_less_or_equal` by casing on both `Zed` constructors and delegating to `Std.Nat`'s `plus` and a total truncated subtraction/`compare` on `Nat` (add `fn monus(m: Nat, n: Nat) -> Nat` and `fn compare_nat(m: Nat, n: Nat) -> Ordering` in `Std.Nat` if absent — check first, reuse if present). **Note: `Std.Nat` does not currently define `multiply`** — `Nat` multiplication today lives only in `Std.Proof.Math` (`lib/std/proof_math.cure`). Rather than importing a proof module into this computational one, add a small structural `fn multiply(m: Nat, n: Nat) -> Nat` directly to `Std.Nat` here (mirroring `proof_math.cure`'s definition: `match m; Z() -> Z(); S(k) -> plus(n, multiply(k, n))`); do not rename or touch `Std.Proof.Math`'s existing `multiply`. `is_less(a,b) = is_less_or_equal(add(a, zed_one), b)`. Keep every branch total and structural.

- [ ] **Step 4: Run it green.** `mix cure.oracle otp` then `mix test test/oracle_replay_test.exs` → the `integer_ops` probe is `rel=same`, all four assertions pass. If any closed computation doesn't reduce, fix the definition (not the probe).

- [ ] **Step 5: Commit.**

```bash
git add lib/std/integer.cure test/oracle/otp/integer_ops.cure test/oracle/otp/integer_ops.idr test/oracle/otp/integer_ops/
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(std): inductive integer type Zed with computable ring/order ops"
```

---

### Task 2: Ordered-ring lemma kit over `Zed` (the long-pole)

**Files:**
- Modify: `lib/std/integer.cure` (add proof section)
- Test: `test/oracle/otp/integer_laws.cure` + `.idr`

**Interfaces:**
- Produces (each a proven `fn`, signatures exact — later tasks depend on these names):
  - `fn add_preserves_less_or_equal(a: Zed, b: Zed, c: Zed, d: Zed, ab: IsTrue(is_less_or_equal(a,b)), cd: IsTrue(is_less_or_equal(c,d))) -> IsTrue(is_less_or_equal(add(a,c), add(b,d)))`
  - `fn scale_nonneg_preserves_less_or_equal(k: Nat, a: Zed, b: Zed, ab: IsTrue(is_less_or_equal(a,b))) -> IsTrue(is_less_or_equal(multiply(FromNat(k), a), multiply(FromNat(k), b)))`
  - `fn less_or_equal_is_transitive(a: Zed, b: Zed, c: Zed, ab: IsTrue(is_less_or_equal(a,b)), bc: IsTrue(is_less_or_equal(b,c))) -> IsTrue(is_less_or_equal(a,c))`
  - `fn zero_is_not_less_or_equal_to_negative_one(proof: IsTrue(is_less_or_equal(FromNat(Z()), NegativeSuccessor(Z())))) -> Empty` — the contradiction extractor
- Consumes: `Std.Integer` ops (Task 1), `Std.Proof.IntMath` (`IsTrue`/`Confirmed`/`true_is_not_false`), `Std.Proof.Math` (`IsLessThanOrEqual` and its lemmas — reuse for the `Nat`-level facts these reduce to), `Std.Decision` (`Empty` — there is no separate `Std.Empty` module; `Empty` is declared inside `Std.Decision`, `lib/std/decision.cure`).

**Strategy (this is proof work — iterate against the elaborator):** `is_less_or_equal` over `Zed` reduces, per constructor case, to a `Nat`-level `IsLessThanOrEqual` fact. Prove each lemma by: (a) reflecting `IsTrue(is_less_or_equal(...))` into the underlying `Nat` order proposition via a helper `fn reflect_leq(a: Zed, b: Zed, ok: IsTrue(is_less_or_equal(a,b))) -> ZedLeqEvidence(a,b)` (an inductive relation on `Zed` you define, mirroring `IsLessThanOrEqual`), (b) doing the structural induction on that inductive evidence reusing `Std.Proof.Math` lemmas, (c) reflecting back to `IsTrue`. This keeps all induction on inductive types (`Nat`, `ZedLeqEvidence`), never on primitive `Int`. Per lemma: `add_preserves_less_or_equal`/`less_or_equal_is_transitive` reuse `adding_the_same_number_preserves_less_than_or_equal` + `less_than_or_equal_is_transitive` directly (the two-sided additive step composes from two applications of the same-addend lemma plus transitivity — `a1≤b1` gives `a1+a2 ≤ b1+a2`, `a2≤b2` gives `b1+a2 ≤ b1+b2`, transitivity closes it). `scale_nonneg_preserves_less_or_equal` is proved by **induction on the `Nat` multiplier `k`** (not on the `ab` evidence): `k=Z` is reflexive (`Z()·a = Z()·b = zed_zero`); `k=S(k')` reduces `S(k')·a ≤ S(k')·b` to `a + k'·a ≤ b + k'·b`, which is exactly the same two-sided additive step as `add_preserves_less_or_equal` (`a≤b` from the hypothesis, `k'·a ≤ k'·b` from the induction hypothesis). **Note: `multiplying_positive_numbers_is_positive` does not establish this** — it proves strict positivity of a product of two positive `Nat`s, not monotonicity of scaling under `≤`, and is not needed here; no dedicated "multiplication preserves `≤`" lemma exists in `Std.Proof.Math` today because none is — the induction bottoms out entirely in addition.

- [ ] **Step 1: Write the failing probe** `integer_laws.cure` (+ `.idr` mirror): apply each lemma to small closed instances and assert the result inhabits the expected `IsTrue(...)` (e.g. `add_preserves_less_or_equal` on `-1≤0` and `0≤2` yields `-1≤2`). For a proof file the primary red is that the *module does not compile* until the lemma bodies are filled; the probe additionally pins behavior for the oracle.
- [ ] **Step 2: Run it red.** `mix cure.oracle otp` and compile `lib/std/integer.cure` → expect unfilled-hole / type errors at the four signatures, surfacing on the `integer_laws` probe. Record.
- [ ] **Step 3: Implement the kit.** Add `ZedLeqEvidence`, `reflect_leq`, and the four lemmas to `lib/std/integer.cure`, following the `proof_math.cure` idiom (empty matches for absurd cases, structural recursion, implicit `{}` binders). **If any lemma resists after honest effort — a stuck index equation, a conversion the elaborator won't close — apply the index-generalization inversion technique (carry the stuck equation as an explicit `Equivalent` argument) before concluding a wall.** On a genuine wall, STOP and write `AUTOPILOT-STATE.md` naming the exact lemma and the elaborator error.
- [ ] **Step 4: Run it green.** `lib/std/integer.cure` compiles; `mix cure.oracle otp` then `mix test test/oracle_replay_test.exs` → the `integer_laws` probe replays `rel=same`.
- [ ] **Step 5: Commit** (`feat(std): ordered-ring lemma kit over Zed for Farkas soundness`, ghost author, explicit pathspec).

---

### Task 3: LIA checker data and the computable `check_lia`

**Files:**
- Create: `lib/std/proof_linear_arithmetic.cure` (module `Std.Proof.LinearArithmetic`)
- Test: `test/oracle/otp/linear_arithmetic_compute.cure` + `.idr`

**Interfaces:**
- Consumes: `Std.Integer` (Task 1), `Std.List` (`foldl`, `zip_with`, `sum`, `map`, `nth`, `length`), `Std.Bool`, `Std.Proof.IntMath` (`IsTrue`).
- Produces:
  - `type Relation = LessOrEqual | LessThan` (no `Equal` — spec §3.1 goal-scope restriction; `Equal` hypotheses are encoded as two `LessOrEqual` atoms by the caller)
  - `rec LinearAtom = { coefficients: List(Zed), constant: Zed, relation: Relation }` — meaning `Σ cᵢ·xᵢ  ⟨rel⟩  constant`
  - `typealias Hypotheses = List(LinearAtom)`, `typealias FarkasWitness = List(Nat)` (nonnegative multipliers; length `|hyps|+1`), `typealias Valuation = List(Zed)` — bare `type X = Y` is genuine-ADT syntax in this codebase (e.g. `type Transition = Row(Atom, Atom, Atom)`, `lib/std/fsm.cure`), not an alias; the alias keyword, confirmed by precedent (`typealias Char = Bounded(1114112)`, `lib/std/char.cure`), is `typealias`.
  - `fn evaluate_atom(atom: LinearAtom, env: Valuation) -> Bool` — dot product of `coefficients` with `env` (via `zip_with multiply` + `sum`-over-`Zed`), compared to `constant` under `relation`
  - `fn negate_atom(atom: LinearAtom) -> LinearAtom` — for `LessOrEqual` (`a ≤ b` ↦ `b + 1 ≤ a`, i.e. `b < a`) and `LessThan` (`a < b` ↦ `b ≤ a`); total on the two allowed relations. **Both outputs are always tagged `LessOrEqual`** — negating a `LessThan` atom (`b ≤ a`) is already non-strict, and negating a `LessOrEqual` atom folds the `+1` into the constant (`b+1 ≤ a`) rather than emitting a `LessThan`-tagged result. This is the same fold `Std.Integer.is_less` already uses (`is_less(a,b) = is_less_or_equal(add(a,zed_one), b)`, Task 1): `<` is definitionally a shifted `≤` over the discrete `Zed`, never a genuinely separate case past this point.
  - `fn combine(atoms: List(LinearAtom), witness: FarkasWitness) -> LinearAtom` — the nonnegative-scaled sum: `foldl` scaling each atom's coefficients+constant by its `Nat` multiplier and adding. **Relation handling:** any `LessThan` atom reaching `combine` is first normalized to the same shifted `LessOrEqual` form `negate_atom` uses (`a < b` ↦ `a+1 ≤ b`) before scaling — so every atom `combine` actually sums is `LessOrEqual`, and `combine`'s result is always `LessOrEqual`. This is a deliberate simplification relative to Micromega's `zChecker` (which tracks strictness through the sum and can conclude the stronger `0 < 0`): because `Zed` is discrete, `0 < 0` and `1 ≤ 0` (⇒ `0 ≤ -1` after the same shift) are the same fact, so folding `<` away before combining loses no soundness and keeps `combine`/`check_lia` needing only the `is_less_or_equal`-only lemma kit from Task 2 (no separate strict-relation preservation lemmas — see Task 4's `combine_preserves_evaluation`).
  - `fn check_lia(hyps: Hypotheses, goal: LinearAtom, witness: FarkasWitness) -> Bool` — `combine(hyps ++ [negate_atom(goal)], witness)` and check the result is the manifest contradiction atom `0 ≤ -1` (coefficients all zero, `LessOrEqual`, constant `≤ -1`); returns `True()`/`False()`. Because of the normalization above, this single `LessOrEqual` check is the only manifest-contradiction form `check_lia` ever needs to test (there is no parallel `0 < 0` case to also check).

- [ ] **Step 1: Write the failing probe** `linear_arithmetic_compute.cure` (+ `.idr`): assert `check_lia` **computes** correctly on closed inputs — the three spec §6 cases at the value level:
  - positive: `hyps = [ -a ≤ 0, -b ≤ 0 ]` (i.e. `a≥0`,`b≥0`), `goal = -(2a+3b) ≤ 0`, a witness that certifies it → `Equivalent(Bool, check_lia(...), True())`;
  - negative antibody: same goal, a **wrong** witness → `Equivalent(Bool, check_lia(...), False())`;
  - boundary (§3.4): a ℤ-only unsat instance (`2n = 1` encoded as `2n ≤ 1 ∧ -2n ≤ -1`, goal `0 ≤ -1`) where a small enumerated set of candidate witnesses each yields `False()` — demonstrating no Farkas witness accepts (documented incompleteness, not a third return value).
- [ ] **Step 2: Run it red.** `mix cure.oracle otp` → the `linear_arithmetic_compute` probe fails on undefined `check_lia`. Record.
- [ ] **Step 3: Implement** the types and functions. Create `lib/std/proof_linear_arithmetic.cure` opening with `@group(:core)` above `mod Std.Proof.LinearArithmetic` (same `:core` preload-group tag as `Std.Integer` above — matches `proof_math.cure`/`proof_int_math.cure` precedent). All are computable/structural — no proofs yet. Add a `fn sum_zed(list: List(Zed)) -> Zed` helper if `Std.List.sum` is `Int`-only.
- [ ] **Step 4: Run it green.** `mix cure.oracle otp` then `mix test test/oracle_replay_test.exs` → the `linear_arithmetic_compute` probe replays `rel=same`; all three compute as asserted.
- [ ] **Step 5: Commit** (`feat(std): LIA checker data + computable check_lia`, ghost author).

---

### Task 4: `check_lia_sound` — the soundness theorem

**Files:**
- Modify: `lib/std/proof_linear_arithmetic.cure` (add proof section)
- Test: `test/oracle/otp/linear_arithmetic.cure` + `.idr` (the canonical spec §6 probe)

**Interfaces:**
- Consumes: everything above — the Task 2 kit (`add_preserves_less_or_equal`, `scale_nonneg_preserves_less_or_equal`, `less_or_equal_is_transitive`, `zero_is_not_less_or_equal_to_negative_one`) and Task 3 (`evaluate_atom`, `combine`, `negate_atom`, `check_lia`).
- Produces the theorem (spec §3.3, over `Zed`):
  - `fn all_hold(hyps: Hypotheses, env: Valuation) -> Bool` — `Std.List.all(hyps, fn(a) -> evaluate_atom(a, env))`
  - `fn check_lia_sound(hyps: Hypotheses, goal: LinearAtom, witness: FarkasWitness, ok: IsTrue(check_lia(hyps, goal, witness)), env: Valuation, holds: IsTrue(all_hold(hyps, env))) -> IsTrue(evaluate_atom(goal, env))`

**Strategy (the payoff — proof, iterate against the elaborator):** three named sub-lemmas, each proved first, then assembled:
1. `combine_preserves_evaluation` — if every atom in `atoms` holds under `env`, the `combine(atoms, witness)` atom holds under `env`. Proof: induction on `atoms`/`witness` (`zip`), each step is `add_preserves_less_or_equal` ∘ `scale_nonneg_preserves_less_or_equal` from the Task 2 kit. This is where nonnegativity of the `Nat` multipliers is load-bearing.
2. `negated_goal_or_goal` — `IsTrue(evaluate_atom(negate_atom(goal), env))` is the exclusive negation of `IsTrue(evaluate_atom(goal, env))` for the two allowed relations (a small case analysis; reuse `Std.Proof.IntMath.true_is_not_false`).
3. Assemble (constructive case-split, not classical excluded middle — no axiom): match on `Std.Proof.IntMath.decide_is_true(evaluate_atom(goal, env))` (the same decidable-`Bool` idiom `proof_int_math.cure` itself uses), an ordinary pattern-match on the computed `Bool`, never an assumed law of excluded middle over an arbitrary proposition. `Yes(proof)` branch: done, return `proof` directly. `No(_)` branch (`evaluate_atom(goal, env)` computes `False()`): by (2)'s exclusive dichotomy, `negate_atom(goal)` then evaluates `True()`, so all of `hyps ++ [negate_atom(goal)]` hold, so by (1) `combine(...)` holds under `env`. But `ok : IsTrue(check_lia(...))` means `combine(...)` **is** the `0 ≤ -1` atom, whose evaluation is `False()` — contradiction via `zero_is_not_less_or_equal_to_negative_one`, producing `Empty`; an empty match on that discharges the branch (ex falso), yielding `IsTrue(evaluate_atom(goal, env))` in both branches.

- [ ] **Step 1: Write the failing probe** `linear_arithmetic.cure` (+ `.idr`) — the spec §6 canonical probe: the three value-level cases from Task 3 **plus** an application of `check_lia_sound` producing `IsTrue(evaluate_atom(goal, env))` for the positive case's `goal`/witness under a concrete `env`, and a second application modeling the genuine refinement shape `fn f({n:Int|n>0}) -> {m:Int| m > n}` — i.e. `hyps = [n > 0]` and `goal = [m > n]` as `LinearAtom`s, for a concrete `n`/`m`/witness. **This second case must be expressed entirely as `LinearAtom`/`Valuation`/`check_lia_sound` applications over `Zed`, never as an actual Cure refinement-typed function using `{n:Int|...}` surface syntax** — the primitive-`Int` refinement surface is the out-of-scope `#4` bridge (spec §0 non-goals), and this probe must not implicitly depend on it. `%default total` in the `.idr`.
- [ ] **Step 2: Run it red.** Module fails to compile at `check_lia_sound` (unfilled). `mix cure.oracle otp` fails on the `linear_arithmetic` probe. Record.
- [ ] **Step 3: Prove it.** Add `combine_preserves_evaluation`, `negated_goal_or_goal`, and `check_lia_sound` to `lib/std/proof_linear_arithmetic.cure`. Expect iteration; apply index-generalization inversion for stuck GADT index equations. **On a genuine elaborator wall, STOP and write `AUTOPILOT-STATE.md`** naming the sub-lemma and error — do not weaken the theorem or add an axiom.
- [ ] **Step 4: Run it green.** `lib/std/proof_linear_arithmetic.cure` compiles (kernel accepted the proof); `mix cure.oracle otp` then `mix test test/oracle_replay_test.exs` → the `linear_arithmetic` probe replays `rel=same`.
- [ ] **Step 5: Commit** (`feat(std): check_lia_sound — Farkas certificate soundness (kernel-checked)`, ghost author).

---

### Task 5: Register the probe, full replay, and stdlib integration check

**Files:**
- Verify only (no manifest to modify — see Step 1): `lib/std/integer.cure`, `lib/std/proof_linear_arithmetic.cure` (author in `lib/std/`, never `priv/std`)
- Test: full oracle replay + full suite

- [ ] **Step 1:** There is no separate stdlib manifest/allowlist to edit. Physical inclusion in the bundled build is fully automatic: `mix compile` runs `cure.bundle_stdlib` (`lib/mix/tasks/cure.bundle_stdlib.ex`), which wildcard-globs every `lib/std/*.cure` file into `priv/std/` unconditionally — a new file needs no registration there. The one real lever is the `:core` preload-group tag: confirm `lib/std/integer.cure` and `lib/std/proof_linear_arithmetic.cure` both open with `@group(:core)` (added at file-creation time in Tasks 1 and 3 above) so `lib/cure/stdlib/preload.ex`'s `filter_by_groups`/`stdlib_modules(:core)` includes them in the `:core` closure like the sibling proof modules. Red signal: `grep -L "@group(:core)" lib/std/integer.cure lib/std/proof_linear_arithmetic.cure` prints a filename (the tag is missing) — add it if so.
- [ ] **Step 2: Run the full oracle replay once.** `mix cure.oracle` (all clusters) then `mix test test/oracle_replay_test.exs` → every new probe in the `otp` cluster (`integer_ops`, `integer_laws`, `linear_arithmetic_compute`, `linear_arithmetic`) is `rel=same`, no prior cluster or probe regressed.
- [ ] **Step 3: Run the full suite once** (`mix test`, one build at a time — matches this repo's established plan convention, e.g. `docs/superpowers/plans/2026-07-02-dependent-match-surface-plan.md`) → green, no regressions.
- [ ] **Step 4: Commit** — only if Step 1 found a missing `@group(:core)` tag and you added it (`chore(std): register Std.Integer + Std.Proof.LinearArithmetic in core bundle`, ghost author); if both files already carried the tag from Tasks 1/3, there is nothing to commit here and this step is a no-op.

---

## Self-Review

- **Spec coverage:** §3.1 types → Task 3; §3.2 `check_lia` → Task 3; §3.3 `check_lia_sound` → Task 4; §3.4 boundary case → Task 3 Step 1 (boundary) + Task 4 probe; §5 layer map (stdlib only) → all tasks; §6 four test obligations → Tasks 3–4 probes + Task 5 replay; §6 discipline (red-before-green, immutable probes) → Global Constraints + each task's Steps 1–2. The inductive-integer substrate is a plan-level elaboration of §3.1's `List Int`, forced by the "no axioms / no kernel change" constraint (primitive `Int` has no induction); the primitive-`Int` surface bridge is explicitly spec-deferred to #4.
- **Placeholder scan:** proof *bodies* are given as strategy + exact signatures + named sub-lemmas rather than final proof terms — this is inherent to theorem-proving (the term is discovered against the elaborator) and is bounded by exact types and the red/green oracle gate, not left vague. All data/computable code is concrete.
- **Type consistency:** `check_lia(hyps, goal, witness)` arg order is identical in Tasks 3 and 4 and matches spec §3.2/§3.3; `IsTrue` is the single evidence vehicle throughout (Tasks 2–4), consistent with `Std.Proof.IntMath`; `FarkasWitness = List(Nat)` (nonnegative) is consistent between Tasks 3 and 4 and is what `scale_nonneg_preserves_less_or_equal` (Task 2) consumes.

## Risk note (for the executor and reviewer)

Task 2 (ordered-ring kit) and Task 4 (soundness assembly) are genuine dependent-proof work and are the run's long-poles. The plan is decomposed so each earlier task commits independently green; if Task 2 or 4 hits an elaborator wall that the index-generalization technique cannot route around, the correct outcome is a clean **Halt** with `AUTOPILOT-STATE.md` naming the exact stuck lemma — not a weakened theorem, a deleted probe, or an axiom. Partial progress (Tasks 1, 3, and whichever lemmas landed) remains valid, committed, and useful.
