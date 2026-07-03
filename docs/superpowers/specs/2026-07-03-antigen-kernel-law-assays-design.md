# Antigen kernel-law assays — design (Run B)

**Status:** approved (design gate — operator batch-approved A/B/C/D). Autopilot on `autopilot/antigen-tier-b`. Pure-Antigen, **kernel-API only** (read-only calls into `Cure.Core.*`; **no TCB edits**).

## 1. Motivation

Antigen's assays check invariants the author thought to state. Two whole families the kernel and Shrink silently depend on are **unchecked**: (a) the **de Bruijn algebra** (`Term.shift`/`Term.subst` — a capture bug here corrupts every substitution the kernel and the shrinker perform, invisibly), and (b) **reduction order-independence** (a `whnf` that disagrees with `nf` is a soundness hole). Subject reduction and `nf(nf t)=nf t` are already covered by `Assays.Term`; this run adds three *new* relational assays that current coverage misses. All are checkable through the public kernel API alone.

## 2. Architecture — reuse `:typed_term`, add assay-ids

No new challenge **kind**. `:typed_term` challenges already carry `payload.{sig, ctx, type, term}` and have full plumbing (Coverage, Corpus, Shrink, health). The existing type-directed generator entry `Antigen.Generators.Term.typed_term(assay_id)` produces a `:typed_term` challenge tagged with any assay-id (this is exactly how `default_gen` already emits `"term/infer_check"`, `"term/subject_reduction"`, `"term/normalization"`). This run adds three assay-ids dispatched to one new assay module:

- `kernel/shift_subst` — de Bruijn algebra laws
- `kernel/weakening` — typing preserved under an unused binder
- `kernel/confluence` — `whnf`-then-`nf` agrees with `nf`

**Wiring (mirrors Run A / existing verticals):**
- New module `Antigen.Assays.KernelLaw` with `run/1` dispatching on `c.assay`.
- `Antigen.Runner.assay_module/1` gains the three id → `Antigen.Assays.KernelLaw` rows.
- `Mix.Tasks.Antigen.default_gen/0` gains three branches: `Term.typed_term("kernel/shift_subst")`, `…("kernel/weakening")`, `…("kernel/confluence")`. **This changes `default_gen`'s branch count from 11 to 14** — Run A's group-guard test (`gen_group_table/0` + the "exactly 11 branches" assertion) and the position→group table **must be updated in lockstep** (the three new branches all emit `:typed_term`, so they extend **Group T**; the guard becomes 14 branches, `t: [4,5,6,9,10,11,12,13,14]`). This is the coupling Run A's guard test was designed to surface — honor it, don't bypass it.

Because these are ordinary `:typed_term`s, they flow through the existing well-formedness filter, coverage dedup, health metrics (binder_usage/reduction_activity), and Shrink for free. No Coverage/Corpus/Challenge changes.

## 3. The three assays (`Antigen.Assays.KernelLaw.run/1`)

Each returns `:ok` or `{:violation, detail}` over `p = c.payload`, with `ctx = SigMenu.rebuild_context(SigMenu.env_of(p.sig), p.ctx)` (the standard reconstruction the other assays use). `t = p.term`.

### 3a. `kernel/shift_subst` — de Bruijn algebra

Checks a family of laws that hold for the kernel's **targeted, capture-avoiding, non-renumbering** `subst` (confirmed: `subst(u,j,r)` replaces index `j`, shifts `r` under binders, never decrements other indices) and its `shift`. Concrete instances, each a pure `Term` computation on `t` (no kernel state needed — these are syntactic identities), all of which are **provably true** and fail loudly on an off-by-one/capture bug:

1. **Shift-zero identity:** `shift(t, 0, 0) == t`.
2. **Shift composition (same cutoff):** `shift(shift(t, a, c), b, c) == shift(t, a + b, c)` for sampled small `a,b,c` (e.g. `a,b ∈ {1,2}`, `c ∈ {0,1}`).
3. **Substitute-a-fresh-index is a no-op:** `subst(shift(t, 1, c), c, r) == shift(t, 1, c)` for any `r` — because `shift(t,1,c)` has **no** free occurrence of index `c` (every index ≥ c was bumped to ≥ c+1), so the substitution finds nothing to replace. Sampled `c ∈ {0,1}`, `r ∈ {Z, S Z}` (closed Nats). This jointly exercises `shift` and `subst` and directly catches the capture/renumbering class.

A violation returns `{:violation, {:shift_subst_law, which_law, ...}}`. (The full shift/subst *commutation* lemma — `shift(subst(t,j,r),a,c)` vs `subst(shift(t,a,c),…)` — is deliberately **not** asserted here: its exact cutoff arithmetic is easy to state wrongly and would risk a false-positive assay. The three laws above are unconditionally true for this calculus and already cover the capture/off-by-one failure modes. Spec review must empirically confirm all three hold on a large sample of generated terms before they are trusted.)

### 3b. `kernel/weakening` — unused-binder invariance

If `infer(ctx, t) = {:ok, v}`, then inserting an unused binding at the front and shifting `t` past it must still type, at the weakened type. Concretely, for a fresh domain `A` (reuse a menu type, e.g. `Nat` as a `Value` via the kernel's own evaluation of `{:data,:Nat,[],[]}`):

- Let `ctx' = Context.extend(ctx, A_value)` and `t' = Term.shift(t, 1, 0)`.
- **Success-preservation (floor):** `infer(ctx, t)` ok ⟹ `infer(ctx', t')` ok. A weakening bug that breaks typability is caught here.
- **Type agreement (if both succeed):** quoting both inferred type-values to terms — `q = Normalise.quote(v, Context.length(ctx))`, `q' = Normalise.quote(v', Context.length(ctx'))` — must satisfy `q' == Term.shift(q, 1, 0)`. The weakened context's inferred type is exactly the original type shifted past the new binder.

Violations: `{:violation, {:weakening_broke_typing, err}}` or `{:violation, {:weakening_type_mismatch, q, q'}}`. If `infer(ctx, t)` itself fails (a genuinely ill-typed generated term — possible if the generator's guarantee is imperfect), the law is **vacuously satisfied** (`:ok`) — this assay tests weakening, not the generator; a bare infer failure is not a weakening violation.

### 3c. `kernel/confluence` — reduction order-independence

`nf` reached via a `whnf` prefix must equal `nf` reached directly:

- `full = Normalise.nf(ctx, t, fuel: Assays.Term.assay_fuel())`
- `staged = case Normalise.whnf(ctx, t, fuel: …) do :fuel_exhausted -> :skip; w -> Normalise.nf(ctx, w, fuel: …) end`
- If either `full` or the inner `nf` is `:fuel_exhausted` (or `whnf` exhausts), return `:ok` (**vacuous** — fuel exhaustion is a resource bound, not a confluence violation; the existing health line already tracks fuel exhaustion separately).
- Otherwise assert `full == staged` (syntactic equality of normal forms). Violation: `{:violation, {:confluence_mismatch, full, staged}}`.

## 4. Testing (TDD, per Stage 4)

Unit tests in `test/antigen/assays/kernel_law_test.exs`, driving `Antigen.Assays.KernelLaw.run/1` on hand-built `:typed_term` challenges (no sampling in the unit tests — deterministic fixtures):

1. **shift_subst positive:** a fixture term (`λNat. S (var 0)` under empty ctx) satisfies all three laws → `:ok`. **shift_subst negative:** a *stubbed* violation is not directly constructible without a broken kernel, so instead assert the law-checker itself computes the identities correctly by re-deriving law 2/3's two sides in the test and asserting they match what the assay compares (guards against the assay tautologically returning `:ok`). (This is the same "does the check actually check" concern Run A's plan review raised; the real adversarial negative lives in Run C, which injects a broken kernel.)
2. **weakening positive:** a closed well-typed `t` (e.g. `S Z : Nat`) → `:ok`, and the type-agreement leg holds (`quote` of the weakened inference equals `shift(quote(orig),1,0)`). **weakening vacuous:** an ill-typed term → `:ok` (vacuous), not a false violation.
3. **confluence positive:** a redex fixture (`(λNat.var 0) (S Z)`) normalizes identically via `nf` and `whnf`→`nf` → `:ok`. **confluence vacuous:** if a fixture exhausts fuel, `:ok`.
4. **registry + guard:** `Runner.assay_module_for("kernel/shift_subst")` (and the other two) returns `Antigen.Assays.KernelLaw`; the updated `default_gen` group-guard test asserts **14** branches with `t: [4,5,6,9,10,11,12,13,14]`.
5. **integration:** a short `Runner.explore` over `Term.typed_term("kernel/confluence")` (and the other two) runs to completion with 0 infections on the current (sound) kernel — evidence the assays don't false-positive on real generated terms.
6. **Stage 5:** full suite once + `mix antigen --count 800` showing the three new verticals participate (health lines unaffected; 0 infections).

## 5. Files

- **Create:** `lib/antigen/assays/kernel_law.ex`, `test/antigen/assays/kernel_law_test.exs`.
- **Modify:** `lib/antigen/runner.ex` (3 `assay_module/1` rows; **update `@group_table` + `gen_group_table/0` to 14 branches**), `lib/mix/tasks/antigen.ex` (`default_gen/0` +3 branches), `test/antigen/runner_test.exs` (update the group-guard test to 14).
- **Untouched:** `Cure.Core.*` (TCB), Coverage, Corpus, Challenge, Shrink.

## 6. Non-goals (YAGNI)

- The full shift/subst **commutation** lemma (risk of a wrong law; §3a covers the failure modes with unconditionally-true laws).
- A **new challenge kind** for kernel laws (reusing `:typed_term` gets all plumbing free).
- **Differential vs an independent checker** (Idris port) — needs the port wired; a separate run.
- **Generating deliberately-ill-typed terms** to stress weakening — Run C (assay sensitivity) supplies the adversarial negative by injecting a broken kernel; here the kernel is trusted and the assays must be quiet on it.
- Confluence across *arbitrary* reduction strategies — only the two the kernel exposes (`whnf`, `nf`).

## 7. Risks

- **A stated law is subtly false** → the assay infects a sound kernel (false positive). Mitigation: §3a restricts to three unconditionally-true identities; spec review empirically samples all three (and the weakening/confluence properties) over thousands of generated terms and must see 0 violations before they ship.
- **`default_gen` grows to 14 and Run A's guard test isn't updated** → guard goes red (by design). Mitigation: §2/§5 make the lockstep update explicit; the guard failing is the safety net working.
- **`quote` depth/shift mismatch in weakening** makes the type-agreement leg wrong. Mitigation: success-preservation is the floor (always sound); the type-agreement leg is reviewed against `Normalise.quote`'s actual depth convention, and if its exact form can't be pinned, it degrades to success-preservation only.
