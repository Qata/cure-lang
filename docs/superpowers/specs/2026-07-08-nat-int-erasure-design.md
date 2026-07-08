# Nat→Int Runtime Erasure — Design

**Status:** approved design (operator standing batch authorization; the feature is Phase 2 of the operator-approved builtin-inductive foundation spec, `docs/superpowers/specs/2026-07-03-builtin-inductive-foundation-design.md` §3 / lines 215–284).
**Layer:** C (untrusted erase/emit, `lib/cure/elab/emit.ex`) + tests. **Zero changes under `lib/cure/core/`** and zero changes to `lib/cure/elab/erase.ex`'s representation behavior (Core stays inductive end-to-end; see §2.5).
**Batch:** parity queue item C-3 (task #12), worktree `kernel-parity-batch`, branch `autopilot/kernel-parity-batch`.

## §0 Context — Phase 1 is landed; this is pure consumption

The foundation's Phase 1 (TCB, gated) landed in full: the `:nat` schema `[{:Z, 0}, {:S, 1}]` (`lib/cure/core/builtins.ex:16`), seeding (`builtins.ex:55-60,91-97`), the registry (`lib/cure/core/inductive.ex:125-143`, `builtins:` field), and the `@builtin(:nat)` binding on the prelude Nat (`lib/std/nat.cure:9-10`, honored by `Cure.Elab.Program.maybe_register_builtin/3`, `program.ex:738-757`, prelude-only). Test pins: `test/cure/core/builtins_seed_test.exs:22`, `builtins_schema_test.exs:44`, `no_gradual_any_test.exs:23`.

What does NOT exist is the representation change itself: today `Z()` emits the BEAM atom `:Z` and `S(n)` the tagged tuple `{:S, n}` (`lib/cure/elab/emit.ex:158-169`), so a Nat n is O(n) heap — fatal on ESP32/AtomVM, the repo's stated reason to exist. The Bool→atom special case (`emit.ex:160-161`, helpers `bool_ctor?/bool_atom/bool_atom_or_self` at `emit.ex:363-370`) is the landed structural precedent, and `builtins.ex`'s moduledoc (lines 4-9) already documents the intended `Z/S -> int` mapping. This spec is the Idris "Nat hack" (`%builtin Natural`; vendored: `reference/idris2/src/TTImp/ProcessBuiltin.idr:211-226` marks, `Core/CompileExpr.idr:19-56` ZERO/SUCC ConInfo flags, backends lower Z→0 / S→+1 / case→zero-test-and-minus-one), realized as registry lookups at the two emit hook sites.

## §1 Goal — the four lowering rules (foundation §3, lines 215-219)

For the family registered as `Inductive.builtin(env, :nat)` — and ONLY that family (§2.4):

1. `Z()` ⇒ integer `0`; `S(e)` ⇒ `e + 1` (native BEAM `+`).
2. `case n of Z() -> a | S(k) -> b` ⇒ BEAM `case n of 0 -> a; N when N > 0 -> K = N - 1, b` (k binds the predecessor; see §2.2c).
3. Nat-typed prim/arithmetic ⇒ machine op — **vacuous in v1**: no Nat-typed `{:prim}` exists (Std.Nat arithmetic is recursive `:case` defs, `lib/std/nat.cure`); those defs compile unchanged over the Int rep (§2.6).
4. `S`/`Z` as first-class values ⇒ `0` and the increment closure `fun(X) -> X + 1 end`.

Runtime Nat becomes O(1) space. Time complexity of Std.Nat arithmetic is unchanged (O(n) recursion) — the ESP32 killer was space, and native-op inlining is a non-goal (§6).

## §2 Design

### §2.1 Hook sites — emit-layer only, mirroring Bool

Two sites in `lib/cure/elab/emit.ex`, exactly where Bool hooks today:

- `lower(env, {:ctor, name, args}, ctx)` (`emit.ex:158-169`): before the generic atom/tuple fallthrough, a `nat_ctor?` check (same shape as `bool_ctor?` at 363: `Inductive.builtin(env, :nat) == ctor_family(env, name)`) dispatches `Z/0` → integer literal `0`, `S/1` → the `+ 1` form on the lowered argument.
- `lower(env, {:case, …}, ctx)` (`emit.ex:171-173`) / `branch_clause/3` (`emit.ex:308-333`): when the scrutinee's branch constructors belong to the `:nat` family, emit the integer-clause form of rule 2 instead of atom/tuple patterns.
- Ctor-in-function-position / first-class references (wherever `emit.ex` lowers a bare constructor as a value or partial application — the plan locates the exact clause): `Z` → `0`, `S` → `fun(X) -> X + 1 end`.

No new IR node, no new registration mechanism, no `erase.ex` change. This mirrors Idris precisely: the ZERO/SUCC decision is a per-constructor nominal flag consumed by the code generator, nothing upstream knows.

### §2.2 Lowering fine points

a. **Clause order/guards.** The Z-branch lowers to the literal pattern `0`; the S-branch lowers to a fresh variable pattern with guard `when N > 0` (not a bare catch-all), so emitted clause order cannot silently change semantics regardless of the order branches arrive in from Core, and a representation bug (a negative int reaching a Nat case) crashes loudly rather than binding `k = -1` and continuing wrong. The kernel guarantees a well-typed Nat scrutinee, so the guard is belt-and-braces, not load-bearing.

b. **Deep patterns need no special handling.** Core `:case` is single-level (the matrix compiler splits nested patterns into single-level cases before elaboration), so `S(S(m))` arrives as two nested single-level cases and lowers compositionally to two `- 1` bindings.

c. **Frame accounting.** The S-branch body's de Bruijn frame counts the field (index 0 = the bound predecessor, per the comment at `emit.ex:307-320`). The S-field must therefore still be a bound BEAM variable — bound by `K = N - 1` at the clause head rather than by a tuple-element pattern — and the body lowering proceeds unchanged against the same frame. This is the single trickiest edit; the plan carries a dedicated red test (nested `S(S(m))` match whose body uses `m`).

d. **`Z()` pattern ≡ literal `0`.** Once Nat is an int at runtime, a `Z()` constructor pattern and an integer-literal `0` pattern (the `try_literal_match` path over primitive scrutinees, which is Int-typed and unrelated to Nat today) coincide as the BEAM pattern `0`. This is an identity to state, not machinery to build — Nat-typed scrutinees never take the literal-chain path and Int-typed scrutinees never take the ctor path.

### §2.3 The generics gap — resolved by parametricity, no monomorphisation

The foundation spec's open question (lines 228-241) asks how a function generic over `a: Type`, instantiated at `Nat` in one call and another inductive elsewhere, reconciles representations in one unspecialized body. Resolution: **the Int representation is global and uniform, and no reconciliation is needed**, because on a dynamically-typed target the only operations an unspecialized body can perform on an `a`-typed value are opaque (pass, store, return, put in a container). Constructor-matching a scrutinee requires the elaborator to know its type is the `Nat` family — a bare type-parameter-typed scrutinee cannot elaborate `Z()`/`S(k)` arms (there is no `:vdata` family to dispatch on). So:

- A `Pair(Nat, Nat)` or `Lst(Nat)` simply holds small ints where it held tuples; the container's own representation is untouched.
- Every site that CAN deconstruct a Nat knows it statically (its scrutinee type elaborated to the `:nat` family), which is exactly the set of `:case`s §2.1 lowers.
- This matches Idris: ZERO/SUCC flags are global, and Idris's Nat hack ships with no monomorphisation.

The spec pins this with a polymorphic-container test (a generic pair holding Nats, constructed and deconstructed through generic code, runtime shape `{:MkP, 0, 2}`-style). If the plan-time sweep finds ANY elaborator path that lets a ctor pattern match a type-parameter-typed scrutinee (refining `a := Nat`), that is a STOP-and-report — it would falsify the parametricity argument and the design needs the operator.

### §2.4 Nominal, not structural

The rep applies only to the family-id registered under `Inductive.builtin(env, :nat)` — the prelude `Std.Nat` (foundation lines 138-155). A locally redeclared `type Nat = Z | S(Nat)` keeps tuples, silently (the foundation's explicit choice). Consequences pinned as regression tests, not changed:

- `test/cure/compiler/dependent_vec_codegen_test.exs` uses a local Nat: its tuple-shape assertions **stay** and double as the nominal-no-op pin.
- The `phase35/` ESP32 demos redeclare Nat locally and therefore get no benefit until they `use Std.Nat`; the recommended lint/compiler note stays out of scope (foundation stance, §6).

### §2.5 What does not change (the layering pins)

- **Kernel and eval untouched:** the kernel keeps checking and reducing Nat as the inductive; `Eval` keeps producing `{:ctor, :S, [...]}`-shaped values. Every `test/cure/core/*` pin (size_change, cycle_rule, conv, certify, unify_indices, builtins_*) must pass unchanged — they are the regression guard that the "checking-time fiction" stayed intact.
- **Erased Core untouched:** `erase.ex` still emits `{:ctor, :Z, []}` / `{:ctor, :S, [kept]}`; representation is chosen at BEAM lowering. Tests asserting on erased-Core shapes (e.g. `test/cure/elab/global_namespace_soundness_test.exs:179-189`) must pass unchanged.
- **Bool behavior untouched**, including `connective_inline` (`emit.ex:215-235`).

### §2.6 Arithmetic

`Std.Nat` arithmetic defs (recursive `:case` over Nat) compile unchanged and now operate on ints: correct by the representation-agreement property, O(1) space, still O(n) time. Inlining known Std.Nat ops to native `+`/`-` (the `connective_inline` precedent) is an explicit non-goal/follow-up — v1 lands the representation, not the arithmetic acceleration. (Idris's `NaturalToInteger`/`IntegerToNatural` identity pragmas are the analogous follow-up surface.)

## §3 Trust boundary and verification

This is the foundation's **Phase 2: untrusted, ungated** (lines 268-272). A lowering bug yields a wrong runtime value, never an unsound acceptance — no TCB review gate applies (and none is available: nothing under `lib/cure/core/` may change). Verification is:

1. Strict red-green unit tests (per lowering rule).
2. **Representation-agreement property (foundation line 224):** a new Antigen assay (`elab/nat_rep`) with a seeded generator of closed, well-typed `Std.Nat` programs (bounded-depth arithmetic + matching + HOF-S/Z + container round-trips): for each, the kernel's inductive `Eval` result (decoded `{:ctor,:S,…}` spine → integer) must equal the BEAM execution result (already an integer). Kernel eval is the oracle — it is the trusted semantics; emit is the system under test.
3. The full suite including oracle replay (differential fixtures pin verdicts, not runtime shapes — replay must stay green untouched).

## §4 Test-migration policy (the deliberate behavior change)

Runtime Nat shapes change from `{:S, {:S, :Z}}`-style tuples to ints — a spec'd, operator-authorized behavior change (foundation §3), so the affected **BEAM-runtime** pins are updated as part of the feature's red-green, under a strict protocol:

- **Flip:** only assertions on `apply(mod, …)` results (and closure-application results) whose values are Std.Nat-built runtime Nats — `{:S, :Z}` → `1`, `:Z` → `0`, values nested in containers likewise (`{:MkP, :Z, {:S,{:S,:Z}}}` → `{:MkP, 0, 2}`). The plan enumerates every file+line at plan time (scout inventory: ~29 files under `test/cure/elab/` incl. `polymorphic_function_test.exs`, `auto_generalize_test.exs`, `first_class_function_test.exs`, `nested_pattern_test.exs`, `guard_test.exs`, and the new `guard_lint_test.exs`; the plan re-greps against the then-current tree). The executor applies the enumerated flips mechanically; any pin that does not flip exactly as predicted, or any pin not on the list that fails, is STOP-and-report.
- **Do not touch:** erased-Core-shape assertions; all `test/cure/core/*`; local-Nat fixtures (`dependent_vec_codegen_test.exs` — nominal no-op pin, §2.4); oracle `verdicts.json` (verdicts are accept/reject, representation-independent).
- The flips land in the SAME commit as the emit change that necessitates them (a green tree at every commit), with the flip list reproduced in the commit message body or the plan checked off per file.

## §5 Idris divergence

None. This aligns Cure WITH Idris (the Nat hack is Idris-sourced); oracle relations are unaffected because the oracle compares elaboration verdicts, not runtime representations.

## §6 Non-goals

- Monomorphisation / specialization machinery (§2.3 shows it is not needed).
- Native inlining of Std.Nat arithmetic (`connective_inline`-style) — follow-up.
- GMP/bignum kernel acceleration (foundation: type-level Nats are small; kernel unchanged).
- The `use Std.Nat` lint / compiler note for locally-redeclared Nats (foundation: out of scope).
- `Bounded`/`Fin` as a further native-int builtin (queued separately in the stdlib-dependent-expansion plan).
- Any change to `lib/cure/elab/erase.ex` representation behavior, `lib/cure/core/*`, `lib/cure/types/*`, `lib/cure/compiler/*` (two-pipeline discipline; `test/cure/compiler/dependent_vec_codegen_test.exs` is a test, not that pipeline's code).

## §7 Acceptance criteria

1. A `use Std.Nat` program's runtime Nats are BEAM ints: `S(S(Z()))` evaluates to `2` via `apply`; matching `S(k)` binds `k = 1`; a body using a two-deep `S(S(m))` binding computes correctly.
2. First-class `Z`/`S` work as values: passing `S` to a HOF and applying yields ints.
3. A generic container holding Nats round-trips through unspecialized generic code with int elements (§2.3 pin).
4. A locally-redeclared Nat still produces tuples (§2.4 pin, existing fixture unchanged).
5. Antigen `elab/nat_rep` representation-agreement assay green: kernel-eval-decoded integer == BEAM integer on the generated corpus.
6. `git diff` of the landed work: zero changes under `lib/cure/core/`, `lib/cure/types/`, `lib/cure/compiler/` (code), and `lib/cure/elab/erase.ex`; every `test/cure/core/*` and erased-Core-shape test unchanged and green.
7. Full gate green: `mix test test/antigen/` then full `mix test` (with oracle replay), zero failures; every §4 flip matches its plan-time prediction.
