# Cross-module lemma import — the prelude-in-slice fix

*2026-07-17. A completeness bug in the dependent pipeline's module import surfaced while
building `Std.Otp.ReplyConservation`: `use Std.Proof` failed for any lemma with a
computed-index `Equivalent` return type. Diagnosed with `Cure.Dev.Trace`, fixed in
`lib/cure/elab/program.ex`.*

## Symptom

```
use Std.Nat
use Std.Proof
fn t(p: Nat, a: Nat) -> Equivalent(Nat, plus(p, S(a)), S(plus(p, a))) = plus_succ_right(p, a)
```

→ REJECT `{:conversion_failure, Equivalent(Nat, Z, Z), Equivalent(Nat, plus(Z, Z), Z)}`.
All `Std.Proof` lemmas (`plus_zero_right`/`plus_succ_right`/`plus_comm`) failed identically.
Direct `plus` and the prelude primitive `reflexive` worked cross-module — only *user
lemmas whose body needs δ-reduction* failed.

## Root cause

Traced (`Cure.Dev.Trace.calls(Cure.Core.Kernel, :check, …)`): the failing conversion is
`Std.Proof.plus_zero_right`'s OWN `Z`-branch (`reflexive(Z) : Eq(Z,Z)` vs its return type at
`n=Z`, `Eq(plus(Z,Z), Z)`) — with `plus(Z,Z)` a stuck neutral. In the failing context's
signature (`Cure.Core.Env`), `Std.Nat#plus` was **entirely absent** (`certified?` false,
`get_def` nil).

`proof.cure` has no `use Std.Nat`; it relies on `Std.Nat` being in `@auto_prelude`. The
top-level `elaborate` (`shadow_resolved_imports`) adds the auto-prelude via
`auto_prelude_imports(ast) ++ imports(ast)`, but the **per-module slice builder
`module_slice_env/1`** — used to slice each imported module — used only `imports(ast)` (the
module's explicit `use`s). So an imported module's body was elaborated without the
auto-prelude; a reference to a prelude def it never `use`d dangled and never δ-reduced.
`proof.cure` compiles fine in the PRELOAD (which accumulates prior modules) but not when
sliced for cross-module import.

Note: `@prelude`/`prelude_slice_env` was the wrong lever — it makes the *type* `Nat` ambient
(`@auto_prelude_types`), not the *function* `plus`. The fix needed the whole `@auto_prelude`
module.

## Fix

`module_slice_env` now merges `slice_prelude_env(ast)`: the flat merge of each
`@auto_prelude` module's own independent slice (the same construction as
`shadow_resolved_imports`). Guard = `find_module_name(ast) in @auto_prelude` — auto-prelude
modules skip it (they are self-sufficient, and this terminates the recursion). The guard is
`@auto_prelude` membership, NOT `prelude_source?` (which is true for *every* registered
stdlib module and would skip `Std.Proof`/`Std.List`/… too).

Scoped to `module_slice_env` only: adding it to `import_source_env` as well compounded into
a 10-minute timeout (prelude construction itself runs through `import_source_env`, and there
is no slice memoization). Cost: ~74 ms per import-heavy elaboration, bounded and linear (each
non-auto slice rebuilds the 7 auto-prelude slices once; those don't recurse). A future
memoization pass (persistent_term, as `prelude_manifest` already uses) would erase it.

## Verified

- The three `Std.Proof` lemmas now type-check cross-module.
- `Std.Otp.ReplyConservation` reuses `Std.Proof.plus_succ_right`/`plus_zero_right`
  cross-module (dogfood).
- Full suite green; no deterministic regression (the one full-suite `union_test` failure
  reproduces neither alone nor deterministically — a pre-existing codegen-load ordering flake).

## Follow-up (not blocking)

- Memoize `module_slice_env`/`slice_prelude_env` to remove the ~74 ms.
- Transitive imports (`import_source_env` path) still lack the auto-prelude, so a module
  imported *only* transitively that relies on an un-`use`d prelude function would still fail;
  fixing it needs the memoization first (else the timeout returns).
