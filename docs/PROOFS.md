# Proofs in Cure

`proof` containers are currently a legacy proof-shape feature. They let source
code group law-shaped declarations, and the legacy checker requires each binding
to return an `Eq(...)`-looking type or a refinement type. They do not yet
elaborate those propositions to `Cure.Core.Kernel`.

That distinction matters: a function in a `proof` container can return
`:cure_refl`, but the trusted dependent kernel is not yet proving the stated
law from Cure source.

## Shape

A proof container looks like a module:

```cure
proof Laws.Arithmetic
  fn plus_zero(_n: Int) -> Eq(Int, n, n) = :cure_refl
  fn plus_comm(_a: Int, _b: Int) -> Eq(Int, a, b) = :cure_refl
```

Every function's return type must be proof-shaped. The body is usually the
runtime atom `:cure_refl`, matching the current `Std.Equal` compatibility API.

## Current Use

- A `proof` keyword documents intent: everything inside is intended as a law,
  not computation.
- The checker applies only a shape gate today. This is useful as a migration
  staging point, but it is not an Idris/Agda-style proof checker.
- `Std.Proof` remains a catalog of law-shaped declarations until public
  `Eq`/`refl`/`rewrite` elaborates to Core.

## Available Legacy Laws In `Std.Proof`

| Law | Signature |
|-----|-----------|
| `plus_zero/1` | `Eq(Int, n, n)` |
| `zero_plus/1` | `Eq(Int, n, n)` |
| `plus_comm/2` | `Eq(Int, a, a)` |
| `append_nil/1` | `Eq(List(T), xs, xs)` |
| `map_id/1` | `Eq(List(T), xs, xs)` |

## Related Features

- `Cure.Core` already has equality and rewrite nodes with kernel tests.
- `Std.Equal` is still a runtime-token compatibility module.
- `Std.Refine` provides SMT-backed refinement aliases and predicates.
- `assert_type expr : T` is a compile-time type assertion that erases at
  runtime, but it is separate from the trusted dependent proof kernel.
