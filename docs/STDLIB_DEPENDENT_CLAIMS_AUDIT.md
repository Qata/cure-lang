# Stdlib Dependent-Type Claims Audit

This note records stdlib-facing APIs and documentation that currently claim,
imply, or rely on dependent typing without being checked by the trusted
dependent kernel.

The current compiler routes a module through `Cure.Elab`/`Cure.Core` only when
the parsed AST contains an `indexed type` declaration. Stdlib modules listed
below do not use `indexed type`, so their dependent-type claims are handled by
the legacy checker, runtime conventions, documentation, or not at all.

## Fixed Claims

### `Std.Vector`

Source: `lib/std/vector.cure`

`Std.Vector` has been migrated from the old tuple-backed API to a real indexed
family checked by the dependent kernel:

```cure
indexed type Vector(a: Type, n: Nat) where
  empty : Vector(a, Z)
  prepend : a -> Vector(a, n) -> Vector(a, S(n))
```

The current trusted API includes:

- `empty() -> Vector(a, Z)`
- `prepend(x: a, xs: Vector(a, n)) -> Vector(a, S(n))`
- `append({a: Type}, {m: Nat}, {n: Nat}, xs: Vector(a, m), ys: Vector(a, n)) -> Vector(a, plus(m, n))`

The erased runtime representation is the constructor shape `:empty` and
`{:prepend, head, tail}`; the `a`, `m`, and `n` arguments are compile-time-only.
`Nat` is defined separately in `lib/std/nat.cure`.

## Incorrect Or Unsupported Claims

### `Std.Equal`

Source: `lib/std/equal.cure`

`Std.Equal` used to document `Eq(T, a, b)` proofs, erased equality values, and
rewrite behavior. The exported functions return plain `Atom`:

- `refl(_x: T) -> Atom`
- `sym(_eq: Atom) -> Atom`
- `trans(_p: Atom, _q: Atom) -> Atom`
- `cong(_f: T -> U, _eq: Atom) -> Atom`

The stdlib comments now mark this as a legacy equality-token API. The runtime
value is always `:cure_refl`, and there is no per-call kernel proof validation
in this module.

### `Std.Proof`

Source: `lib/std/proof.cure`

`Std.Proof` contains law-shaped definitions returning `Eq(...)`-looking types.
The legacy checker only enforces a proof-shaped return type for proof
containers. It does not validate the stated proposition in the trusted kernel.

The legacy type representation also accepts any atom as an inhabitant of
`Eq(...)` so proof functions can return `:cure_refl` directly. That makes these
functions proof-shaped, but not proof-checked in the sense required by a
trusted dependent kernel.

Examples:

- `plus_zero(_n: Int) -> Eq(Int, n, n)`
- `zero_plus(_n: Int) -> Eq(Int, n, n)`
- `plus_comm(_a: Int, _b: Int) -> Eq(Int, a, a)`
- `append_nil(_xs: List(T)) -> Eq(List(T), xs, xs)`
- `map_id(_xs: List(T)) -> Eq(List(T), xs, xs)`

Several of these types are also weaker than their comments suggest: for
example, `plus_comm` is documented as commutativity but states `Eq(Int, a, a)`.

### `Std.CRDT`

Source: `lib/std/crdt.cure`

`Std.CRDT` used to claim that CRDT merge laws were asserted in companion
`Std.Proof` obligations emitted by `lib/std/crdt.cure` when re-checked. The
source comment now says the runtime implementation is intended to satisfy those
laws, but no trusted Core proof obligations are emitted yet.

## Borderline: Real Refinements, Not Kernel Dependent Types

### Refinement types (removed)

Formerly `lib/std/refine.cure`.

The refinement-type aliases (`NonZero`, `Positive`, `Percentage`,
`Probability`, ...) and the legacy SMT-backed refinement checker have been
removed, pending SMTCoq-style proof reconstruction. They were never
trusted-kernel dependent types; this entry is kept only to record that the
feature and its stdlib module are gone.

## Routing Implication

The dependent-kernel handoff now routes the supported surface through Core:
indexed types, typed erased parameters, `Sigma(...)`, pair literals, and pair
projections. It still does not route public `Eq(...)`/`refl`/`rewrite` or proof
containers as trusted proofs, because that Cure source elaboration is not
implemented yet.
