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

`Std.Equal` documents `Eq(T, a, b)` proofs, erased equality values, and rewrite
behavior. The exported functions return plain `Atom`:

- `refl(_x: T) -> Atom`
- `sym(_eq: Atom) -> Atom`
- `trans(_p: Atom, _q: Atom) -> Atom`
- `cong(_f: T -> U, _eq: Atom) -> Atom`

The docs describe a propositional equality API, but the stdlib function
signatures do not expose those `Eq(...)` types. The runtime value is always
`:cure_refl`, and there is no per-call kernel proof validation in this module.

### `Std.Proof`

Source: `lib/std/proof.cure`

`Std.Proof` claims laws-as-programs whose definitions return `Eq(...)`
witnesses. The legacy checker only enforces a proof-shaped return type for
proof containers. It does not validate the stated proposition in the trusted
kernel.

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

`Std.CRDT` claims that CRDT merge laws are asserted in companion `Std.Proof`
obligations emitted by `lib/std/crdt.cure` when re-checked. No such companion
obligations were found in `Std.Proof`, and because `Std.Proof` itself is only
proof-shaped under the legacy checker, this claim is not currently backed by
trusted kernel proof checking.

## Borderline: Real Refinements, Not Kernel Dependent Types

### `Std.Refine`

Source: `lib/std/refine.cure`

`Std.Refine` provides real refinement aliases such as:

- `NonZero = {x: Int | x != 0}`
- `Positive = {x: Int | x > 0}`
- `Percentage = {p: Int | p >= 0 and p <= 100}`
- `Probability = {p: Float | p >= 0.0 and p <= 1.0}`

These are legitimate as SMT-backed refinement types in the legacy checker.
They should not be described as trusted-kernel dependent types unless and until
the dependent kernel owns refinement checking or the documentation clearly
distinguishes the two systems.

## Routing Implication

The dependent-kernel handoff currently keys on `indexed type`. That means
`Eq(...)`, `Sigma(...)`, `Pi(...)`, proof containers, and refinement aliases can
appear in non-indexed modules without automatically entering the trusted
dependent pipeline.

Until that boundary changes, stdlib documentation should avoid implying that
these modules are validated by the trusted kernel.
