# Cure Dependent Types Guide

This page describes the dependent features backed by the current trusted Core
kernel. All accepted Cure source follows this path: it elaborates to
`Cure.Core`, is checked by `Cure.Core.Kernel`, and is erased/emitted from that
checked Core term. The former `Cure.Types.*` pipeline has been removed.

## Trusted Surface Today

The dependent compiler path currently handles:

- indexed families declared with `indexed type ... where`;
- typed erased parameters such as `{a: Type}` and `{n: Nat}`;
- dependent global calls whose erased arguments are inferred at call sites;
- `Sigma(x: A, B)` dependent pairs, pair literals `%[a, b]`, and projections
  `p.1` / `p.2`;
- holes inside dependent programs, which typecheck but block codegen;
- type-level reduction through `Cure.Core.Normalise`.

## Indexed Families

Indexed families let data carry type indices checked by the kernel:

```cure
type Nat = Z | S(Nat)

indexed type Vector(a: Type, n: Nat) where
  empty : Vector(a, Z)
  prepend : a -> Vector(a, n) -> Vector(a, S(n))
```

The constructor index arguments are erased. Runtime `Vector` values are ordinary
constructors, while the Core checker verifies the length index.

## Typed Erased Parameters

Braced parameters are implicit and erased when they have explicit types:

```cure
fn id_nat({n: Nat}, x: Nat) -> Nat = x
```

The source function has two parameters, but the emitted BEAM function has arity
one. Untyped `{T}` syntax still parses for compatibility, but the trusted
dependent path currently requires explicit parameter types such as `{T: Type}`.

## Sigma Types

Sigma types pair a value with a type that may depend on that value:

```cure
fn pack(d: Dec) -> Sigma(x: Dec, Dec) = %[d, d]
fn recover(p: Sigma(x: Dec, Dec)) -> Dec = p.2
```

`Sigma(x: A, B)` elaborates to Core `Σ`; `%[a, b]` elaborates to pair
introduction, and `p.1` / `p.2` elaborate to projections. Runtime pairs emit as
2-tuples.

## Type-Level Reduction

Type-level computation is represented directly in Core and evaluated by
normalization-by-evaluation. Arithmetic, Boolean operations, comparisons, and
projections therefore participate in definitional equality without a separate
surface-AST reduction bridge.

## Holes

`?name` holes are real in dependent programs. The kernel accepts a hole at the
declared goal type so tooling can report the goal and local context, but codegen
rejects any definition that still contains a hole.
