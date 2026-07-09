# Cure Dependent Types Guide

This page describes the dependent features that are backed by the current
trusted Core kernel. Older modules under `Cure.Types.*` still exist as
compatibility APIs, but a Cure source feature should only be described as
trusted dependent typing when it elaborates to `Cure.Core`, is checked by
`Cure.Core.Kernel`, and is erased/emitted from that checked Core term.

## Trusted Surface Today

The dependent compiler path currently handles:

- indexed families declared with `indexed type ... where`;
- typed erased parameters such as `{a: Type}` and `{n: Nat}`;
- dependent global calls whose erased arguments are inferred at call sites;
- `Sigma(x: A, B)` dependent pairs, pair literals `%[a, b]`, and projections
  `p.1` / `p.2`;
- holes inside dependent programs, which typecheck but block codegen;
- type-level reduction through Core normalization, exposed to legacy callers by
  `Cure.Types.Reduce`.

The compiler routes modules using indexed types, typed erased parameters, or
Sigma/projection surface forms through the dependent compiler even if they do
not also declare an indexed family.

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

`Cure.Types.Reduce` is now a compatibility facade over Core normalization.
Before normalization it substitutes requested source-level bindings, then
translates the supported expression fragment to Core, evaluates with
normalization-by-evaluation, and reads the result back. Arithmetic, Boolean
operations, comparisons, and literal tuple projection are covered by this bridge;
irreducible source syntax is kept structurally and its children are normalized.

## Holes

`?name` holes are real in dependent programs. The kernel accepts a hole at the
declared goal type so tooling can report the goal and local context, but codegen
rejects any definition that still contains a hole.

## Not Trusted Kernel Surface Yet

The following pieces remain compatibility or design surface, not completed
trusted Cure dependent typing:

- Public `Eq(T, a, b)`, `refl`, and `rewrite` syntax is not fully elaborated
  from Cure source to Core yet. Core has equality/rewrite nodes and kernel tests,
  but `Std.Equal` still returns runtime `Atom` witnesses.
- `proof` containers are currently a legacy proof-shape gate. They require
  proof-looking return types, but they do not validate the proposition in the
  trusted Core kernel.
- `Cure.Types.Pi`, `Cure.Types.Sigma`, `Cure.Types.Equality`, and
  `Cure.Types.Holes` are compatibility helpers unless the source program
  also routes through `Cure.Elab.Program`.

The next dependency work should turn the unsupported items above into either
Core-backed user features or explicit compile-time rejections.
