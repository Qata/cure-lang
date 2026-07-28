# Proofs in Cure

Proofs are ordinary Cure values checked by the dependent kernel. There is no
runtime equality token and no separate legacy checker: a declaration proving a
proposition elaborates to checked Core, and proof-only values are erased before
BEAM emission.

## Propositional equality

`Std.Equivalent` defines the kernel-recognised identity family:

```cure
@builtin(:eq)
type Equivalent(a: Type) indices (x: a, y: a)
  reflexive : Equivalent(a, w, w)
```

An inhabitant of `Equivalent(a, x, y)` is evidence that `x` and `y` are the
same value. This differs from `Std.Equatable`: `x == y` computes a runtime
`Bool`, while `Equivalent(a, x, y)` is a proposition checked at compile time.

`reflexive` closes a goal whose endpoints are definitionally equal. Matching on
an equality proof identifies the endpoints, so transport and the usual laws
are written without a primitive `rewrite` node:

```cure
use Std.Equivalent

fn symmetric(
  {a: Type},
  {x: a},
  {y: a},
  proof: Equivalent(a, x, y)
) -> Equivalent(a, y, x) =
  match proof
    reflexive -> reflexive
```

`Std.Equivalent` supplies `sym`, `trans`, and `cong` using this same
single-constructor elimination.

## Indexed propositions

Any indexed family can be a proposition. Its constructors are the valid proof
rules:

```cure
type IsEven indices (n: Nat)
  even_zero : IsEven(Z)
  even_step : IsEven(n) -> IsEven(S(S(n)))
```

A function returning `IsEven(n)` must construct evidence for that exact index.
Impossible branches can be marked `impossible` when constructor-index
unification proves that no value can reach them.

## Proof authoring surface

- `have name = expression` introduces a checked local fact.
- `proof chain` gives equality composition a readable surface.
- `because` blocks provide directed rewrites, simplification, and induction
  commands that elaborate to ordinary proof terms.
- `?name` and `??` create typed holes and report the goal plus local context.
- Generated defining equations are theorem members available to completion and
  hover.

These commands are elaboration syntax. They do not add unchecked Core nodes and
do not survive erasure.

## Trust

`postulate`, bodyless `@extern`, and `believe_me` are explicit trust roots. The
compiler records their canonical identities and dependency reachability:

```bash
cure audit trust My.Module
```

The report distinguishes a theorem proved from definitions from one that
depends on an axiom. SMT guard coverage is linting outside the trusted kernel;
it can warn about coverage or shadowing but does not manufacture proof
evidence.

## Standard proof modules

- `Std.Equivalent` — identity, symmetry, transitivity, and congruence.
- `Std.Proof` — structural equality laws over `Std.Nat`.
- `Std.Proof.Math` — positive-natural and ordering evidence.
- `Std.Decision` — decidable propositions carrying either evidence or a
  refutation.
- `Std.Proof.LinearArithmetic` — checked linear-arithmetic reflection and its
  semantics.

See [Dependent Types](DEPENDENT_TYPES.md) for indexed programming and
[Kernel](KERNEL.md) for conversion, totality certificates, and the trusted
boundary.
