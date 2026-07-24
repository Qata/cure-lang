# Cure Type System

## Overview

Cure has a bidirectional type system with support for:

- Primitive types and composite types
- Algebraic data types (ADTs / sum types)
- Refinement types with SMT-backed verification
- Protocol-based ad-hoc polymorphism
- Pattern exhaustiveness checking

## Bidirectional Type Checking

The type checker operates in two modes:

- **Infer mode**: determines the type of an expression from its structure
- **Check mode**: verifies an expression has an expected type

Functions are checked in two passes:
1. Collect all function signatures (name, parameter types, return type)
2. Check each function body against its declared return type

## Primitive Types

- `Int` -- arbitrary-precision integers
- `Float` -- IEEE 754 floating point
- `String` -- UTF-8 binary strings
- `Bool` -- `true` or `false`
- `Atom` -- Erlang atoms (`:ok`, `:error`)
- `Char` -- single Unicode character
- `Unit` -- no meaningful value (`nil`)
- `Pid` -- BEAM process identifier; bare `Pid` elaborates to
  `{:pid, :any}` (v0.25.0)
- `Pid(Inbox)` -- typed pid where `Inbox` is the ADT the receiving
  process accepts (v0.25.0)
- `Ref` -- monitor reference returned by `Std.Process.monitor/1`
  (v0.25.0)

## Composite Types

- `List(T)` -- homogeneous linked list
- `Map(K, V)` -- map from `K` to `V`
- `%[A, B, ...]` -- tuple type, mirroring the value syntax `%[a, b, ...]`
- `A -> B`, `(A, B) -> C` -- function types

The canonical tuple-type spelling is `%[A, B]`. Legacy `(A, B)` remains
accepted and compiles to the identical dependent tuple and flat BEAM value, but
emits the explainable `E086 / E-TYPE-TUPLE-PAREN` deprecation. This does not
affect grouped `(A)` or the parameter list in `(A, B) -> C`.

## Subtyping

- `Int <: Float` (numeric widening)
- `Never <: T` for all T (bottom type)
- `T <: Any` for all T (top type)
- `{x: Int | P(x)} <: Int` (refinement drops constraint)
- `List(A) <: List(B)` if `A <: B` (covariant)
- `(A -> B) <: (C -> D)` if `C <: A` and `B <: D` (contravariant params)
- `Pid(A) <: Pid(B)` if `A <: B` (covariant in the inbox, v0.25.0).
  In particular, any `Pid(Inbox)` is a subtype of the top `Pid` alias
  (elaborated as `Pid(:any)`), so untyped APIs remain assignable from
  narrower typed pids without friction.

## Refinement Types

Refinement types constrain a base type with a logical predicate:

```cure
type NonZero = {x: Int | x != 0}
type Positive = {x: Int | x > 0}
type Percentage = {p: Int | p >= 0 and p <= 100}
```

### Subtype Verification

Refinement subtyping is verified at compile time using Z3:

- `Positive <: NonZero` because `forall x. x > 0 => x != 0` (proven by Z3)
- `Percentage <: NonNegative` because `forall p. (p >= 0 and p <= 100) => p >= 0`
- `NonZero` is NOT `<: Positive` (counterexample: x = -1)

### Satisfiability

The compiler verifies refinement types are not empty:

- `{x: Int | x > 0}` is satisfiable (x = 1 works)
- `{x: Int | x > 0 and x < 0}` is unsatisfiable (warning)

## Pattern Exhaustiveness

The type checker analyzes match expressions for completeness:

- `Bool`: requires `true` and `false`
- `Result(T, E)`: requires `Ok(...)` and `Error(...)`
- `Option(T)`: requires `Some(...)` and `None()`
- `List(T)`: requires `[]` and `[_ | _]`
- Infinite types (`Int`, `String`): require a wildcard `_`

Non-exhaustive matches produce compile-time warnings.

## Guard-Based Type Refinement

When a function has a guard, parameter types are refined within the body:

```cure
fn process(x: Int) -> Int when x > 0 =
  # Inside this body, x has type {x: Int | x > 0}
  x * 2
```

For multi-clause functions, the type checker uses SMT to verify
guard coverage and detect unreachable clauses.

## Record types

Records introduce named product types. The type checker represents them as
`{:named, "TypeName"}` -- a lightweight reference that carries the original
name without erasing it to `Any`.

### Schema registration

The checker's first pass (`collect_signatures`) registers each `rec` definition
in `Env.types`:

```
"Point" -> {:record, :point, %{"x" => :int, "y" => :int}}
"Person" -> {:record, :person, %{"name" => :string, "age" => :int}}
```

This schema is available during the second pass so that field accesses and
record updates can be type-checked against the declared field types.

### Typing rules

- **Construction** -- `Point{x: 3, y: 4}` has type `{:named, "Point"}`.
- **Field access** -- `p.x` where `p : {:named, "Point"}` has type `:int`
  (looked up from the registered schema). Field access on `Any` produces `Any`.
- **Record update** -- `Point{p | x: new_x}` where `p : {:named, "Point"}`
  type-checks each override value against the declared field type and returns
  `{:named, "Point"}`.
- **Parameters** -- `fn f(p: Point)` resolves `Point` to `{:named, "Point"}`,
  making `p` available with full field-type information in the body.

### Subtyping for named types

`{:named, Name}` participates in the subtype hierarchy:

- `{:named, T} <: Any` for all T (inherited from the universal rule)
- `{:named, "Pair"} <: {:adt, :pair, _params}` when
  `String.downcase("Pair") == "pair"` -- named types satisfy their
  corresponding parameterized ADT return type (e.g. `fn f() -> Pair(A, B)`
  is satisfied by a body of type `{:named, "Pair"}`)
- `{:named, T} <: {:named, T}` (reflexivity, from `subtype?(t, t)`)

## Protocols

Protocols provide ad-hoc polymorphism. The type checker:

1. Registers protocol method signatures during the first pass
2. Validates implementation method signatures match the protocol
3. Checks implementation bodies against declared types

## Typed Sends (v0.25.0)

`Cure.Elab.Elaborator` handles `{:send, meta, [target, message]}` nodes
emitted by the Melquiades Operator `<-|` (and the keyword form
`send target, msg`) in the dependent pipeline:

1. Infer the target's type. If it is `{:pid, inbox}`, unify the
   message type against `inbox`.
2. Emit `E046 Inbox Mismatch` with a concrete diagnostic when the
   unification fails.
3. Return the message's type as the expression's type, so
   `let reply = pid <-| msg` binds `reply` to the value that was sent.

Bare `Pid` elaborates to `{:pid, :any}`; sends against it never fail
type-checking but attract `E045 Untyped Send` under strict mode.
Effect inference attracts the `:state` effect for every send.

## Sigma, Pi, equality, holes, totality (v0.17.0)

See `DEPENDENT_TYPES.md` for the full guide. Brief summary:

- **Sigma types** -- `{:sigma, var, fst_type, snd_ast}` -- dependent
  pairs where the second component's type may reference the first
  component's value. Surface syntax: `Sigma(name: T1, T2)`.
- **Pi types** -- `{:pi, [{name, type, mode}], ret_ast}` -- dependent
  function types. Return types may reference parameter names; the
  checker substitutes and normalises at every call site.
- **Equality types** -- Core has `{:eq, T, a, b}`, `refl`, and
  `rewrite` support, but the public Cure source surface is not fully
  wired through the trusted dependent compiler yet. `Std.Equal`
  remains a runtime-token compatibility API.
- **Holes** -- `?name` and `??` placeholders. The checker emits a
  `:hole_goal` event with the goal type and local context.
- **Totality** -- `Cure.Elab.TotalityClosure` validates the reachable
  definition closure before trusted certification. The `@total true`
  decorator makes that requirement explicit at the declaration.
- **Type-level reduction** -- `Cure.Core.Normalise` evaluates dependent Core
  terms for definitional equality.
- **Unification** -- `Cure.Elab.Unify` solves implicit metavariables with an
  occurs check and preserves source context for failures.
- **Branch refinement** -- dependent pattern elaboration refines indices and
  local types independently in each checked branch.
