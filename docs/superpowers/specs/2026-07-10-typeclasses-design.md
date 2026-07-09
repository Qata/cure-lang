# Compile-time Typeclasses — Design

**Status:** design approved (operator, 2026-07-10). Scope: migrate ALL existing
proto/impl modules. This document is the source of truth for the elaboration
strategy; the surface was locked in prior decisions (see Non-Goals §9).

**Task:** #21 (K). Prerequisite that unblocks char-literal patterns (#25),
string-literal patterns (#27), and `Std.String` (#29), all of which want value
equality through the resulting `Equatable` interface.

---

## 1. Goal

Replace Cure's **runtime `proto`/`impl` protocol dispatch** with **compile-time
typeclasses** elaborated entirely in the dependent pipeline (`lib/cure/elab/*` +
`lib/cure/core/*`). Interfaces become Core record types, implementations become
dictionary values, and instance selection is resolved by the elaborator at
compile time — statically inlined at concrete call sites, threaded as an implicit
dictionary parameter through polymorphic code. The polymorphic structural
equality primitive `struct_eq`/`struct_ne` is retired in favour of a real
`Equatable` interface.

**Success criterion:** every existing stdlib `proto`/`impl` module (`Equatable`,
`Ord`, `Show`, `Functor`, `Access`, `Equivalent`, `JSON`) is rewritten to
`interface`/`implementation`, elaborates through the dependent pipeline, and its
methods resolve and run correctly; `struct_eq` and the 4-way `==` dispatch are
gone; the full suite is green.

## 2. Locked surface (restated, not re-litigated)

From prior operator decisions (memory `typeclass-surface-decisions`):

- Keywords **`interface`** / **`implementation`** (Idris2 pairing),
  indentation-based blocks, **no `end`** terminator.
- **Coherence = global uniqueness + named implementations.** At most one
  anonymous instance per `(interface, head type)` globally; additional instances
  must be *named* and are selected explicitly.
- **Deriving approved**, decl-attached clause is the default form
  (`type Color = R | G | B deriving Equatable`), plus a standalone
  `derive Equatable for Color` form.

This design does NOT revisit keyword choice, block syntax, or the coherence
policy. It settles only *how these lower into Core*.

## 3. Elaboration strategy (the core of this design)

### 3.1 Interfaces are Core record types

`interface Equatable(a)` with methods `eq`, `ne` elaborates to a **dependent
record type** (the same Core machinery as `Std.Pair`/dependent records, memory
`dependent-records-finding`), parameterised by the interface variable(s):

```
Equatable : Π(a : Type). Type
Equatable(a) ≙ record { eq : a → a → Bool, ne : a → a → Bool }
```

- The interface head variable `a` has kind `Type` in every existing stdlib
  interface — including `Functor(g)`, whose surface treats `g : Type` with free
  element variables in the method signature (`fmap(container: g, f: a→b) → g`).
  **v1 therefore does NOT require true higher-kinded (`Type → Type`) heads.**
  The design keeps interface heads at kind `Type`, matching the current surface
  exactly. (True HKT is a documented later extension, §8.)
- Method signatures with free type variables beyond the interface head (e.g.
  `fmap`'s `a`, `b`) are elaborated as **implicit-generalised** method fields:
  the record field type is a Π over those extra variables. This is ordinary
  auto-generalisation, already supported by the elaborator.
- A method whose body is defined in the interface (a *default method*, e.g.
  `Equatable`'s `ne` derived from `eq`) is stored as a **default** used when an
  implementation omits it (§3.3).

### 3.2 Implementations are dictionary values

`implementation Equatable for Int` elaborates to a **record value** (dictionary)
of type `Equatable(Int)`:

```
equatable_Int : Equatable(Int) ≙ record { eq = int_eq, ne = <default ne applied to int_eq> }
```

- The dictionary is registered in a new **coherence table** (§3.4), keyed by
  `(interface_id, head_type_id)` = `(Equatable, Int)`.
- Each method field takes its body from the implementation's method clause;
  omitted methods fall back to the interface's default method (§3.1), specialised
  to this instance.
- A **named** implementation (`implementation Equatable for Int as strictInt`)
  is registered under its name, NOT in the anonymous coherence slot, and never
  participates in automatic resolution — it is referenced explicitly.

### 3.3 Default methods

An interface may supply a default body for a method (`Equatable.ne` is
`pickup eq(a,b) -> false else -> true`). When an implementation omits that
method, the dictionary field is filled by the default body **closed over the
instance's other methods** (so the default `ne` calls *this* instance's `eq`).
Implementations may override the default by providing their own clause.

### 3.4 Coherence table + resolution

A new elaborator-scoped registry: `interface_id → head_type_id → dictionary_ref`
(anonymous instances) plus `name → dictionary_ref` (named instances). It lives
alongside the existing `Inductive`/builtin registries in the signature/env so it
survives across module boundaries (imports contribute their instances).

**Global uniqueness:** registering a second anonymous instance for an existing
`(interface, head type)` is a hard error `{:overlapping_instance, iface, head}`.
An anonymous instance whose head type is defined in *another* module than both
the interface and the instance is an `{:orphan_instance, …}` error (Rust/Haskell
orphan rule; enforced at registration).

**Resolution** at a method-call site `m(args...)` where `m` is an interface
method:
1. Infer the type `T` of the method's interface-head argument position (for
   `eq(x,y)` that is the type of `x`).
2. **Concrete head** (`T`'s head is a known type constructor with a registered
   anonymous instance): resolve to that dictionary and **project + inline the
   method statically** — `eq(x,y)` on `Int` becomes exactly `int_eq(x,y)`, with
   **no dictionary value at runtime**. This is the generalisation of today's
   type-directed `==` dispatch.
3. **Abstract head** (`T` is a rigid type variable `a` in scope under a
   constraint `{Equatable a}`): the constraint introduced an **implicit
   dictionary parameter** `dict_Equatable_a : Equatable(a)`; the method call
   **projects from that parameter** — `eq(x,y)` becomes `dict.eq x y`.
4. **No instance found** and no constraint in scope: hard error
   `{:no_instance, iface, T}`.

### 3.5 Constraints as implicit dictionary parameters

A constrained signature `fn f{a: Type}(… ){Equatable a} -> …` (surface form per
locked syntax) introduces, at elaboration, an **implicit parameter**
`{dict : Equatable(a)}` immediately after the type parameter `a`. Its quantity is
**ω-present iff a method is actually invoked** in the body — Cure's {0,ω}
erasure discipline (memory `erasure-relevance-check-decision`) computes this for
free: if the body never calls an `Equatable` method on `a`, the dictionary is
erased. Calls to constrained functions pass the resolved dictionary implicitly
(resolution §3.4 applied at the call's concrete type argument).

### 3.6 Deriving

`deriving Equatable` (decl-attached) or `derive Equatable for T` (standalone)
generates an `implementation Equatable for T` whose method is a **structural
recursive equality**:

- For each constructor pair, `eq` matches both scrutinees; equal constructors
  compare fields pairwise via **each field's own `Equatable`** (recursively
  resolved — enabling `deriving` on recursive/nested types); different
  constructors give `false`.
- First-order data (no function-typed fields) MAY emit to BEAM `==` as an
  optimisation, but the *semantics* are the generated structural eq (this is the
  law-abiding replacement for `struct_eq`'s "compare erased representations").
- `deriving Ord` / `deriving Show` are generated analogously (lexicographic
  constructor-then-field order for `Ord`; constructor-name + field rendering for
  `Show`). Deriving is available for all three of `Equatable`, `Ord`, `Show`.

## 4. The `==`/`struct_eq` reconciliation

### 4.1 Torn out

- `struct_eq`/`struct_ne` builtin-op globals: `builtins.ex` `@struct_ops` and
  their body-less-def seeding; `normalise.ex` `builtin_op_fold` struct_eq/ne
  arm; `emit.ex` `lower_builtin_op` + `builtin_op_wrapper` struct_eq/ne arms;
  `guard_lint.ex` struct_eq/ne handling.
- The 4-way `==`/`!=` dispatch in `elaborator.ex` `build_binop`
  (`:bool→eq`, `:int→int_eq`, `:float→float_eq`, `:error→struct_eq`): the
  `:error` (structural) arm is **deleted**. `==`/`!=` on ANY type now resolve via
  `Equatable`/coherence (§3.4). The primitive arms are subsumed: on `Int`,
  resolution finds `equatable_Int` and inlines `int_eq` — same emitted code as
  today, reached through the interface instead of a hardcoded switch.

### 4.2 Repointed (kept)

`int_eq`, `float_eq`, `eq` (Bool), string equality, atom equality stay as
builtin-op globals and become the **method bodies of the primitive `Equatable`
implementations**. **Circularity fix (found during design):** the current
`impl Equatable for Int` body is literally `a == b`; once `==` *is* `Equatable.eq`
that is infinite regress. The migrated primitive implementations must therefore
reference the **primitive builtin-op directly** (`int_eq(a,b)`, not `a == b`).
This is the one non-mechanical rewrite in the stdlib migration.

### 4.3 `Ord` comparison operators

`<`, `<=`, `>`, `>=` currently dispatch to `int_*`/`float_*` in `build_binop`.
These are similarly re-expressed as `Ord` method resolution, with the primitive
`int_lt`/… repointed as the primitive `Ord` implementations' method bodies.
Non-`Ord` operand types now error via `{:no_instance, Ord, T}` instead of the
current `{:unsupported_operand_type, _}`.

## 5. Migration of the 7 stdlib modules

Rewrite each from `proto`/`impl` to `interface`/`implementation`:

1. **Equatable** — primitive impls reference builtin-ops directly (§4.2);
   `ne` default method.
2. **Ord** — repoint `int_*`/`float_*` comparisons (§4.3).
3. **Show** — `show : a → String`; primitive impls; deriving.
4. **Functor** — `fmap`; head at kind `Type` (§3.1); `List` impl delegates to
   `Std.List.map`.
5. **Access**, **Equivalent**, **JSON** — mechanical surface rewrite; verify
   resolution.

Each migrated module must elaborate through the **dependent** pipeline cleanly.
Where a module is not yet dependent-clean (memory `value-surface-parity-program`
notes most stdlib still leans on classic Codegen), making its interface/impl
elaborate is in scope; making unrelated value code dependent-clean is NOT — if a
module cannot elaborate for reasons unrelated to typeclasses, that is a
documented blocker, not silently worked around.

**Old `proto`/`impl` keywords:** left in the lexer/parser as now-unreachable
classic-pipeline surface (their removal belongs to #18, the classic-pathway
rip-out). No stdlib module uses them after migration.

## 6. Testing strategy

Strict red-green TDD throughout. Behavioural tests (elaborate real `.cure`
source, assert Core shape and/or run the emitted BEAM), not implementation-
coupled. Coverage:

- **Parse:** `interface`/`implementation` (anonymous + named + deriving) produce
  the expected AST nodes; a red parser test first.
- **Interface → record type:** elaborating an interface registers a record type
  of the right field shape.
- **Implementation → dictionary:** registers a dictionary; duplicate anonymous
  instance ⇒ `{:overlapping_instance}`; orphan ⇒ `{:orphan_instance}`.
- **Concrete resolution:** `eq(1,2)` elaborates to the inlined `int_eq` spine
  (no dictionary), runs to `false`.
- **Abstract resolution:** a constrained polymorphic `fn` projects the method
  from its implicit dictionary parameter; runs correctly for two different
  instances.
- **Erasure:** a constrained `fn` that never calls a method erases the
  dictionary (quantity 0); one that does keeps it (quantity ω).
- **Default method:** an implementation omitting `ne` gets the default closed
  over its `eq`.
- **Deriving:** `deriving Equatable`/`Ord`/`Show` on a recursive ADT generates a
  working structural instance; a nested/recursive value compares/renders
  correctly.
- **`==` retirement:** `struct_eq`/`struct_ne` no longer seeded (assert absent);
  `==` on an ADT with a derived instance works; `==` on a type with NO instance
  is `{:no_instance, …}` (behavioural change from struct_eq's accept-anything).
- **End-to-end:** each migrated stdlib module compiles + its methods run.
- **Differential oracle (cure-porting):** a `typeclass` oracle cluster with
  paired `.cure`/`.idr` interface/implementation programs, verifying Cure's
  acceptance/rejection matches Idris2 for resolution, coherence, and deriving.

## 7. Risks

- **Blast radius of `==` retirement.** Every `==`/`!=` in the codebase and tests
  currently relying on struct_eq's accept-anything behaviour may change verdict
  (a no-instance type now errors). Mitigation: primitive types keep identical
  emitted code; ADTs used with `==` in tests get derived instances; run the full
  suite and triage each newly-failing `==` site (real regression vs. a type that
  legitimately now needs a derived instance).
- **Resolution non-termination.** Recursive deriving (`eq` on a recursive type
  calling `eq` on its own sub-values) must resolve to the *same* instance, not
  loop in the resolver. Mitigation: resolution memoises `(interface, head)` and
  the generated recursive method refers to itself by name.
- **Stdlib not dependent-clean.** Some of the 7 modules may not elaborate
  through the dependent pipeline for unrelated reasons. Mitigation: §5's blocker
  rule — surface it, do not paper over it. If a module is blocked, its migration
  is deferred with a written reason and the run continues with the rest.
- **Import-order / global coherence coupling** (flagged at `program.ex:224`).
  The coherence table must aggregate instances across imported modules
  deterministically. Mitigation: instances registered at elaboration in import
  order; overlap check is order-independent (any two anonymous instances for the
  same key collide regardless of order).
- **TCB surface.** Dictionaries reuse existing dependent-record Core; no new
  kernel node is anticipated. If resolution/erasure turns out to need a kernel
  change, that is a HARD-STOP-and-review per the porting charter, gated by the
  full Antigen + test suite (memory `tcb-change-blanket-approval` pre-approves
  Agda/Lean-aligned kernel changes but still requires the full gate).

## 8. Later extensions (explicitly out of scope for v1)

- True higher-kinded interface heads (`Functor(f)` with `f : Type → Type`),
  superclass/interface inheritance, multi-parameter interfaces, functional
  dependencies, and monomorphising specialisation (v1 threads runtime
  dictionaries at abstract sites; specialisation is a perf optimisation later).

## 9. Non-goals

- Re-litigating the locked surface (§2).
- Removing the classic `proto`/`impl` parser/runtime (that is #18).
- Making unrelated stdlib value code dependent-clean (only interface/impl
  elaboration is in scope).
- SMT/refinement interactions (refinements are removed, memory
  `smt-trust-boundary-decision`).
