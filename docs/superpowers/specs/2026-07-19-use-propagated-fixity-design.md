# `use`-Propagated Fixity Design

**Goal:** Make operator fixity (precedence groups + `infix`/`prefix`/`postfix`
declarations) propagate through `use`, uniformly for user modules and the
stdlib, with `@prelude` as the mechanism that makes the core operators ambient.

**Architecture:** A module's parse-time fixity table is the union of its own
fixity declarations, the fixity of every module in its transitive `use`-closure,
and the fixity of every `@prelude` provider. Extraction of a module's own
declarations is *table-independent*, so no dependency-ordered parsing is
required — only `use`-graph reachability (already computed by `DepGraph`) plus a
cheap per-module scanner. Operator *protection* stops being a privileged
built-in list and becomes a single invariant: within any one module's assembled
table, each operator lexeme has at most one fixity.

**Tech stack:** Elixir; `Cure.Compiler.Parser` and friends. All changes live in
the compiler/parser and elaboration layers — **`lib/cure/core/**` (the TCB) is
untouched.**

## Global Constraints

- Zero TCB change. Nothing under `lib/cure/core/**` is modified.
- Fixity is a *syntactic* property, resolved at parse time. It must not depend
  on elaboration, type-checking, or name resolution.
- Fixity extraction for a module must never fail because that module's function
  bodies fail to parse — declarations are inert and extracted independently.
- Overloading (multiple `fn <op>` definitions) is orthogonal to fixity and never
  produces a fixity conflict.
- Full gate (`mix test`) green before merge; commits authored as the user only,
  no co-sign trailer.

---

## Background: current state

- `BuiltinFixity.table()` is the memoized parse of `lib/std/operators.cure`
  only. It is the single ambient fixity table.
- The parser seeds each module's Pratt table from `BuiltinFixity.table()` and
  layers the module's *own* `infix`/`precedencegroup` decls on top via
  `BuiltinFixity.extend/2`. `use`d modules contribute **nothing** to fixity.
- Therefore an operator declared outside `operators.cure` is usable only inside
  its own defining module, and is invisible to any importer.
- `Program.check_no_builtin_rebind/1` rejects a user module that redeclares the
  fixity of any operator present in the built-in table, exempting
  `Std.Operators` itself. This is a location-based privileged-list rule.

## The unified model

For a module `M`:

```
fixity(M) = own(M)
          ∪ ⋃ { own(X) : X ∈ use_reach(M) }
          ∪ ⋃ { own(P) : P ∈ prelude_providers }
```

- `own(X)` — the fixity declarations textually present in module `X`.
- `use_reach(M)` — every module reachable from `M` over `use` edges
  (transitive; cycles included).
- `prelude_providers` — modules carrying `@prelude` (already identified by
  `DepGraph`). Marking `Std.Operators` `@prelude` places the core operators into
  every module's table by this clause — the same clause a user's `use Foo`
  triggers. There is no separate "built-in" path.

Both precedence groups and operator declarations are ordinary nodes in each
module's AST, so groups travel with the operators that reference them; no
separate group-propagation logic is needed.

## Key enabler: fixity extraction is table-independent

`infix`/`prefix`/`postfix`/`precedencegroup` are inert declaration syntax whose
parse does **not** consult the fixity table. Extracting `own(X)` therefore needs
neither a seeded table nor a successful parse of `X`'s function bodies. This
removes the hard problem (dependency-ordered two-phase parsing, bootstrap,
cycle handling for extraction): `own(X)` is a cheap, order-independent scan, and
`fixity(M)` is then just set-union over graph reachability.

## Components

### 1. Per-module fixity scanner — `own(X)`

A function that, given module `X`'s source (or tokens), returns its fixity
declaration nodes. It reuses the existing `parse_fixity` / precedence-group
productions but consumes only top-level fixity declarations and skips every
other top-level item; it seeds an empty table and cannot fail on function
bodies. Memoized per module (persistent-term, keyed by module name), like
`prelude_macros`. Source location reuses today's resolution: `Paths` for the
stdlib, `:cure_source_roots` / `user_source_path` for user modules.

### 2. `use`-closure fixity resolver — `fixity(M)`

Given `M`'s `use` list (from a header scan of `M`) and the `@prelude` provider
set, compute `use_reach(M)` via `DepGraph` reachability, then union `own/1` over
the reach plus prelude plus `own(M)`. Memoized per module. Cycles need no
special handling beyond reachability (union is idempotent).

### 3. Parser hook

When the parser begins module `M`:

1. **Header scan** `M`'s own `use` declarations (parse without a fixity table).
2. **Assemble** `fixity(M)` via the resolver.
3. **Body parse** the rest of `M` seeded with `fixity(M)`.

`BuiltinFixity` degenerates to "`fixity/1` applied to the prelude-provider set,"
providing the bootstrap table for the header/expression-free cases and for a
single-file parse with no surrounding source universe (see Edge cases).

### 4. `@prelude` on the operators module

Mark `Std.Operators` `@prelude` so it enters `prelude_providers`. This is the
change that keeps the core operators ambient under the new model — via the
general union, not a special case.

### 5. Conflict detection replaces `check_no_builtin_rebind`

While assembling `fixity(M)`, if two declarations bind the same lexeme (same
fixity slot — infix/prefix/postfix) to **different** groups, that is a hard
error naming the conflicting lexeme (and, where available, the contributing
modules). Consequences:

- A prelude operator sits in every table, so redeclaring `+`'s group always
  conflicts → rejected everywhere (recovers today's behavior with no list).
- Two `use`d modules declaring `<?>` with different precedence conflict *in the
  importer* → rejected there (Haskell's "conflicting fixity" semantics).
- An **identical** redeclaration (same group) is a silent no-op, not an error.
- `Std.Operators` declaring its own operators is not a conflict (sole source).

Error tag: keep `:builtin_operator_not_overloadable`? No — generalize to a new
tag `:conflicting_operator_fixity` carrying `{lexeme, group_a, group_b}`. The
existing `operator_flip_test` "rebinding a builtin syntactic operator is
rejected" is updated to expect the new tag (the prelude `|>` vs a user
`Additive` redeclaration is now a conflict).

## Overloading vs fixity (explicit)

Fixity attaches to the operator **symbol**, not to any typed overload. Defining
additional `fn <op>(...)` implementations of different types is overloading; it
carries no fixity declaration and can never conflict. All overloads of a symbol
share the single declared precedence. This matches both Haskell and Swift and is
why the conflict check keys on fixity *declarations* only, never on function
definitions.

## Decisions (locked)

1. **Transitivity** — full transitive `use`-closure. Over-approximating fixity
   is safe: extra entries only shape parse trees; an operator not semantically
   imported is still rejected at elaboration (`no_operator_meaning`).
2. **Cycles** — merged by union via reachability; no strict topo order needed.
3. **One fixity per lexeme** — different-group redeclaration is a hard error;
   identical redeclaration is a no-op; function overloads never conflict and
   share the precedence.

## Edge cases

- **Single-file parse, no source universe** (e.g. an isolated parser test):
  `use_reach` resolves only the modules whose sources are locatable; unresolved
  `use` targets contribute nothing (as today). The prelude providers and `own(M)`
  are always available, so core operators still bind. This preserves current
  single-file behavior.
- **Operator present, its group absent** (an imported operator whose group's
  module was not reached): the lexeme is unranked/incomparable, the existing
  `incomparable?` path applies. With transitive closure this should not arise
  for well-formed programs, but the parser degrades gracefully rather than
  crashing.
- **Prelude bootstrap**: `own(Std.Operators)` scans `operators.cure` with an
  empty table (all inert decls), exactly as `BuiltinFixity.compute` does today.

## Migration

- **Revert the half-built whole-stdlib scan.** The uncommitted plan to make
  `BuiltinFixity.table()` scan every `lib/std/*.cure` is wrong under this model
  (it would make stdlib operators ambient regardless of `use`) and is dropped.
  The already-committed augmented-assignment removal and `builtin`-keyword
  retirement stay.
- `FixityTable.declares?/2` (added in the retirement commit) is retained; the
  resolver and conflict check use it plus per-slot group lookups.
- `@prelude` is added to `lib/std/operators.cure`.

## Testing

- **Scanner**: `own/1` extracts fixity decls from a module whose function bodies
  reference not-yet-known operators without failing.
- **Propagation**: user module `A` declares `infix <?> : G`; module `B` that
  `use A` parses `x <?> y` with `<?>`'s precedence; a module that does **not**
  `use A` fails to parse `x <?> y` as an operator (or elaborates to
  `no_operator_meaning`, per how an unknown infix lexeme is handled).
- **Transitivity**: `A` declares, `B use A`, `C use B` — `C` sees `<?>`.
- **Conflict**: `use`-ing two modules that declare `<?>` in different groups is
  rejected in the importer with `:conflicting_operator_fixity`.
- **Prelude still protected**: redeclaring `+`/`|>` group in any user module is
  rejected (now as a conflict).
- **Overload is not a conflict**: adding `fn <?>` of a second type alongside an
  existing declaration parses and elaborates.
- **Idempotent redeclare**: declaring `<?>` with the same group as an imported
  declaration is accepted.
- Full `mix test` gate green.

## Rollback

The change is confined to the parser/elaboration layer. Reverting the fixity
resolver + parser hook + `@prelude` marker + conflict check restores the
location-based rule. No TCB or on-disk-format changes to reverse.
