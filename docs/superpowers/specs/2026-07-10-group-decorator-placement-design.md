# `@group` decorator placement — above `mod`, not inside it

**Status:** Approved (design), ready for planning.
**Date:** 2026-07-10
**Batch:** Std hygiene (1 of 2; precedes `2026-07-10-primitive-type-declarations-design`).

## Problem

`@group(:core)` currently sits as the *first statement inside* the `mod` body:

```cure
mod Std.Binary
  ## docs …
  use Std.Bounded
  @group(:core)          # <-- inside the body
  ...
```

This is a holdover from when grouping was the magic identifier `__group__`, a
statement that necessarily lived among the module's statements. Now that it is a
real decorator, its in-body position is *misleading*: a decorator annotates
**the item that follows it**, so a reader parses `@group(:core)` as "the next
declaration is grouped," when what it actually annotates is **the module
itself** (`Cure.Stdlib.Preload.module_groups/0` is keyed by module atom, not by
any inner declaration).

The fix is to place `@group` **above** the `mod` declaration, the position where
a decorator unambiguously annotates what follows:

```cure
@group(:core)
mod Std.Binary
  ## docs …
  use Std.Bounded
  ...
```

## Why this is more than moving text

`@group` is in the parser's `@module_level_decorators` allow-list
(`parser.ex:71`). When the parser encounters it, it **short-circuits to a
standalone `{:decorator, …}` node** (`parser.ex:4914`) *before* inspecting what
follows, and never attaches it to anything. `parse_at_attach/4` knows how to
attach a decorator to a following `fn` / `rec` / `type` (`parser.ex:4927-4948`)
but has **no clause for `mod`**. So a `@group` written above `mod` today becomes
a floating node *outside* the module, orphaned from it.

Two consumers read the group, and they must keep working after the move:

1. **Compile-time source scan** — `@std_module_groups` (`preload.ex:110`) uses
   the line-anchored, multiline regex `@group_regex` (`preload.ex:104`,
   `~r/^\s*@group\(\s*:([a-z_][a-z0-9_]*)\s*\)/m`). This is **position-agnostic**:
   it matches `@group(:x)` on *any* line, so it already works whether the
   decorator is inside or above `mod`. **No change required** — but the design
   pins a test that confirms it.
2. **BEAM-attribute path** — packaged releases with no `lib/std/` source read the
   group from each module's `-group([:g])` BEAM attribute
   (`preload.ex:422-428`). That attribute is emitted by the **classic codegen**
   from a module-level decorator. If the parser attaches the pre-`mod` `@group`
   to the module container, codegen must read it from the container meta so the
   attribute is still emitted.

## Design

### 1. Parser — attach a pre-`mod` module-level decorator to the module

Before the `@module_level_decorators` short-circuit turns `@group` into a
standalone node, check whether the very next token opens a module (`mod` /
`module` keyword). If so, parse the module and attach the decorator to the
module container's `:decorator` meta (reusing `attach_decorator/3`'s generic
container clause, the same path `@builtin(:key) type Name` uses at
`parser.ex:4945-4948`). If the next token is anything else, preserve today's
behaviour (standalone node) so nothing regresses.

Result AST for `@group(:core)\nmod Std.Binary … end`: a single `{:container,
container_type: :module, …}` node carrying `decorator: [group: [:core]]` (or the
established meta shape — the plan verifies the exact key against
`attach_decorator/3`), **not** a floating sibling decorator.

### 2. Classic codegen — emit `-group` from the module container meta

Wherever the classic pipeline currently emits the `-group([:g])` module
attribute from an in-body `@group` decorator node, additionally (or instead)
read it from the module container's attached decorator meta, so the attribute is
emitted for the above-`mod` form. This touches `lib/cure/compiler/codegen.ex` —
which is legitimate here: module grouping is a **classic-pipeline / Preload
runtime** concern, not a dependent-kernel one. This is explicitly *not* a
dependent-pipeline change.

### 3. Migration — move `@group(:core)` above `mod` in all 13 std files

The modules carrying `@group(:core)` today:

`functor, bool, ord, equatable, bounded, equivalent, core, decision, sigma,
binary, nat, proof, show` (files under `lib/std/`).

Each moves its `@group(:core)` line from the body to immediately above its `mod`
line. No other edits.

### 4. Back-compat — tolerate the in-body form, don't hard-error

The parser continues to accept an in-body `@group` (today's standalone-node
path), so any usage outside the migrated std files does not break, and the
position-agnostic regex keeps finding it. The **canonical, documented form is
above `mod`**, and all std files adopt it. A deprecation *warning* for the
in-body form is out of scope (a candidate for the migration facility later).

> Decision point for spec review: if you prefer a hard cutover (in-body `@group`
> becomes a parse error once the 13 files are migrated), say so and §4 flips —
> it is a one-line parser choice. The tolerant form is chosen as the lower-risk
> default.

## Testing

- **Parser** — `@group(:core)\nmod M … end` parses to a single module container
  whose meta carries the group; the floating-sibling shape is gone. An in-body
  `@group` still parses (back-compat).
- **Association** — `Preload.module_groups()` returns `:core` for every migrated
  module (regex path), and `group_from_beam/2` returns `:core` for a compiled
  module (BEAM-attribute path) — proving both consumers survive the move.
- **Migration guard** — every file under `lib/std/` that contains `@group(`
  has it on a line *above* its `mod` line (a structural rehearsal check over the
  sources), so no file silently keeps the legacy placement.
- **Full suite + stdlib preload** green (the preload machinery is exercised
  throughout the suite via `setup_all` preload).

## Out of scope

- Any change to the dependent elaborator / kernel.
- Deprecation warnings or automated codemod for the in-body form.
- Grouping semantics themselves (what `:core` means, prelude membership) — that
  is the sibling primitive-types spec's concern.
