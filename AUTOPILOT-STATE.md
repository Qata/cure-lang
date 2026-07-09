# Autopilot state — Typeclasses (task #21)

**Branch:** `autopilot/kernel-parity-batch` (per operator preference: no new worktree)
**Plan:** `docs/superpowers/plans/2026-07-10-typeclasses-plan.md`
**Status:** Core machinery COMPLETE and green (full suite 3289 passed, 0 failures).
Tasks 6, 8, 9 are BLOCKED on prerequisite subsystems outside the typeclasses
task. Stopping per the plan's §5 blocker rule + autopilot Halt protocol —
**not** papering over. Not auto-merged.

## Done (committed on this branch)

| Task | What | Commit |
|------|------|--------|
| 1–3  | `interface`/`implementation` parse + descriptors + coherence registry + mangled-method lowering | (earlier) |
| 4    | Concrete + abstract (dictionary-threaded) method resolution; constrained-function dict injection + erasure demotion | `8b2e25f` |
| #26  | `struct_eq`/`struct_ne` type-arg erased (fixes `Std.List.contains` relevance bug) | `969db87` |
| 5    | HKT resolution (Functor over `List`); `apply_checked_args` for checking-mode method args | `e4101a0` |
| 7    | Structural `deriving Equatable`/`Ord` (recursion-safe, no connective/tuple); `Show` reports an honest blocker | `85d9b26` |

The load-bearing deliverable — the compile-time typeclass system that replaces
runtime `proto`/`impl`, with the `Equatable` interface + resolution that #25/#27/#29
consume — is in place and fully tested (`test/cure/elab/resolve_firstorder_test.exs`,
`resolve_hkt_test.exs`, `struct_eq_erasure_test.exs`, `deriving_test.exs`).

## Blocked — Tasks 6, 8, 9 (evidence-based)

Each blocker was verified by probing `Program.elaborate/1` directly (not assumed):

### Task 8 — migrate 5 stdlib modules (`lib/std/{equatable,ord,show,functor,access}.cure`)

- **show** — every instance renders via `<>` string concat and `int_to_string`.
  `a <> b` on `String` → `{:error, {:unsupported_expression, …}}`: the dependent
  pipeline has **no string-concatenation lowering**. Blocked by the String value
  surface (#27/#29). HARD.
- **functor** — `impl Functor for List` delegates to `Std.List.map`; `use Std.List`
  → `{:error, {:unsupported_expression, …}}` because `Std.List`'s `uncons`/`split_first`
  use the still-open flat-tuple value surface (`%[[],[]]`). Blocked by #23. HARD.
- **access** — keyword-list helpers use `==`/`!=` on statically `Any`-typed operands
  (spec §3.4 has no resolution rule for `Any` — neither a concrete head nor a rigid
  var under a constraint), and the module traffics in `Tuple` throughout. Blocked by
  #23 + the anticipated §7 `Any` gap. HARD (the plan flagged this as *expected*).
- **equatable / ord** — Int/Float instances migrate cleanly, but the **String** instances
  fail: `x == y` on `String` → `{:error, :unknown_global}` (no `string_eq` builtin-op;
  `struct_eq`'s quoted `String` type reads back as an unknown global). The §4.2
  circularity fix requires `string_eq`/`atom_eq`/`bool_eq` builtin-ops that **do not
  exist** — the plan says "add one or special-case, do NOT invent a repoint," i.e. a
  new builtin-op is a prerequisite. PARTIAL — cannot ship a module whose String/Atom
  instances don't elaborate.
- **Shared-worktree risk:** `lib/std/*.cure` are consumed by the still-present classic
  `proto`/`impl` pipeline (#18 rip-out is PENDING). Converting them to
  `interface`/`implementation` in place risks breaking classic consumers. Migration
  should follow, not precede, #18.

### Task 6 — retire `struct_eq`/`struct_ne`; repoint `==`/`<` to Equatable/Ord

- Consumes Task 8's **complete** primitive instance set, which is blocked (above).
- `==` on `Bool` and on a bare ADT currently succeed via `struct_eq` (verified `:ok`).
  Retiring `struct_eq` flips every instance-less `==`/`<` site to `{:no_instance, …}`
  — the intended semantics, but a **suite-wide** behavioural migration that needs the
  full stdlib instance set in scope AND updates across existing tests. Unsafe to force
  autonomously while the primitive instances can't be fully expressed and the classic
  pipeline still routes `==`. HARD (cascading).

### Task 9 — differential oracle cluster

Depends on Tasks 6/8 landing (the probes exercise migrated `==`/`show`/`fmap`). Deferred
with them.

## What unblocks the rest (prerequisites, in order)

1. **#23** flat-tuple value surface — unblocks `Std.List` (`uncons`/`split_first`),
   hence **functor** and **access**.
2. **#27/#29** String value surface — string concatenation lowering + `string_eq`
   (and `atom_eq`) builtin-ops + `String` as an interface-record field type — unblocks
   **show** and the String/Atom instances of **equatable**/**ord**.
3. **#18** classic-pipeline rip-out (or a decision to dual-register) — makes it safe to
   convert `lib/std/*.cure` to `interface`/`implementation` without breaking classic
   `proto`/`impl` consumers.
4. Then **Task 8** (all 5 modules) → **Task 6** (global `==`/`<` repoint, one licensed
   suite-wide test pass) → **Task 9** (oracle).

## Recommendation

Merge the completed typeclass machinery (Tasks 1–5, 7 + #26) — it stands on its own and
the suite is green. Sequence Tasks 6/8/9 after #23 and #27/#29 land. The `Deriving.Show`
clause is a one-liner once string primitives exist (see `deriving.ex` moduledoc + the
`{:deriving_needs_strings, :Show}` guard).
