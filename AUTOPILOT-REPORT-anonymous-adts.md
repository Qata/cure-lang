# Autopilot — Anonymous ADTs (`Int | String`)

**Branch:** `autopilot/anonymous-adts` (15 commits, working tree clean)
**Status:** ✅ Complete — ready for review & merge. **Not auto-merged.**
**Suite:** 4421 passed, 2 skipped (baseline 4412/2; the 2 skips are the pre-existing
`#18`-paused pins, unchanged).
**TCB:** **zero change** — `git diff 49a7d47..HEAD -- lib/cure/core/` is empty.

## What landed

`Int | String` and `3 | :north` are now type expressions. They elaborate to a
compiler-generated **discriminated inductive family** whose constructors are derived
from the members. A union's identity is its canonical member list — flattened,
`nf`-normalised, type-distinguishingly keyed, deduped, lexically sorted — so
`Int | String` and `String | Int` produce *literally the same* `{:data, name}` and are
definitionally equal with no kernel involvement at all.

- **Introduction** is an elaborator-inserted coercion at check-position, never a kernel
  rule. The injected `{:ctor, …}` is re-verified by `Kernel.check`, so the elaborator
  stays untrusted.
- **Elimination** is by type pattern (`match x { n: Int -> … }`), desugared to an
  ordinary Core `:case`, so coverage, exhaustiveness and totality come from existing
  machinery.
- **Widening** (`Int|Bool` → `Int|Bool|Atom`) is a real `:case` remap, not a cast.
- **Erasure**, proven on a real BEAM: `{:'Union<Bool|Int>$Int', 7}` for a type member,
  a bare nullary atom for a literal member.

## Stage-by-stage

| Stage | Outcome |
|---|---|
| 0 — Brainstorm | Design approved (the only human gate). Spec `cb609a4`. |
| 1 — Spec review (Sonnet) | 6 passes. Found the `whnf`-vs-`nf` hole and the bare-name keying hole — both real. `861ec0f`. |
| 2 — Plan | 10 TDD tasks. `c52fb73`. |
| 3 — Plan review (Sonnet) | 11 passes. Caught a **severe regression in my own plan**: an unconditional literal guard in `parse_type_arrow/1` would have broken every numeral-in-type-index in the tree (`Bounded(1114112)` in `lib/std/char.cure`). `49a7d47`. |
| 4 — Execute (Opus, TDD) | 10 tasks, red→green, commit per task. |
| 5 — Code review (Sonnet) | 5 passes. **Five real bugs**, each reproduced red-test-first before fixing. |
| 6 — Verify | Full suite green. |

## Two binding corrections to the spec (found while planning, verified in the tree)

1. **Constructor names MUST be family-qualified.** The spec said the ctor atom could be
   the bare key (`:'Int'`). `env.ctors` is a **global flat map**, so two unions each
   having an `Int` member would both register `:Int`, last-write-wins, and
   `ctor_to_family[:Int]` would point at the wrong family — silently miscompiling every
   `match` on the other union. Ctors are `:"<union_key>$<member_key>"`.
2. **No synthetic module is needed.** The spec required generated families be "emitted
   once per program, referenced remotely." `Emit` only walks `env.defs`; families emit
   **zero** BEAM forms and ctors lower inline. Two modules declaring the identical family
   cannot conflict. That whole subsystem was deleted from the plan.

## Bugs the reviews caught (all reproduced, all fixed)

**Stage 5 — code review, five confirmed defects:**

1. **`union_family?/1` was spoofable** (`3fd6551`). I assumed `<` was unlexable in a type
   name. Backtick-quoted identifiers let a user declare a real ADT named
   `` `Union<Bool|Int>` ``, which the elaborator then "exploded" as a generated family,
   corrupting it. Now the namespace is reserved at every declaration site.
2. **A regression *beyond* union code** (`3b82ba8`). The pre-existing `pattern_binders/1`
   — backing the capture-avoidance guard used by ~10 surface-substitution sites — didn't
   know the new `:typed_pattern` node's bound name, so an unrelated `let`/`match`
   combination spliced the wrong term. Also added the missing capture guard to the
   sub-union substitution itself.
3. **`union_renames/3` needed a fixpoint** (`286e511`). A union nested inside another
   union's payload (`List(Union<…>)`) could be visited first and keyed against a stale
   rename map, registering the family under a name that lied about its content.
4. **Qualified type names rejected** in pattern annotations (`514655f`) — `n: Std.Nat.Nat`
   hard-failed, though the same name parses fine as a parameter annotation.
5. **`dependent?/1` didn't recurse into meta** (`c0cc216`), so a union in a `let`
   ascription or a match-arm pattern silently routed to the classic pipeline.

**During execution — the most important catch, by the round-trip test:**

`Program.dependent?/1` had no clause for `:union_type`, so a module using only unions was
judged non-dependent and compiled by the **classic** pipeline, where the union resolves to
`:any` and the value is emitted **untagged**. The feature type-checked perfectly and was
then never used at codegen — silently producing exactly the untagged erasure the design
rejected as unsound (`String` *is* `List(Char)`, so members are not runtime-distinguishable).
Fixed in `9052df5`; the round-trip test now pins the tagged erasure.

## Deviations from the plan, and why

- **`parse_pattern_type/1`** instead of `parse_type_expr/1` for pattern annotations. The
  plan's version breaks the feature's primary syntax: `parse_type_arrow/1` is greedy, so
  given `n: Int -> 1` it read `Int -> 1` as a *function type*, swallowed the arm's arrow,
  and parsed the body as a codomain.
- **`coerce_union/5` applied in four infer-mode sites**, not the single check-mode funnel
  the plan named. `elaborate_body/6` (catch-all *and* `{:function_call,…}`) and
  `elaborate_branch_body/5` all infer and discard the expected type, so the plan's single
  injection point could never fire for `fn f(n: Int) -> Int | Bool = n`.
- **Sub-union arms use an `assert_type` ascription**, not the plan's `{:assignment,…}` in a
  `{:block,…}` — `:block` has no infer-mode clause and branch bodies are inferred.
- **The pre-pass hooks `register_signature/2` as well as `elaborate/2`** — `Program` routes
  function defs to the former, and a signature is the commonest place a union appears.
- **Three plan tests were inexpressible** and were replaced with cases that test the same
  property: `Bounded(1+1)` doesn't parse (no arithmetic in type-arg position → used a
  *certified global applied inside an index*, the real whnf-vs-nf distinguisher); `:4` isn't
  lexable (→ `"north" | :north`, same collision property); two sibling modules can't both
  declare `Point` (hard `:sibling_module_collision` → drove `rekey_module_env/3` directly).

## Known limitations (by design, and one deferred)

- Members must be **ground and closed** — `a | Int` is rejected (that's row polymorphism).
- Unions live in **check mode only**: `let xs = [1, "a"]` needs an annotation.
- **Uniform tagged erasure**, no transparent erasure for all-literal unions.
- `@extern` cannot return a union directly.
- **The spec's headline heterogeneous-`Map` example is not yet exercisable end-to-end** —
  not because of this branch, but because `Std.Map` itself does not yet elaborate in the
  dependent pipeline. Pre-existing, separate gap.
- **AtomVM validation is a follow-up outside this repo.** `cure-lang` is the compiler; the
  generic-unix AtomVM loop lives in the parent `esp32-beam` repo. The in-repo equivalent
  (a real BEAM round-trip) is done and green.

## Next

Review and merge `autopilot/anonymous-adts`. Then, if wanted: run the union oracle programs
on generic-unix AtomVM from the parent repo.
