# Value-Surface Wave 1 — `pickup` — Design (task #23, Wave 1)

**Date:** 2026-07-09. First wave of the value-surface parity program (roadmap `2026-07-09-value-surface-roadmap-design.md`, hardened fcc768d). Teaches the dependent elaborator the `pickup` predicate-dispatch form. Chosen as Wave 1 because it is pure value surface with a direct existing Core target (no new primitive, no kernel change, no representation decision) — it de-risks the elaborator-clause + oracle harness the later waves reuse.

## 1. What pickup is + why it's nearly free

`pickup` is the predicate-dispatch counterpart to `match` (parser.ex:2073-2119). Surface:
```
pickup
  g1 -> b1
  g2 -> b2
  else -> e
```
Parser output: `{:pickup, meta, clauses}` where each clause is `{:pickup_clause, cmeta, [guard, body]}` or the mandatory terminator `{:pickup_else, emeta, [body]}`. The terminator is enforced at PARSE time (`validate_pickup_clauses`, parser.ex:2116) — a `pickup` with no `else` is already a parse error, so "terminator mandatory" needs no elaborator work.

Classic semantics (the oracle, `codegen.ex:1454-1500` + `checker.ex:1349-1366`): a clause chain lowers to nested 2-arm `case Bool of True -> body ; False -> <rest>`, guards must be Bool (E079), all branch types must join (E080).

**The dependent pipeline already has this exact target.** `{:conditional, meta, [c, t, e]}` is fully elaborated in BOTH modes (elaborator.ex:466-473 infer, :1024-1028 checked) via `bool_case/5` (elaborator.ex:2646, a `:case` on the inductive Bool). The conditional clause already: checks the condition against Bool (elaborator.ex:467 — this IS the E079 rule), infers the then-branch, and checks the else-branch against the then-branch's type (elaborator.ex:470 — this IS the E080 join rule). Guarded `match` arms already desugar to nested conditionals through this same path (elaborator.ex:3090-3097, `mk_if/3` at :2882).

So `pickup` is a **pure syntactic desugaring** to a right-nested `:conditional` chain — no new Core, no kernel change, no new typing rule; it reuses the conditional path's Bool-guard and branch-join checks verbatim.

## 2. The change

**Desugaring:** `pickup [g1->b1, g2->b2, ..., else->e]` becomes
```
{:conditional, [], [g1, b1,
  {:conditional, [], [g2, b2,
    ... e ...]}]}
```
i.e. `fold_right` over the guard clauses with the `pickup_else` body as the seed, each guard clause wrapping the accumulated else with `{:conditional, [], [guard, body, acc]}`.

**Where:** add a `{:pickup, _meta, clauses}` clause to the elaborator dispatchers that builds the nested conditional and delegates to the EXISTING conditional elaboration:
- `elaborate_expr_typed` (infer position, elaborator.ex near :466) — builds the chain, calls `elaborate_expr_typed` on it.
- `elaborate_expr_checked` (checked position, near :1024) — builds the chain, calls `elaborate_expr_checked` on it with the expected type.
- `elaborate_expr` (type-level position, near :4735) — only if a `pickup` can appear in type position; if the classic checker never allowed pickup in a type, add a clause that either delegates (same desugaring) or is intentionally omitted so it falls through to the existing `:unsupported_expression` (decide from the classic checker — if `checker.ex` rejects type-level pickup, match that by NOT adding the type-level clause). Ledger the decision.

A single shared private helper `desugar_pickup(clauses) :: {:conditional, ...} | {:error, ...}` builds the chain, used by both value-position clauses. It maps `{:pickup_clause, _, [g, b]}` → wrapper and `{:pickup_else, _, [e]}` → seed. A `pickup` whose parse somehow lacks the terminator (should be impossible post-parse) returns `{:error, {:pickup_missing_else, ...}}` rather than crashing — defensive, ledgered as belt-and-suspenders.

**No kernel change. No emit change** (the desugared conditional lowers through the existing `bool_case`→`:case` emit path). Firewall stays green (elaborator-only, no classic reference).

## 3. Scope guard

- ONLY `pickup`. Do not touch conditional/match/bool_case internals.
- Diff confined to `lib/cure/elab/elaborator.ex` + new test file(s). `lib/cure/core/` EMPTY.
- The `pickup_clause`/`pickup_else` meta may carry positions used in error messages — thread them into the built conditional's meta if the conditional path surfaces them, but do NOT invent new diagnostics; a non-Bool guard or non-joining branches must surface the SAME error the conditional path already produces (verified against the oracle in §4).

## 4. Oracle + ratchet

**Behavioral oracle:** `test/cure/compiler/pickup_test.exs` (classic) pins the runtime semantics and the W081/W082/E076-E080 diagnostics. Wave 1's directed tests mirror the runtime-behavior pins (not the classic error CODES — the dependent path surfaces its own Bool-check/join errors; assert the ERROR HAPPENS on a non-Bool guard and on non-joining branches, and that a well-formed pickup evaluates to the correct branch, matching the classic runtime result). New test file `test/cure/elab/pickup_test.exs`:
- a 3-clause pickup selects each branch correctly at runtime (compile_and_load via the dependent pipeline, apply, compare to the expected value — mirror the classic pickup_test's runtime cases);
- a pickup used in checked position (known expected type) elaborates;
- a non-Bool guard is rejected (error, any shape);
- non-joining branch types are rejected;
- (parser already covers missing-else; a directed parse-error assertion is optional, ledgered if included).

**Ratchet:** re-run the stdlib disposition script (roadmap §0). Wave 1 is expected to move NO module fully to KEEP by itself (every pickup-using std module also needs List/extern/lambda), but it MUST NOT regress the current KEEP set, and any module whose ONLY remaining blocker was pickup flips (per the gap matrix, none are pickup-only — so the expected delta is 0 modules, capability added). State the before/after count; a regression = STOP.

## 5. Gate

1. Red-first: each directed test written and shown failing (the reject cases fail as `:unsupported_expression` before the clause is added; the runtime-selection test fails to compile before).
2. Scoped `mix test test/cure/elab/pickup_test.exs test/cure/elab/` green; then full suite ONCE, 0 failures, arithmetic = baseline + new tests.
3. Firewall test green; disposition count not regressed.
4. Diff-scope: `lib/cure/core/` EMPTY; only elaborator.ex + the new test file touched.
5. Commit (ghost, explicit pathspecs): `feat(elab): pickup predicate-dispatch — desugar to nested conditional (value-surface Wave 1)`.

## 6. Out of scope

Everything else in the value-surface program (List, String, lambda-inference, extern, Map, tuples); any change to conditional/match/bool_case; W081/W082 pickup-specific WARNINGS (the classic redundant-clause/unreachable-else lints — if the dependent path doesn't reproduce them, that is acceptable degradation for Wave 1, ledgered as a possible follow-up, NOT built here).
