# Value-Surface Wave 1 — `pickup` — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Teach the dependent elaborator the `pickup` predicate-dispatch form by desugaring it to the already-supported right-nested `:conditional` chain — no kernel change, no new Core, no new typing rule.

**Architecture:** `pickup` is a pure syntactic desugaring. A `{:pickup, meta, clauses}` surface node folds right into `{:conditional, [], [guard, body, acc]}` wrappers around the terminator's body as seed. Both value-position dispatchers (`elaborate_expr_typed` infer, `elaborate_expr_checked` checked) gain a `:pickup` clause that builds the chain via one shared helper and delegates to the EXISTING conditional elaboration, which already enforces the Bool-guard (E079-equivalent) and branch-join (E080-equivalent) rules. Type-position (`elaborate_expr/3`) is deliberately left unsupported — it already has no `:conditional` clause, so a desugared `pickup` is transitively unsupported there with zero new code.

**Tech Stack:** Elixir; Cure dependent elaborator (`lib/cure/elab/elaborator.ex`); ExUnit.

## Global Constraints

- **Spec:** `docs/superpowers/specs/2026-07-09-wave1-pickup-design.md` (hardened, commit c10ed85). Read it before starting; this plan implements it exactly.
- **Diff scope:** ONLY `lib/cure/elab/elaborator.ex` + the new test file `test/cure/elab/pickup_test.exs`. `lib/cure/core/` MUST stay EMPTY of changes. No emit change. No parser change. No kernel change.
- **Two-pipeline steer:** the dependent machinery lives ONLY in `lib/cure/elab/*` + `lib/cure/core/*`. IGNORE `lib/cure/compiler/*` (`codegen.ex`, `pattern_compiler.ex`) and `lib/cure/types/*` — those are the non-dependent lowering/checker pipeline and their same-named `pickup`/`conditional` functions are decoys. `lib/cure/compiler/pickup` handling in `codegen.ex` is the ORACLE (read for behavior), never a place to edit.
- **BUILD-LOCK ORDERING (critical):** this plan's execution runs on the SAME worktree as the in-flight #22 canonical-spelling kernel batch. Only ONE `mix` suite may run at a time (a past concurrent full-suite run caused a kernel panic). Do NOT run any `mix` command until the #22 executor has released the build lock (confirmed complete). Until then, only write code/tests. When the lock is free, run scoped tests first, and the full suite exactly ONCE at the gate.
- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO `Co-Authored-By`, NO Claude signature, NO trailers.
- **Explicit-pathspec staging ONLY:** `git add -- <path>` / `git commit -- <path>`. NEVER `git add -A` / `git add .` / `git add -u` — a concurrent agent shares this worktree.
- **Tests immutable once green**, behavioral not implementation-coupled. Strict red-green: show each named test failing before implementing.
- **No `iex -S mix`.** Prefer scoped `mix test <file>`.

---

## File Structure

- **Modify:** `lib/cure/elab/elaborator.ex`
  - Add `elaborate_expr_typed({:pickup, _meta, clauses}, ...)` clause immediately BEFORE the catch-all at line 554 (`def elaborate_expr_typed(other, ...)`), i.e. after the `:pattern_match` clause (ends ~553).
  - Add `elaborate_expr_checked({:pickup, _meta, clauses}, ...)` clause immediately BEFORE the checked catch-all at line 1032 (`def elaborate_expr_checked(expr, expected_core, ...)` → `elaborate_expr_checked_fallback`), i.e. after the `:conditional` checked clause (ends 1030).
  - Add private helpers `desugar_pickup/1`, `fold_pickup_wrappers/2`, `pickup_seed/1` (place them near the new clauses, e.g. just after the `elaborate_expr_checked` `:pickup` clause, before `elaborate_lambda/6` at ~1035, OR grouped with other private desugaring helpers — executor's choice, keep them together).
- **Create:** `test/cure/elab/pickup_test.exs`

## Anchors verified against current source (2026-07-09)

- `elaborate_expr_typed({:conditional, _meta, [c, t, e]}, names, ctx, env)` — line 466. Infer mode: checks `c` against Bool, infers `t`'s type, checks `e` against it. This IS the E079/E080 path.
- `elaborate_expr_typed(other, _names, _ctx, _env)` catch-all — line 554, returns `{:error, {:unsupported_expression, other}}`.
- `elaborate_expr_checked({:conditional, _meta, [c, t, e]}, expected_core, names, ctx, env)` — line 1024. Checked mode: checks `c` against Bool, checks both branches against `expected_core`.
- `elaborate_expr_checked(expr, expected_core, names, ctx, env)` fallback — line 1032.
- Parser output (parser.ex:2084-2119, 2226-2239): `{:pickup, meta, clauses}`; guard clause `{:pickup_clause, meta, [guard, body]}`; terminator either `{:pickup_else, meta, [body]}` OR a trailing `{:pickup_clause, meta, [{:literal, _, true}, body]}` (the alternative-form terminator, `pickup_terminator?/2`). Terminator-last + single-terminator + non-empty are all enforced at PARSE time (`validate_pickup_clauses`).

---

## Task 1: `pickup` desugaring + infer/checked dispatch

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` (two new public clauses ~line 554 and ~line 1032; three new private helpers)
- Test: `test/cure/elab/pickup_test.exs` (create)

**Interfaces:**
- Consumes: existing `elaborate_expr_typed/4`, `elaborate_expr_checked/5` (the `:conditional` clauses at 466 / 1024); parser node shapes above.
- Produces: `pickup` support in both value positions. No public signature changes; the two dispatchers gain a clause, and `desugar_pickup/1 :: (clauses) -> {:ok, expr} | {:error, {:pickup_missing_else, term}}` is a private helper.

- [ ] **Step 1: Write the failing test file**

Create `test/cure/elab/pickup_test.exs`. Uses only `Bool` guards + `Nat` bodies (the dependent pipeline's currently-supported surface — NOT `Atom`/atom-literals, which classic pickup tests use but the dependent path does not yet support). Mirrors `conditional_test.exs` harness (`Program.elaborate` → `Emit.compile_and_load` → `apply`).

```elixir
defmodule Cure.Elab.PickupTest do
  @moduledoc """
  `pickup` predicate dispatch (value-surface Wave 1). It desugars to a
  right-nested `:conditional` chain and reuses that path's Bool-guard and
  branch-join checks verbatim — no kernel change, no new Core. Guards must be
  Bool; all branch bodies must join. Tests use Bool guards + Nat bodies only
  (the dependent pipeline's supported surface); the classic pickup oracle's
  Atom/atom-literal cases are out of reach for the dependent path today.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "3-way pickup with an else terminator selects each branch at runtime" do
    src =
      @nat <>
        "  fn pick(b1: Bool, b2: Bool) -> Nat =\n" <>
        "    pickup\n" <>
        "      b1 -> Z()\n" <>
        "      b2 -> S(Z())\n" <>
        "      else -> S(S(Z()))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Pickup1", functions: [:pick])

    assert apply(mod, :pick, [true, false]) == :Z
    assert apply(mod, :pick, [false, true]) == {:S, :Z}
    assert apply(mod, :pick, [false, false]) == {:S, {:S, :Z}}
  end

  test "trailing `true ->` terminator form (no pickup_else node) evaluates its body when reached" do
    src =
      @nat <>
        "  fn always_b() -> Nat =\n" <>
        "    pickup\n" <>
        "      false -> Z()\n" <>
        "      true  -> S(Z())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Pickup2", functions: [:always_b])

    # first guard is literal false, so the trailing-true terminator body is reached
    assert apply(mod, :always_b, []) == {:S, :Z}
  end

  test "a degenerate single-clause `pickup else -> e` collapses to its body" do
    src =
      @nat <>
        "  fn only() -> Nat =\n" <>
        "    pickup\n" <>
        "      else -> S(Z())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Pickup3", functions: [:only])

    assert apply(mod, :only, []) == {:S, :Z}
  end

  test "a pickup used against a known return type (checked position) elaborates" do
    src =
      @nat <>
        "  fn checked(b: Bool) -> Nat =\n" <>
        "    pickup\n" <>
        "      b -> Z()\n" <>
        "      else -> S(Z())\nend\n"

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a non-Bool guard is rejected" do
    # guard `n` : Nat, not Bool — the conditional path's Bool check rejects it.
    src =
      @nat <>
        "  fn bad(n: Nat) -> Nat =\n" <>
        "    pickup\n" <>
        "      n -> Z()\n" <>
        "      else -> S(Z())\nend\n"

    assert {:error, _} = Program.elaborate(src)
  end

  test "non-joining branch types are rejected" do
    # then-branch : Nat, else-branch : Bool — no single result type.
    src =
      @nat <>
        "  fn bad2(b: Bool) -> Nat =\n" <>
        "    pickup\n" <>
        "      b -> Z()\n" <>
        "      else -> true\nend\n"

    assert {:error, _} = Program.elaborate(src)
  end
end
```

- [ ] **Step 2: Run the test to verify it fails (RED)** — only if the build lock is free (see Global Constraints); otherwise write Step 3 first and run Steps 2+4 together once the lock frees.

Run: `mix test test/cure/elab/pickup_test.exs`
Expected: the selection / trailing-true / degenerate / checked tests FAIL because `{:pickup, ...}` hits the `elaborate_expr_checked` fallback → `{:error, {:unsupported_expression, {:pickup, ...}}}`, so `Program.elaborate` returns `{:error, ...}` and the `{:ok, env}` match raises. (The two reject tests may already "pass" for the WRONG reason — an `:unsupported_expression` error rather than the targeted Bool/join error — which is why Step 4 re-confirms them after the clause exists.)

- [ ] **Step 3: Add the desugaring helper + both dispatcher clauses**

Add the `:pickup` clause to `elaborate_expr_typed` immediately before the catch-all at line 554:

```elixir
  # `pickup` predicate dispatch (value-surface Wave 1). Pure syntactic
  # desugaring to a right-nested `:conditional` chain; reuses the conditional
  # path's Bool-guard and branch-join checks verbatim. No kernel change.
  # See docs/superpowers/specs/2026-07-09-wave1-pickup-design.md.
  def elaborate_expr_typed({:pickup, _meta, clauses}, names, ctx, env) do
    with {:ok, desugared} <- desugar_pickup(clauses) do
      elaborate_expr_typed(desugared, names, ctx, env)
    end
  end
```

Add the mirrored clause to `elaborate_expr_checked` immediately before the fallback at line 1032:

```elixir
  # `pickup` in checked position: desugar to the nested conditional and check
  # it against the expected type (each branch body is checked at `expected_core`).
  def elaborate_expr_checked({:pickup, _meta, clauses}, expected_core, names, ctx, env) do
    with {:ok, desugared} <- desugar_pickup(clauses) do
      elaborate_expr_checked(desugared, expected_core, names, ctx, env)
    end
  end
```

Add the three private helpers (keep them together, near the new clauses):

```elixir
  # Fold a `pickup` clause list into a right-nested `:conditional` chain.
  # The LAST clause is the terminator (its body is the seed); every earlier
  # clause is a guard wrapper `{:conditional, [], [guard, body, acc]}`.
  # Three terminator shapes (matching codegen.ex's pickup lowering exactly):
  #   {:pickup_else, _, [e]}                         -> seed e
  #   {:pickup_clause, _, [{:literal, _, true}, e]}  -> seed e (guard discarded)
  #   anything else in last position                 -> defensive error
  # A single-clause pickup (only the terminator) collapses to the seed body
  # with no wrapping conditional (PICKUP §11: `pickup else -> e ≡ e`).
  # The empty/terminatorless shapes are impossible post-parse (the parser's
  # validate_pickup_clauses enforces them); the error arms are belt-and-suspenders.
  defp desugar_pickup([]), do: {:error, {:pickup_missing_else, []}}

  defp desugar_pickup(clauses) do
    {wrappers, [last]} = Enum.split(clauses, length(clauses) - 1)

    with {:ok, seed} <- pickup_seed(last) do
      fold_pickup_wrappers(wrappers, seed)
    end
  end

  defp fold_pickup_wrappers(wrappers, seed) do
    Enum.reduce_while(Enum.reverse(wrappers), {:ok, seed}, fn
      {:pickup_clause, _cm, [g, b]}, {:ok, acc} ->
        {:cont, {:ok, {:conditional, [], [g, b, acc]}}}

      other, {:ok, _acc} ->
        {:halt, {:error, {:pickup_missing_else, other}}}
    end)
  end

  defp pickup_seed({:pickup_else, _m, [e]}), do: {:ok, e}
  defp pickup_seed({:pickup_clause, _m, [{:literal, _, true}, e]}), do: {:ok, e}
  defp pickup_seed(other), do: {:error, {:pickup_missing_else, other}}
```

- [ ] **Step 4: Run the scoped test to verify it passes (GREEN)**

Run: `mix test test/cure/elab/pickup_test.exs`
Expected: all six tests PASS. In particular the two reject tests now fail for the RIGHT reason (Bool-guard / branch-join error from the conditional path, not `:unsupported_expression`) — confirm by temporarily inspecting the error tuple if in doubt, but do not add an implementation-coupled assertion on the exact error atom (the dependent path's own error shape, not the classic E-code).

- [ ] **Step 5: Diff-scope + firewall + ratchet checks**

- Confirm `git -C <worktree> diff --stat` shows ONLY `lib/cure/elab/elaborator.ex` and the new test file. `lib/cure/core/` MUST be untouched.
- Run the firewall test (proves the dependent pipeline still references no classic module):
  Run: `mix test test/cure/dependent_pipeline_firewall_test.exs` → expected PASS.
- Ratchet (spec §4): re-run the stdlib disposition script (roadmap `2026-07-09-value-surface-roadmap-design.md` §0). Record the KEEP-count before/after. Expected delta: **0 modules** (no std module is pickup-only-blocked). A REGRESSION in the KEEP set = STOP and report. (If the disposition script needs `mix`, run it only while you hold the build lock, serialized with the full-suite run below.)

- [ ] **Step 6: Full suite ONCE, then commit**

- With the build lock held (see Global Constraints), run the full suite exactly once:
  Run: `mix test`
  Expected: 0 failures; total = prior baseline + 6 new tests. (If any pre-existing unrelated failure appears that is NOT caused by this diff, STOP and report — do not "fix" out-of-scope tests.)
- Commit (ghost author, explicit pathspecs):

```bash
git -C <worktree> add -- lib/cure/elab/elaborator.ex test/cure/elab/pickup_test.exs
git -C <worktree> commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -- lib/cure/elab/elaborator.ex test/cure/elab/pickup_test.exs \
  -m "feat(elab): pickup predicate-dispatch — desugar to nested conditional (value-surface Wave 1)"
```

---

## Out of scope (do NOT build here)

- Everything else in the value-surface program (List, String, lambda-inference, @extern, Map, tuples/records).
- Any change to `:conditional` / `match` / `bool_case` internals.
- Type-position (`elaborate_expr/3`) `:pickup` support — deliberately omitted; the desugared `:conditional` is already transitively unsupported there (spec §2).
- W081/W082 pickup-specific WARNINGS (classic redundant-clause / unreachable-else lints). If the dependent path doesn't reproduce them, that is acceptable Wave-1 degradation, ledgered as a possible follow-up, NOT built here.
- The guard-scope gap (PICKUP §5.4: a guard's bindings visible in its own body). Inert today — the dependent elaborator has no clause for a bare `{:assignment, ...}` standalone expression, so no reachable guard both type-checks as Bool and introduces a binding. Ledgered in the spec (§1); re-derive before relying on it if standalone-assignment-as-expression is ever added.
