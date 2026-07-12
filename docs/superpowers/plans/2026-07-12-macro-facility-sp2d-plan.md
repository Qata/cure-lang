# SP2 Tier-3 slice 1 — Parse `computed by` (elab) rules — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (autopilot Stage 4). Steps use `- [ ]`. Strict red-green TDD; commit per task. Begins Tier-3 (`computed by`), the SP2 headline capability. SP1 + SP2 M1 + M3 COMPLETE.

**Goal:** Parse the Tier-3 rule form `syntax <segments> computed by <elab-fn>` (base design §3, tier table row 3). A `computed by` rule's expansion is *computed* at compile time by running the referenced elab function over the quoted input — vs Tier-2 `becomes`'s template substitution. This slice is the **front-end only**: recognize `computed by <fn>`, capture the elab reference on the rule map. Building the quoted-AST `Syntax` value model and the compile-time execution that actually *runs* the elab are the next Tier-3 slices.

**Architecture:** A macro-body `syntax` rule is closed by a **tier verb** (design §3, l.83): `becomes <template>` (Tier-2, built) or `computed by <fn>` (Tier-3, this). After a rule's `segments`, branch on the verb: `becomes` → the existing `%{kind: :syntax, template: …}` path; `computed` → a new `%{kind: :computed, elab: …}` rule. `:computed` rules are deliberately **not** harvested into `active_macros` yet (harvest filters `kind: :syntax`), so a computed macro's use-site stays inert until the execution slice — nothing can dispatch to an elab that can't run yet. **TCB delta zero** (parser front-end; the elab's eventual *output* is re-elaborated + kernel-checked, K3 firewall, when execution lands).

**Tech Stack:** Elixir; `lib/cure/compiler/parser.ex`; ExUnit.

## Global Constraints

- **TCB delta ZERO.** `lib/cure/compiler/parser.ex` only (+ tests). No `lib/cure/core/*`, no `lib/cure/elab/*`.
- **Ghost commits** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no Co-Authored-By. `git add -- <path>`, never `-A`.
- **One build at a time.** Scoped `mix test test/cure/compiler/macro_computed_test.exs`; `mix test test/cure/compiler/` for regression.
- **Run mix from the worktree root** (`.claude/worktrees/core-let-binder`), NEVER the parent clone. (A background formatter re-touches `parser.ex` timestamps → the Edit tool may report "file modified"; `git status` shows it clean vs HEAD — re-read the exact region and re-apply.)
- **Tests immutable once green.** Go green by fixing implementation only; touch a passing test only if it is provably wrong (state why first).
- **Locked AST:** `{:macro_def, meta, rules}` unchanged; `:computed` is a new rule-map `kind`, a sibling of `:syntax`/`:literal`/`:explain`.

## Verified grounding (probed live)

- `computed by build_it` tokenizes `[identifier: "computed", identifier: "by", identifier: "build_it"]` — all plain identifiers (soft keywords, like `syntax`/`becomes`/`literal`/`explain`).
- Current `parse_macro_rule/1` (`parser.ex`): after `{segments, state} = parse_rule_segments(state, [])` it unconditionally expects `becomes`, then `parse_expr` (template), then `parse_rule_examples`, then builds `%{kind: :syntax, keyword, segments, template, examples, progress: nil, line}`. The verb branch goes right after `parse_rule_segments`.
- `harvest_active_macros/1` filters `%{kind: :syntax, keyword: kw} when is_binary(kw)`; `harvest_literal_macros/1` filters `%{kind: :literal, …}`. A `:computed` rule matches neither → **not harvested → inert at use-sites** (exactly right for this slice).
- `MacroValidate` checks filter `kind: :syntax` (`check_rules_pinned`, `check_examples`) or `[:syntax, :literal]` (`derive_points`) — so `:computed` rules are also exempt from the M1/M3 obligations this slice (their examples need the elab to run; that is a later slice's concern).
- Helpers: `peek/1`, `advance/1`, `add_error/2`, `parse_expr/2`, `parse_rule_examples/1` (from M3). The elab reference (`build_it`, or a dotted `Mod.build_it`) is captured by `parse_expr(state, 0)` — a bare name parses to `{:variable, meta, name}`, a dotted path to its dotted-name AST, and `parse_expr` stops at the newline / examples indent.

---

### Task 1: Parse `syntax … computed by <fn>` to a `:computed` rule

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (`parse_macro_rule/1` — split the verb branch; add `parse_becomes_rule/4`, `parse_computed_rule/4`)
- Test: `test/cure/compiler/macro_computed_test.exs` (create)

**Interfaces:**
- Produces `%{kind: :computed, keyword: String.t(), segments: […], elab: ast(), examples: […], progress: nil, line: n}` for a `computed by` rule. `becomes` rules keep their exact `%{kind: :syntax, …}` shape (regression-guarded).

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/compiler/macro_computed_test.exs
defmodule Cure.Compiler.MacroComputedTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  defp rules({:macro_def, _, rs}), do: rs
  defp rules({_t, _m, ch}) when is_list(ch), do: Enum.find_value(ch, &rules/1)
  defp rules(_), do: nil

  test "a `computed by` rule parses to a :computed rule capturing the elab reference" do
    [rule] = rules(parse!("macro Mk\n  syntax mk <x: Code> computed by build_it\n"))
    assert rule.kind == :computed
    assert rule.keyword == "mk"
    assert [{:hole, %{name: "x", kind: "Code"}}] = rule.segments
    assert {:variable, _, "build_it"} = rule.elab
  end

  test "a `becomes` rule still parses to a :syntax rule (non-breaking)" do
    [rule] = rules(parse!("macro Now\n  syntax now becomes Clock.now()\n"))
    assert rule.kind == :syntax
    assert {:function_call, _, _} = rule.template
  end

  test "a :computed rule is NOT dispatched at a use-site yet (inert until execution slice)" do
    # `mk` is a computed macro; a bare `mk` use-site must parse as an ordinary
    # variable (not expand), because :computed rules aren't harvested yet.
    node = parse!("mod M\n  macro Mk\n    syntax mk computed by build_it\n  fn f() = mk\n")
    find = fn find, n ->
      case n do
        {:function_def, meta, [body]} -> if(to_string(Keyword.get(meta, :name)) == "f", do: body)
        {_t, _m, ch} when is_list(ch) -> Enum.find_value(ch, &find.(find, &1))
        _ -> nil
      end
    end
    assert {:variable, _, "mk"} = find.(find, node)
  end
end
```

- [ ] **Step 2: Run it — expect FAIL** (after `mk <x: Code>`'s segments, `parse_macro_rule` expects `becomes` and hits `computed` → records `{:expected, :becomes, :got, :identifier, …}` → `Parser.parse` returns `{:error, …}`, so `parse!` raises for the first test).

Run: `mix test test/cure/compiler/macro_computed_test.exs` → FAIL.

- [ ] **Step 3: Split the verb branch in `parse_macro_rule/1`**

Replace the body after `{segments, state} = parse_rule_segments(state, [])` … through the `rule` map with a verb branch, and extract the two paths:

```elixir
  defp parse_macro_rule(state) do
    kw_token = peek(state)
    state = advance(state)

    keyword_token = peek(state)
    keyword = to_string(keyword_token.value)
    state = advance(state)

    {segments, state} = parse_rule_segments(state, [])

    case peek(state) do
      %Token{type: :identifier, value: "computed"} ->
        parse_computed_rule(state, kw_token, keyword, segments)

      _ ->
        parse_becomes_rule(state, kw_token, keyword, segments)
    end
  end

  # Tier-2: `becomes <template>` (unchanged behaviour, just extracted).
  defp parse_becomes_rule(state, kw_token, keyword, segments) do
    state =
      case peek(state) do
        %Token{type: :identifier, value: "becomes"} -> advance(state)
        t -> add_error(state, {:expected, :becomes, :got, t.type, t.line, t.col})
      end

    {template, state} = parse_expr(state, 0)
    {examples, state} = parse_rule_examples(state)

    rule = %{
      kind: :syntax,
      keyword: keyword,
      segments: segments,
      template: template,
      examples: examples,
      progress: nil,
      line: kw_token.line
    }

    {rule, state}
  end

  # Tier-3: `computed by <elab-fn>` (base design §3). Captures the elab
  # reference; running it is a later slice. NOT harvested into active_macros
  # (harvest filters kind: :syntax), so a computed macro's use-site is inert
  # until the execution slice lands.
  defp parse_computed_rule(state, kw_token, keyword, segments) do
    state = advance(state)  # `computed`

    state =
      case peek(state) do
        %Token{type: :identifier, value: "by"} -> advance(state)
        t -> add_error(state, {:expected, :by, :got, t.type, t.line, t.col})
      end

    {elab, state} = parse_expr(state, 0)
    {examples, state} = parse_rule_examples(state)

    rule = %{
      kind: :computed,
      keyword: keyword,
      segments: segments,
      elab: elab,
      examples: examples,
      progress: nil,
      line: kw_token.line
    }

    {rule, state}
  end
```

- [ ] **Step 4: Run the test — expect PASS**

Run: `mix test test/cure/compiler/macro_computed_test.exs` → PASS (all three).

- [ ] **Step 5: Full parser suite — no regression** (`becomes` path is byte-for-byte the same, just extracted; `:computed` is a new inert kind — confirm milestone-1/2, literal, hygiene, explain, example tests all pass).

Run: `mix test test/cure/compiler/` → all pass.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/compiler/parser.ex test/cure/compiler/macro_computed_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): parse Tier-3 `computed by` elab rules (SP2 Tier-3)"
```

---

## Slice boundary — the rest of Tier-3

This slice only *parses* `computed by`. A computed macro cannot expand yet. Remaining Tier-3 slices,
in dependency order:

- **Quoted-AST `Syntax` value model (§3)** — a Cure representation of the parsed input the elab receives
  (`quote` builds it, `$( )` splices), + the `Syntax` type in the stdlib.
- **Compile-time elab execution** — at a computed use-site: quote the matched input → run the elab function
  **staged on the host** (compile+load+call, or a compile-time evaluator) → splice its returned `Syntax` back
  as the expansion. Harvest `:computed` rules into `active_macros`; dispatch runs the elab. The elab's output
  is re-elaborated + kernel-checked (K3 firewall) — TCB delta stays zero. This is the big one.
- **`check … else fail C`** in elabs (§3.4) — ties Tier-3 to author-declared `Diagnosis` (`fail C`), folding
  into M1's exhaustiveness.
- **Example checking for `:computed` rules** — once the elab runs, `:computed` rules re-enter the M3
  presence/equality obligations (currently exempt).

Then the **wiring slice** (invoke M1/M3 checks + example kernel-check + `{:type}` pins in the compile
pipeline; pin SP1 macros). When all SP2 mechanisms land → SP2 Stage 6 → SP2 complete → SP3.
