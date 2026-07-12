# SP1 T4 — Tier-1 `literal` Rules (units) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (autopilot Stage 4). Steps use `- [ ]`. Strict red-green TDD; commit per task. Builds on milestone 2 (keyword-triggered `syntax` rules) + T7 (`<fresh>`).

**Goal:** Add the design's Tier-1 `literal` rule (base §111-113, §194): `literal <n: Number> ms becomes Duration.ms(n)`, so a use-site `500ms` expands to `Duration.ms(500)`. This is the `units`-style macro the SP1 gate requires ("a Tier-1 … macro compiles, expands").

**Architecture:** **Parser-only, no lexer change** — probed live: `500ms` already tokenizes `[integer: 500, identifier: "ms"]` (and `500 ms` identically; whitespace is dropped, so juxtaposition = token-adjacency). A `literal` rule is structurally a leading number-hole + a `{:lit, suffix}` segment — the exact shape `parse_rule_segments/2` already produces — but unlike keyword-triggered `syntax` rules it dispatches on a **number** use-site followed by a registered suffix. Harvest indexes literal rules by suffix in a new `literal_macros` state map; `parse_prefix/1`'s `:integer`/`:float` cases consult it. Expansion reuses `match_segments`/`expand_rule` (so `<fresh>` + hole substitution + the T8 soundness firewall all apply). **TCB delta zero.**

**Tech Stack:** Elixir; `lib/cure/compiler/parser.ex`; ExUnit.

## Global Constraints

- **TCB delta ZERO.** Only `lib/cure/compiler/parser.ex` (+ tests). No `lib/cure/core/*`, no `lib/cure/lexer` change.
- **Ghost commits** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no Co-Authored-By. `git add -- <path>`, never `-A`.
- **One build at a time.** Scoped `mix test test/cure/compiler/macro_literal_test.exs`; `mix test test/cure/compiler/` for regression.
- **Run mix from the worktree root** (`.claude/worktrees/core-let-binder`), NEVER the parent clone.
- **Tests immutable once green.**

## Verified grounding (probed live)

- `500ms` → `[integer: 500, identifier: "ms"]`; `2s` → `[integer: 2, identifier: "s"]`; `3.5s` → `[float: 3.5, identifier: "s"]`; `500 ms` identical to `500ms`. **No lexer change.**
- `parse_macro_rules/2` (`parser.ex:4184`) dispatches ONLY on `%Token{type: :identifier, value: "syntax"}` → `parse_macro_rule/1` (`:4202`); anything else records `{:expected, :syntax_rule, …}`. Add a `"literal"` clause.
- `parse_macro_rule/1` (`:4202`) consumes the rule-kind word, then a **keyword** (2nd token), then `parse_rule_segments/2` (`:4234`, already parses `<n: Number>` holes + `{:lit, w}` literals), then `becomes`, then `parse_expr(state, 0)`. Rule = `%{kind: :syntax, keyword, segments, template, progress, line}`. A `literal` rule has NO keyword — it parses segments directly after the `literal` word.
- Expansion: `parse_macro_use/2` (`:155`) → `match_segments/4` (binds holes / matches `{:lit}`) → `expand_rule/3` (`freshen` then `subst_holes`). Parser state `defstruct` at `:45` (`[…, active_macros: %{}, fresh_counter: 0]`). `harvest_active_macros/1` + `collect_macro_defs/1` index `syntax` rules by `rule.keyword`.
- `parse_prefix/1`'s `:integer`/`:float` cases (`:386-390`) currently do `{literal(:integer, token), advance(state)}` with no lookahead.

## Scope note

T4 covers the design exemplar shape: **one leading number-hole + one literal suffix** (`literal <n: Number> ms becomes …`). Multi-suffix or hole-after-suffix literal rules are out of scope (no design driver). The hole's declared kind (`Number`) is carried but not enforced here — kind-checking is the elaborator's job after expansion (the T8 firewall guarantees the expansion is re-checked). Registered-suffix collision (two literal rules same suffix) uses first-wins like `syntax` multi-rule; a diagnostic is the error-floor task (next), not T4.

---

### Task 1: Parse `literal <hole> <suffix> becomes <template>` rules

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (`parse_macro_rules/2` at `:4184`; add `parse_literal_rule/1`, `literal_suffix/1`)
- Test: `test/cure/compiler/macro_literal_test.exs` (create)

**Interfaces:**
- Produces a rule map `%{kind: :literal, keyword: nil, segments: [{:hole,…}, {:lit, suffix} | …], suffix: String.t() | nil, template, progress: nil, line}`. Consumed by Task 2's harvest/dispatch.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/compiler/macro_literal_test.exs
defmodule Cure.Compiler.MacroLiteralTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  test "a literal rule parses to a :literal-kind rule with a hole, a suffix, and a template" do
    node = parse!("macro Dur\n  literal <n: Number> ms becomes Duration.ms(n)\n")
    assert {:macro_def, _meta, [rule]} = node
    assert rule.kind == :literal
    assert rule.suffix == "ms"
    assert [{:hole, %{name: "n", kind: "Number"}}, {:lit, "ms"}] = rule.segments
    assert {:function_call, _, _} = rule.template
  end
end
```

- [ ] **Step 2: Run it — expect FAIL** (`parse_macro_rules` records `{:expected, :syntax_rule, …}` on the `literal` line, so `Parser.parse` returns `{:error, …}` and `{:ok, ast} =` raises).

Run: `mix test test/cure/compiler/macro_literal_test.exs` → FAIL.

- [ ] **Step 3: Add the `literal` rule-kind clause + parser**

In `parse_macro_rules/2` (`:4184`), add a clause before the `other ->` fallback:

```elixir
      %Token{type: :identifier, value: "literal"} ->
        {rule, state} = parse_literal_rule(state)
        parse_macro_rules(state, [rule | acc])
```

Add `parse_literal_rule/1` + `literal_suffix/1` next to `parse_macro_rule/1`:

```elixir
  # `literal <n: Number> ms becomes <template>` — a Tier-1 units rule (base
  # §111). Unlike `syntax`, there is NO leading keyword; the rule is triggered
  # at a use-site by a NUMBER followed by the suffix (Task 2). Segments reuse
  # parse_rule_segments (a leading number-hole + a `{:lit, suffix}`).
  defp parse_literal_rule(state) do
    kw_token = peek(state)
    state = advance(state)

    {segments, state} = parse_rule_segments(state, [])

    state =
      case peek(state) do
        %Token{type: :identifier, value: "becomes"} -> advance(state)
        t -> add_error(state, {:expected, :becomes, :got, t.type, t.line, t.col})
      end

    {template, state} = parse_expr(state, 0)

    rule = %{
      kind: :literal,
      keyword: nil,
      segments: segments,
      suffix: literal_suffix(segments),
      template: template,
      progress: nil,
      line: kw_token.line
    }

    {rule, state}
  end

  # The dispatch suffix is the first literal segment following the leading
  # number-hole (`[{:hole,_}, {:lit, s} | _]`). A malformed literal rule
  # (no hole-then-lit prefix) has no suffix and is un-triggerable (harvest
  # skips it, Task 2); T4 does not diagnose that (error-floor task).
  defp literal_suffix([{:hole, _}, {:lit, s} | _]), do: s
  defp literal_suffix(_), do: nil
```

- [ ] **Step 4: Run the test — expect PASS**

Run: `mix test test/cure/compiler/macro_literal_test.exs` → PASS.

- [ ] **Step 5: Full parser suite — no regression** (the `syntax` path and all existing macro tests are untouched; `literal` was previously an error).

Run: `mix test test/cure/compiler/` → all pass.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/compiler/parser.ex test/cure/compiler/macro_literal_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): parse Tier-1 literal <hole> <suffix> becomes rules (SP1 T4)"
```

---

### Task 2: Harvest literal rules by suffix + dispatch a number use-site

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (defstruct `:45`; `parse/2` harvest; `harvest_active_macros/1`; `parse_prefix/1` `:integer`/`:float` at `:386`; add `maybe_literal_macro/2`, `expand_literal_rule/3`)
- Test: `test/cure/compiler/macro_literal_test.exs` (extend)

**Interfaces:**
- Adds `literal_macros: %{suffix :: String.t() => [rule]}` to parser state, seeded by the harvest pass alongside `active_macros`.
- `maybe_literal_macro(state, num)` — called after a number literal is read (state already advanced past it); if the next token is a registered suffix, expands the literal rule, else returns `{num, state}`.

- [ ] **Step 1: Write the failing test**

```elixir
  test "a number use-site with a registered suffix expands the literal rule" do
    node =
      parse!(
        "macro Dur\n  literal <n: Number> ms becomes Duration.ms(n)\n\nfn f() -> Int = 500ms\n"
      )
    body = find_fn_body(node, "f")
    # 500ms  ==>  Duration.ms(500)
    assert {:function_call, meta, [arg]} = body
    assert Keyword.get(meta, :name) in ["Duration.ms", "ms"]
    assert {:literal, _, 500} = arg
  end

  test "a bare number without a registered suffix is unaffected" do
    node = parse!("fn f() -> Int = 500\n")
    body = find_fn_body(node, "f")
    assert {:literal, _, 500} = body
  end

  defp find_fn_body({:function_def, meta, [body]}, name),
    do: if(to_string(Keyword.get(meta, :name)) == name, do: body)
  defp find_fn_body({_t, _m, ch}, name) when is_list(ch), do: Enum.find_value(ch, &find_fn_body(&1, name))
  defp find_fn_body(_, _), do: nil
```

Note: the two macro+fn top-level forms are separated by a blank line so the `macro` block's dedent closes before `fn` (mirrors the milestone-2 tests' structure — confirm the exact top-level shape by running; the `find_fn_body` walker tolerates a `{:block, …}` wrapper if `parse/2` wraps the two forms).

- [ ] **Step 2: Run it — expect FAIL** (first test: `500ms` parses as a bare `{:literal, _, 500}` then a stray `{:variable, _, "ms"}`, so `body` is not a `Duration.ms` call. Second test passes already — it is the regression guard.)

Run: `mix test test/cure/compiler/macro_literal_test.exs` → the suffix test FAILs.

- [ ] **Step 3: Add the literal_macros index + number dispatch**

Add `literal_macros: %{}` to the defstruct (`:45`):

```elixir
  defstruct [:tokens, :file, pos: 0, errors: [], emit_events: false, active_macros: %{}, fresh_counter: 0, literal_macros: %{}]
```

In `parse/2` (both harvest→seed and authoritative), seed `literal_macros` from the same harvested defs. Change `harvest_active_macros/1` to return BOTH maps, and thread the literal one onto state. Simplest: add a sibling `harvest_literal_macros/1` and set both fields:

```elixir
    active = harvest_active_macros(harvest_exprs)
    literal = harvest_literal_macros(harvest_exprs)

    state = %__MODULE__{
      tokens: tokens, file: file, emit_events: emit?,
      active_macros: active, literal_macros: literal
    }
```

(Apply the same two fields wherever the authoritative `state` is built in `parse/2`.) Add the harvester (mirrors `harvest_active_macros/1` but for `:literal` rules keyed by suffix, skipping suffix-less malformed rules):

```elixir
  defp harvest_literal_macros(exprs) do
    exprs
    |> collect_macro_defs()
    |> Enum.reduce(%{}, fn {:macro_def, _meta, rules}, acc ->
      Enum.reduce(rules, acc, fn
        %{kind: :literal, suffix: s} = rule when is_binary(s) ->
          Map.update(acc, s, [rule], &(&1 ++ [rule]))

        _ ->
          acc
      end)
    end)
  end
```

Guard `harvest_active_macros/1` so it only indexes `syntax` rules (literal rules have `keyword: nil`):

```elixir
  defp harvest_active_macros(exprs) do
    exprs
    |> collect_macro_defs()
    |> Enum.reduce(%{}, fn {:macro_def, _meta, rules}, acc ->
      Enum.reduce(rules, acc, fn
        %{kind: :syntax, keyword: kw} = rule when is_binary(kw) ->
          Map.update(acc, kw, [rule], &(&1 ++ [rule]))

        _ ->
          acc
      end)
    end)
  end
```

Dispatch in `parse_prefix/1`'s `:integer`/`:float` cases (`:386-390`):

```elixir
      :integer ->
        maybe_literal_macro(advance(state), literal(:integer, token))

      :float ->
        maybe_literal_macro(advance(state), literal(:float, token))
```

Add the dispatch + expansion helpers (near `parse_macro_use/2`):

```elixir
  # After a number literal is read (state already past it), check whether the
  # next token is a registered literal-rule suffix; if so, expand that rule with
  # the number bound to its leading hole. Otherwise return the plain number.
  defp maybe_literal_macro(state, num) do
    case peek(state) do
      %Token{type: :identifier, value: suffix} ->
        case Map.fetch(state.literal_macros, suffix) do
          {:ok, [rule | _]} -> expand_literal_rule(rule, num, state)
          :error -> {num, state}
        end

      _ ->
        {num, state}
    end
  end

  # Bind the already-read number to the rule's leading hole, then match the
  # remaining segments (the suffix, consumed here) and expand. Reuses
  # match_segments/expand_rule so <fresh> + hole-subst + the soundness firewall
  # all apply identically to keyword-triggered rules.
  defp expand_literal_rule(rule, num, state) do
    [{:hole, %{name: hole_name}} | rest] = rule.segments

    case match_segments(state, rest, %{hole_name => num}, 1) do
      {:ok, bindings, _progress, state} ->
        expand_rule(rule, bindings, state)

      {:error, _progress, state} ->
        # Suffix present but trailing segments didn't match: yield the plain
        # number, leaving the suffix token for normal parsing.
        {num, state}
    end
  end
```

- [ ] **Step 4: Run the tests — expect PASS**

Run: `mix test test/cure/compiler/macro_literal_test.exs` → PASS (both suffix expansion and bare-number regression).

- [ ] **Step 5: Full parser suite — no regression** (numbers not followed by a registered suffix are unchanged; `literal_macros` is empty for all existing code). Also confirm milestone-2 + T7 macro tests still pass:

Run: `mix test test/cure/compiler/` → all pass.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/compiler/parser.ex test/cure/compiler/macro_literal_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): dispatch + expand Tier-1 literal units at number use-sites (SP1 T4)"
```

---

## Task boundary + what remains in SP1

T4 delivers the Tier-1 `literal` units rule — with Tier-2 `syntax` (done), the SP1 gate's "a Tier-1 AND a Tier-2 macro compile+expand+kernel-check" is met (kernel-check is guarded by the T8 firewall, which covers literal expansions too since they route through the same `expand_rule`).

**Remaining SP1 scope** (subsequent Stage-2 rounds, program-doc order):
- **Error-machinery floor (§2):** wrong-arity / unknown-suffix / unknown-category macro uses must produce a *diagnostic* (a default-machinery error, not a raw `:macro_use_mismatch`/`:expected` parser error). Gate-required.
- **T9 — import scoping + same-keyword conflict (§7) + two-pass name resolution (§6):** cross-module macros. The hard architectural piece (parser must locate+parse imported modules for their grammars).
- **T7b — automatic hygiene** + the fresh∩hole-name and backtick-spoof gaps + `<capture>`.

When all SP1 scope is executed + code-reviewed, run SP1's Stage 6 (full `mix test`), update the state file, and start **SP2**.
