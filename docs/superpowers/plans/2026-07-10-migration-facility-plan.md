# Migration Facility + `cure migrate` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a lossless, extensible source-migration facility to the Cure compiler — a rule registry with two consumers (`cure build` warn-and-tolerate; a new `cure migrate` command that rewrites files in place) built on a comment-preserving whole-file reprint.

**Architecture:** Approach A (whole-file canonical reprint). Make `Cure.Compiler.Printer` total over the AST; add a token-anchored **trivia** model (comments + blank-lines attached to AST-node `meta` by a single post-parse pass) so the Printer round-trips losslessly; add a `Cure.Migrate` rule registry; expose it via `cure build` (warn) and `cure migrate` (rewrite, gated by a git-clean guard + batch atomicity).

**Tech Stack:** Elixir (mix project `cure`), ExUnit tests, the existing hand-rolled Pratt `Cure.Compiler.{Lexer,Parser,Printer}`, `cli.ex` command dispatch, `git` shelled out via `System.cmd/3`.

## Global Constraints

- **Compiler is Elixir**; escript built via `mix escript.build`. Run tests with `mix test`.
- **Source of truth spec:** `docs/superpowers/specs/2026-07-10-migration-facility-implementation-design.md`. Every task's requirements implicitly include it.
- **Lossless is mandatory** — every comment survives a rewrite; an unplaced trivia item is a hard error, never a silent drop (spec §5.2).
- **AST shape is fixed:** Metastatic 3-tuples `{type, meta, children_or_value}`; `meta` is a keyword list. Trivia lives in `meta` under new keys (`:leading`, `:trailing`, `:trailer`) — **no tuple-shape change** (spec §4.2).
- **Blank-line policy (spec §5.4), fully opinionated:** top of file 0 blanks; bottom exactly 1; exactly 1 between top-level defs; inside a block cap runs at 1 and trim adjacent to open/close; normalization applies to statement lists only, not arbitrary expression spans (§5.4.5).
- **One registry, two consumers, identical per-file `ctx`** (spec §5.5): a rule fires in `cure build` warn-mode on exactly the inputs `cure migrate` rewrites.
- **Git discipline:** all work stays on branch `autopilot/migration-facility` in worktree `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/migration-facility`. Commit per task. **No co-authored-by trailer** (project rule: commits are the user's alone).
- **One build/test run at a time** — never launch concurrent `mix test` runs.
- **v1 scope note:** `cure fmt` keeps its existing Algebra formatter (`Cure.Compiler.Formatter.format_algebra`); this plan does NOT rewire `cure fmt` onto the trivia Printer. The trivia Printer powers `cure migrate` only. (Spec §4.1 names `cure fmt` as a *motivation* for Approach A; repointing it is a separate future change, consistent with §8 keeping scope tight.)

---

## File Structure

**New files:**
- `lib/cure/compiler/printer/unprintable_node_error.ex` — exception raised by the Printer catch-all (Phase 1).
- `lib/cure/compiler/trivia.ex` — `Cure.Compiler.Trivia`: post-parse trivia attachment pass + `carry/2` helper (Phase 2).
- `lib/cure/migrate.ex` — `Cure.Migrate`: registry, `run/2`, warning struct (Phase 3).
- `lib/cure/migrate/rule.ex` — `Cure.Migrate.Rule` struct (Phase 3).
- `lib/cure/migrate/rules/if_elif_to_pickup.ex` — first seed rule (Phase 3).
- `lib/cure/migrate/rules/uppercase_type_var.ex` — second seed rule (Phase 3).
- Tests: `test/cure/compiler/printer_totality_test.exs`, `test/cure/compiler/trivia_test.exs`, `test/cure/compiler/lossless_roundtrip_test.exs`, `test/cure/migrate/rule_registry_test.exs`, `test/cure/migrate/if_elif_to_pickup_test.exs`, `test/cure/migrate/uppercase_type_var_test.exs`, `test/cure/migrate/warn_tolerate_parity_test.exs`, `test/cure/cli/migrate_cli_test.exs`.
- Fixture: `test/fixtures/printer_totality.cure` — exercises every surface construct (Phase 1).

**Modified files:**
- `lib/cure/compiler/printer.ex` — raise-catch-all; missing node clauses; trivia emission.
- `lib/cure/compiler/lexer.ex` — lossless-mode trivia collection to a side list.
- `lib/cure/compiler/parser.ex` — expose collected trivia + per-node position spans needed by attachment (read-only additions; no grammar change).
- `lib/cure/cli.ex` — `["migrate" | paths]` dispatch + `cmd_migrate/2`; warn-and-tolerate hook in `compile_one/3` (after `Parser.parse`, cli.ex:749).

---

## Phase 1 — Printer totality

**Why first:** whole-file reprint is only safe if the Printer handles every node kind. Today the catch-all (`printer.ex:536`) silently `inspect`s unknown nodes → unparseable output (spec §3 Bug 1). This phase is independently valuable (fixes `cure.rewrite` reparse breakage).

### Task 1: Printer catch-all raises instead of `inspect`

**Files:**
- Create: `lib/cure/compiler/printer/unprintable_node_error.ex`
- Modify: `lib/cure/compiler/printer.ex:536-538`
- Test: `test/cure/compiler/printer_totality_test.exs`

**Interfaces:**
- Produces: `Cure.Compiler.Printer.UnprintableNodeError` (exception; fields `:node`), raised by `Printer.quoted_to_string/2` on an unhandled node kind.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/compiler/printer_totality_test.exs
defmodule Cure.Compiler.PrinterTotalityTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Printer
  alias Cure.Compiler.Printer.UnprintableNodeError

  test "an unhandled node kind raises loudly, never silently inspects" do
    # A synthetic node kind the Printer has no clause for.
    bogus = {:definitely_not_a_real_node_kind, [line: 1, col: 1], []}

    assert_raise UnprintableNodeError, fn ->
      Printer.quoted_to_string(bogus)
    end
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/compiler/printer_totality_test.exs`
Expected: FAIL — current catch-all returns `inspect(other)` (a string), so no error is raised.

- [ ] **Step 3: Create the exception module**

```elixir
# lib/cure/compiler/printer/unprintable_node_error.ex
defmodule Cure.Compiler.Printer.UnprintableNodeError do
  @moduledoc """
  Raised when `Cure.Compiler.Printer` is asked to render an AST node kind it
  has no clause for. Whole-file reprint (migration facility, Approach A)
  requires the Printer to be total; a silent `inspect` fallback used to emit
  unparseable output (spec §3 Bug 1). Failing loudly converts a future gap
  into an immediate crash at the first offending node.
  """
  defexception [:node]

  @impl true
  def message(%__MODULE__{node: node}) do
    kind =
      case node do
        {k, _meta, _} when is_atom(k) -> inspect(k)
        _ -> "non-tuple"
      end

    pos =
      case node do
        {_k, meta, _} when is_list(meta) ->
          " at line #{Keyword.get(meta, :line, "?")}, col #{Keyword.get(meta, :col, "?")}"

        _ ->
          ""
      end

    "Printer has no clause for AST node kind #{kind}#{pos}. " <>
      "Add a `to_string/3` clause in Cure.Compiler.Printer. Node: #{inspect(node)}"
  end
end
```

- [ ] **Step 4: Change the catch-all to raise**

In `lib/cure/compiler/printer.ex`, replace the fallback at lines 536-538:

```elixir
  defp to_string(other, _depth, _indent) do
    raise Cure.Compiler.Printer.UnprintableNodeError, node: other
  end
```

Keep the binary passthrough clause immediately above it (`defp to_string(other, _depth, _indent) when is_binary(other), do: other`) unchanged. Add an `alias` if the module prefers short names; a fully-qualified `raise` is fine.

- [ ] **Step 5: Run test to verify it passes**

Run: `mix test test/cure/compiler/printer_totality_test.exs`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add lib/cure/compiler/printer/unprintable_node_error.ex lib/cure/compiler/printer.ex test/cure/compiler/printer_totality_test.exs
git commit -m "feat(printer): raise on unprintable node kinds instead of inspecting"
```

### Task 2: Construct-complete fixture + exhaustiveness/round-trip gate (RED)

This gate is the falsifiable "total" claim (spec §5.3 point 2, §7). It parses a fixture that exercises every surface construct, and asserts `parse → print` (a) raises nowhere, (b) reparses, (c) is a print-fixpoint. It will be RED until Task 3 fills the missing clauses.

**Files:**
- Create: `test/fixtures/printer_totality.cure`
- Modify: `test/cure/compiler/printer_totality_test.exs`

**Interfaces:**
- Consumes: `Cure.Compiler.Lexer.tokenize/2`, `Cure.Compiler.Parser.parse/2`, `Printer.quoted_to_string/1`.

- [ ] **Step 1: Build the construct-complete fixture**

Create `test/fixtures/printer_totality.cure`. It must parse cleanly and, between it and the existing in-repo corpus, exercise every non-error surface node kind. Seed it from real constructs; grow it in Task 3 as the gate reports gaps. Minimum contents (add module/imports so it parses):

```cure
mod PrinterTotality

# A pin pattern, an as-pattern, a guard, a GADT/ctor, records, lambdas,
# interface/implementation, supervisor, dependent-type surface (pi/sigma),
# a hole, with-abstraction — one of each construct the parser can build.
# (Fill from lib/std examples; each construct added here is driven by the
#  gate in Step 3 reporting its node kind as unprinted.)

fn classify(n: Int) -> String =
  match n
    ^zero -> "zero"          # :pin
    x as whole -> "some"     # :as_pattern
    _ -> "other"
```

Note: the fixture is *grown by the Task-3 loop*. Start minimal; every time the gate in Step 3 raises `UnprintableNodeError` for a node kind, ensure a construct producing that kind is present here (or in the corpus) and add its Printer clause.

- [ ] **Step 2: Write the gate test (expected RED for now)**

Append to `test/cure/compiler/printer_totality_test.exs`:

```elixir
  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src, file) do
    {:ok, toks} = Lexer.tokenize(src, file: file, emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    ast
  end

  # Every non-error node kind the parser can construct in a *well-formed*
  # program. Error/diagnostic node kinds (produced only on parse failure)
  # are excluded — they never appear in a successfully parsed AST.
  @error_node_kinds ~w(
    error expected unexpected_token parser ok pickup_no_else pickup_else_not_last
    pickup_multiple_else lambda_block_unterminated with_multi_arity_mismatch
    named_implicit_not_in_pattern if_deprecated
  )a

  defp node_kinds(ast, acc \\ MapSet.new())
  defp node_kinds({k, _m, ch}, acc) when is_atom(k) and is_list(ch),
    do: Enum.reduce(ch, MapSet.put(acc, k), &node_kinds/2)
  defp node_kinds({k, _m, _v}, acc) when is_atom(k), do: MapSet.put(acc, k)
  defp node_kinds(l, acc) when is_list(l), do: Enum.reduce(l, acc, &node_kinds/2)
  defp node_kinds(_, acc), do: acc

  test "printer is total over the construct-complete fixture (no raise, reparses, fixpoint)" do
    file = "test/fixtures/printer_totality.cure"
    src = File.read!(file)
    ast = parse!(src, file)

    # (a) prints without raising UnprintableNodeError
    out1 = Cure.Compiler.Printer.quoted_to_string(ast)

    # (b) reparses
    ast2 = parse!(out1, file)

    # (c) print is a byte-fixpoint
    out2 = Cure.Compiler.Printer.quoted_to_string(ast2)
    assert out1 == out2
  end

  test "every surface node kind in the whole in-repo corpus prints without raising" do
    files = Path.wildcard("lib/**/*.cure") ++ Path.wildcard("examples/**/*.cure")

    for file <- files do
      src = File.read!(file)

      with {:ok, toks} <- Lexer.tokenize(src, file: file, emit_events: false),
           {:ok, ast} <- Parser.parse(toks, file: file, emit_events: false) do
        # Must not raise UnprintableNodeError for any node the corpus exercises.
        _ = Cure.Compiler.Printer.quoted_to_string(ast)
      end
    end
  end
```

- [ ] **Step 3: Run to verify it fails (surfacing the first missing clause)**

Run: `mix test test/cure/compiler/printer_totality_test.exs`
Expected: FAIL with `UnprintableNodeError` naming a node kind (e.g. `:pin`).

- [ ] **Step 4: Commit the RED gate**

```bash
git add test/cure/compiler/printer_totality_test.exs test/fixtures/printer_totality.cure
git commit -m "test(printer): construct-complete totality + corpus round-trip gate (red)"
```

### Task 3: Fill missing Printer clauses (TDD loop, one node kind per iteration)

Drive entirely by the Task-2 gate. The **known missing surface node kinds** (parser constructs them; Printer lacks a clause) are:

```
:pin :as_pattern :assert_type :ctor :gadt_ctor :indexed_type :interface
:implementation :named_dom :pi_type :sigma_type :supervisor :with_abs :hole
:forced_pattern :child_spec :on_phase :arrow_chain :named_implicit_pat
:keyword_variadic :variadic :binary_generator :param :type :positional
:string_part :expr
```

For **each** kind above (and any other the gate raises on), do this five-step cycle. `:pin` is worked in full as the template; repeat identically for the rest, deriving each node's shape from its construction site in `parser.ex` and its surface syntax from a real example in `lib/std/**` or `docs/`.

- [ ] **Step 1 (per kind): Write a round-trip unit test**

For `:pin` — add to `test/cure/compiler/printer_totality_test.exs`:

```elixir
  test "pin pattern round-trips as ^name" do
    src = """
    mod M
    fn f(t: Atom) -> Bool =
      match t
        ^target -> true
        _ -> false
    """

    ast = parse!(src, "pin.cure")
    out = Cure.Compiler.Printer.quoted_to_string(ast)
    assert out =~ "^target"
    # and it reparses
    assert _ = parse!(out, "pin.cure")
  end
```

- [ ] **Step 2 (per kind): Run to confirm RED**

Run: `mix test test/cure/compiler/printer_totality_test.exs -k "pin pattern"`
Expected: FAIL with `UnprintableNodeError` for `:pin`.

- [ ] **Step 3 (per kind): Find the node shape and add the clause**

Find the construction site: `grep -n "{:pin," lib/cure/compiler/parser.ex`. The pin node is `{:pin, meta, [inner_expr]}` where `inner_expr` is the pinned variable. Add a clause to `printer.ex` (place it near the other pattern clauses, before the fallback):

```elixir
  # -- Pin pattern -----------------------------------------------------------
  defp to_string({:pin, _meta, [inner]}, depth, indent) do
    "^" <> to_string(inner, depth, indent)
  end
```

For each other kind, the clause is analogous: read the parser construction site to learn the children layout, read a real source example to learn the surface syntax, write the clause. Do NOT guess — verify the shape against `parser.ex` and the surface against a `.cure` example.

- [ ] **Step 4 (per kind): Run to confirm GREEN**

Run: `mix test test/cure/compiler/printer_totality_test.exs`
Expected: the per-kind test passes; the gate advances to the next missing kind (or passes fully when none remain).

- [ ] **Step 5 (per kind): Commit**

```bash
git add lib/cure/compiler/printer.ex test/cure/compiler/printer_totality_test.exs test/fixtures/printer_totality.cure
git commit -m "feat(printer): render <kind> node to surface syntax"
```

- [ ] **Loop exit:** repeat Steps 1–5 until `mix test test/cure/compiler/printer_totality_test.exs` is fully green (both the fixture gate and the corpus gate). Then run the full suite once: `mix test`. Expected: green. Commit any incidental fixes.

---

## Phase 2 — Trivia model

Make comments + blank-lines survive a reprint (spec §5.2). Trivia is collected by the lexer, attached to AST nodes by a new pass, and emitted by the Printer.

### Task 4: Lexer collects positioned trivia to a side list

**Files:**
- Modify: `lib/cure/compiler/lexer.ex` (add lossless trivia collection alongside existing `preserve_comments`)
- Test: `test/cure/compiler/trivia_test.exs`

**Interfaces:**
- Produces: `Lexer.tokenize(src, file: f, trivia: true)` returns `{:ok, tokens, trivia}` where `trivia` is an ordered list of `{:comment, text, line, col} | {:doc_comment, text, line, col} | {:blank, count, line}`. When `trivia:` is absent/false, behavior is unchanged (`{:ok, tokens}`).

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/compiler/trivia_test.exs
defmodule Cure.Compiler.TriviaTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Lexer

  test "lexer collects every comment and blank run as positioned trivia" do
    src = """
    mod M

    # leading comment
    fn f() -> Int = 1  # trailing comment
    """

    {:ok, _tokens, trivia} = Lexer.tokenize(src, file: "t.cure", trivia: true)

    texts = for {:comment, t, _l, _c} <- trivia, do: String.trim(t)
    assert "leading comment" in texts
    assert "trailing comment" in texts
    assert Enum.any?(trivia, &match?({:blank, _, _}, &1))
  end
end
```

- [ ] **Step 2: Run to verify it fails**

Run: `mix test test/cure/compiler/trivia_test.exs`
Expected: FAIL — `tokenize/2` returns a 2-tuple, no `trivia` element.

- [ ] **Step 3: Implement trivia collection**

In `lib/cure/compiler/lexer.ex`: add a `trivia: false` option (mirroring `preserve_comments`). When `trivia: true`, accumulate every comment (`#`, `##`, `###`) and every run of blank lines into a `trivia` accumulator on the lexer state as positioned items (reuse the existing comment-emission sites at `lexer.ex:255,265,376,386,441`; the position is already known there). Track blank runs by counting consecutive newline-only lines. Return `{:ok, tokens, Enum.reverse(state.trivia)}` from the public `tokenize/2` when `trivia: true`; keep the existing `{:ok, tokens}` return otherwise. (Keep `preserve_comments` untouched for existing callers.)

- [ ] **Step 4: Run to verify it passes**

Run: `mix test test/cure/compiler/trivia_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/compiler/lexer.ex test/cure/compiler/trivia_test.exs
git commit -m "feat(lexer): collect positioned comment/blank trivia in trivia mode"
```

### Task 5: `Cure.Compiler.Trivia` attachment pass (total by construction)

**Files:**
- Create: `lib/cure/compiler/trivia.ex`
- Test: `test/cure/compiler/trivia_test.exs`

**Interfaces:**
- Produces: `Cure.Compiler.Trivia.attach(ast, trivia_list) :: ast` — returns the AST with each trivia item placed in a node's `meta[:leading]` / `meta[:trailing]` / `meta[:trailer]`. Raises `Cure.Compiler.Trivia.UnplacedTriviaError` (fields `:item`) if any item cannot be placed (spec §5.2 "total by construction").
- Produces: `Cure.Compiler.Trivia.carry(from_node, to_node) :: to_node` — moves `from_node`'s attached leading/trailing/trailer trivia onto `to_node` (for restructuring rules, spec §5.2).

Attachment rule (spec §5.2): an item on the **same line** as, and **after**, a node's last token → that node's `:trailing`. Otherwise → the `:leading` of the next node that starts at or after the item's line. An item after the last child of a container (program, block, branch body, fsm state) with no following sibling → that container's `:trailer`. Attach to the **innermost** enclosing container.

- [ ] **Step 1: Write the failing tests (incl. nested-block trailer + totality)**

```elixir
  # append to test/cure/compiler/trivia_test.exs
  alias Cure.Compiler.{Parser, Trivia}
  alias Cure.Compiler.Trivia.UnplacedTriviaError

  defp attach(src, file) do
    {:ok, toks, trivia} = Lexer.tokenize(src, file: file, trivia: true)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    Trivia.attach(ast, trivia)
  end

  test "leading comment attaches to the following definition" do
    ast = attach("mod M\n\n# doc\nfn f() -> Int = 1\n", "a.cure")
    leadings =
      ast |> collect_meta(:leading) |> List.flatten() |> Enum.map(&elem(&1, 1)) |> Enum.map(&String.trim/1)
    assert "doc" in leadings
  end

  test "comment after last statement of a nested block lands in that block's trailer" do
    src = """
    mod M
    fn f() -> Int =
      let x = 1
      x
      # nested trailer
    """
    ast = attach(src, "b.cure")
    trailers =
      ast |> collect_meta(:trailer) |> List.flatten() |> Enum.map(&elem(&1, 1)) |> Enum.map(&String.trim/1)
    assert "nested trailer" in trailers
  end

  test "attachment is total: an item that cannot be placed raises, never drops" do
    # A trivia item positioned beyond any node with an empty AST forces the
    # unplaced path.
    assert_raise UnplacedTriviaError, fn ->
      Trivia.attach({:block, [line: 1, col: 1], []}, [{:comment, "orphan", 99, 1}])
    end
  end

  # helper: collect all values of a given meta key across the AST
  defp collect_meta(ast, key, acc \\ [])
  defp collect_meta({_k, m, ch}, key, acc) when is_list(m) and is_list(ch) do
    acc = if v = Keyword.get(m, key), do: [v | acc], else: acc
    Enum.reduce(ch, acc, &collect_meta(&1, key, &2))
  end
  defp collect_meta({_k, m, _v}, key, acc) when is_list(m) do
    if v = Keyword.get(m, key), do: [v | acc], else: acc
  end
  defp collect_meta(l, key, acc) when is_list(l), do: Enum.reduce(l, acc, &collect_meta(&1, key, &2))
  defp collect_meta(_, _key, acc), do: acc
```

- [ ] **Step 2: Run to verify it fails**

Run: `mix test test/cure/compiler/trivia_test.exs`
Expected: FAIL — `Cure.Compiler.Trivia` does not exist.

- [ ] **Step 3: Implement the attachment pass**

Create `lib/cure/compiler/trivia.ex`. Implement `attach/2` as: (1) build a position index of nodes from the AST (each node's `meta` carries `line`/`col`; a node's span is from its first to last descendant position); (2) for each trivia item in source order, classify trailing vs leading vs container-trailer by the rule above; (3) place it, threading placement back into the node's `meta`; (4) track placed items in a set — after the walk, if any item is unplaced, `raise UnplacedTriviaError, item: item`. Also create the `UnplacedTriviaError` exception (define it in the same file or a sibling). Implement `carry/2` to move `:leading`/`:trailing`/`:trailer` keys from one node's meta to another's (concatenating if the target already has some).

- [ ] **Step 4: Run to verify it passes**

Run: `mix test test/cure/compiler/trivia_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/compiler/trivia.ex test/cure/compiler/trivia_test.exs
git commit -m "feat(trivia): total post-parse trivia attachment pass + carry helper"
```

### Task 6: Printer emits attached trivia + blank-line policy

**Files:**
- Modify: `lib/cure/compiler/printer.ex`
- Test: `test/cure/compiler/lossless_roundtrip_test.exs`

**Interfaces:**
- The Printer, when a node's `meta` carries `:leading`/`:trailing`/`:trailer`, emits them: `:leading` each on its own line at the node's indent before the node; `:trailing` as ` # …` after the node's line; a container's `:trailer` at the end of that container's body. Blank-line normalization per §5.4 is applied between statement-list entries.

- [ ] **Step 1: Write the failing lossless round-trip gate**

```elixir
# test/cure/compiler/lossless_roundtrip_test.exs
defmodule Cure.Compiler.LosslessRoundtripTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Trivia, Printer}

  defp comments(src) do
    src
    |> String.split("\n")
    |> Enum.flat_map(fn line ->
      case Regex.run(~r/#+\s?(.*)$/, line) do
        [_, txt] -> [String.trim(txt)]
        _ -> []
      end
    end)
    |> Enum.reject(&(&1 == ""))
    |> Enum.sort()
  end

  @corpus Path.wildcard("lib/std/*.cure")

  for file <- @corpus do
    @file file
    test "lossless round-trip preserves every comment: #{file}" do
      src = File.read!(@file)
      {:ok, toks, trivia} = Lexer.tokenize(src, file: @file, trivia: true)
      {:ok, ast} = Parser.parse(toks, file: @file, emit_events: false)
      out = ast |> Trivia.attach(trivia) |> Printer.quoted_to_string()

      # every comment present in the source is present in the output
      assert comments(src) -- comments(out) == []
      # and the output reparses
      assert {:ok, _} = Lexer.tokenize(out, file: @file, trivia: true) |> elem(0) |> then(fn _ -> Parser.parse(elem(Lexer.tokenize(out, file: @file), 1), file: @file, emit_events: false) end)
    end
  end
end
```

(Simplify the reparse assertion to a clean `parse!` helper as in earlier tasks; the intent is: output reparses.)

- [ ] **Step 2: Run to verify it fails**

Run: `mix test test/cure/compiler/lossless_roundtrip_test.exs`
Expected: FAIL — the Printer does not yet emit `:leading`/`:trailing`/`:trailer`, so comments are lost (this is the §3 measurement, now a gate).

- [ ] **Step 3: Implement trivia emission + blank-line policy**

In `printer.ex`: (1) at the start of rendering any node, if `meta[:leading]` is present, emit each leading item on its own line at the current indent; (2) after a node's line, if `meta[:trailing]` is present, append ` # text`; (3) in the container/statement-list join (`:block`, program body, branch bodies), after the last child emit `meta[:trailer]` items; (4) apply the §5.4 blank-line policy when joining statement-list entries (0 at top, exactly 1 between top-level defs, cap-at-1 inside blocks, exactly 1 trailing at EOF). Factor a small `render_leading/trailing/trailer` helper to avoid duplicating across clauses.

- [ ] **Step 4: Run to verify it passes**

Run: `mix test test/cure/compiler/lossless_roundtrip_test.exs`
Expected: PASS for the `lib/std/*.cure` corpus.

- [ ] **Step 5: Run the full suite once**

Run: `mix test`
Expected: green. Fix any Printer-output regressions in existing tests (e.g. `comment_preservation_test.exs`, `algebra_test.exs` are independent of the Printer path and should be unaffected; `bin_segment_test.exs` uses the Printer — verify).

- [ ] **Step 6: Commit**

```bash
git add lib/cure/compiler/printer.ex test/cure/compiler/lossless_roundtrip_test.exs
git commit -m "feat(printer): emit attached trivia and apply blank-line policy (lossless round-trip)"
```

---

## Phase 3 — Rule registry

One registry, two consumers (spec §5.5). Seed rules: `if/elif→pickup` and uppercase-type-var→lowercase.

### Task 7: `Cure.Migrate.Rule` struct + registry + ordered-fold `run/2`

**Files:**
- Create: `lib/cure/migrate/rule.ex`, `lib/cure/migrate.ex`
- Test: `test/cure/migrate/rule_registry_test.exs`

**Interfaces:**
- Produces: `%Cure.Migrate.Rule{id: atom, description: String.t, phase: :syntactic | :needs_resolution, detect_and_rewrite: (ast, ctx -> {:rewrite, ast} | :no_change), warning_template: String.t}`.
- Produces: `Cure.Migrate.rules() :: [Rule.t]` (declaration order).
- Produces: `Cure.Migrate.run(ast, opts) :: {ast, [warning]}` where `opts` carries `:file`; `ctx` is built from the AST alone (declared + imported type names); rules run once each as an ordered fold (spec §5.5); `warning` is `%Cure.Migrate.Warning{rule: atom, message: String.t, file: String.t, line: pos_integer}`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/migrate/rule_registry_test.exs
defmodule Cure.Migrate.RuleRegistryTest do
  use ExUnit.Case, async: true
  alias Cure.Migrate

  test "run threads rules as an ordered fold and returns warnings" do
    src = "mod M\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n"
    {:ok, toks} = Cure.Compiler.Lexer.tokenize(src, file: "r.cure", emit_events: false)
    {:ok, ast} = Cure.Compiler.Parser.parse(toks, file: "r.cure", emit_events: false)

    {new_ast, warnings} = Migrate.run(ast, file: "r.cure")

    # the if/elif rule rewrote the conditional to a pickup
    assert new_ast != ast
    assert Enum.any?(warnings, &(&1.rule == :W_if_elif_pickup))
  end
end
```

(Use the real rule id chosen in Task 8; adjust the assertion to match.)

- [ ] **Step 2: Run to verify it fails**

Run: `mix test test/cure/migrate/rule_registry_test.exs`
Expected: FAIL — `Cure.Migrate` does not exist.

- [ ] **Step 3: Implement the struct, registry, and `run/2`**

Create `lib/cure/migrate/rule.ex` (the struct + `@type`). Create `lib/cure/migrate.ex` with: `Warning` struct; `rules/0` returning the seed rules (Task 8/9 modules); `build_ctx/1` computing the per-file declared+imported type-name `MapSet` from the AST; `run/2` folding rules in order, each called with `(ast, ctx)`, collecting a warning (rendered from `warning_template`) whenever a rule returns `{:rewrite, _}`. `run/2` returns `{final_ast, warnings}`.

- [ ] **Step 4: Run to verify it passes** — `mix test test/cure/migrate/rule_registry_test.exs` → PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/migrate.ex lib/cure/migrate/rule.ex test/cure/migrate/rule_registry_test.exs
git commit -m "feat(migrate): rule struct + registry + ordered-fold run/2 with per-file ctx"
```

### Task 8: Port `if/elif → pickup` rule (with paren-context fix)

**Files:**
- Create: `lib/cure/migrate/rules/if_elif_to_pickup.ex`
- Test: `test/cure/migrate/if_elif_to_pickup_test.exs`

**Interfaces:**
- Consumes: the rewrite logic in `lib/mix/tasks/cure.rewrite.ex` (`rewrite/1`, `conditional_to_pickup/3`, `do_chain/4`).
- Produces: `Cure.Migrate.Rules.IfElifToPickup.rule() :: Rule.t` with `id: :W_if_elif_pickup`, `phase: :syntactic`.

Spec §5.5 requires resolving the known parenthesised-context reparse bug: a `{:conditional, …}` embedded inside a call-argument list must NOT be rewritten (skip it — still emit the warning), because a multi-line `pickup` block cannot live inside a paren context and would fail to reparse.

- [ ] **Step 1: Write failing tests (rewrite happy-path, comment preservation, paren-skip)**

```elixir
# test/cure/migrate/if_elif_to_pickup_test.exs
defmodule Cure.Migrate.IfElifToPickupTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Trivia, Printer}
  alias Cure.Migrate

  defp migrate(src, file) do
    {:ok, toks, trivia} = Lexer.tokenize(src, file: file, trivia: true)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    {new_ast, warns} = Migrate.run(Trivia.attach(ast, trivia), file: file)
    {Printer.quoted_to_string(new_ast), warns}
  end

  test "top-level if/else rewrites to pickup and reparses" do
    {out, _} = migrate("mod M\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n", "a.cure")
    assert out =~ "pickup"
    assert {:ok, _} = Lexer.tokenize(out, file: "a.cure")
  end

  test "comments on branches survive the restructuring rewrite" do
    src = "mod M\nfn f(x: Int) -> Int =\n  if x > 0 then\n    1  # positive\n  else\n    2  # non-positive\n"
    {out, _} = migrate(src, "b.cure")
    assert out =~ "positive"
    assert out =~ "non-positive"
  end

  test "conditional inside a call-argument list is NOT rewritten (paren-context), still warns" do
    src = "mod M\nfn g(x: Int) -> Int = h(if x > 0 then 1 else 2)\n"
    {out, warns} = migrate(src, "c.cure")
    refute out =~ "pickup"
    assert Enum.any?(warns, &(&1.rule == :W_if_elif_pickup))
    assert {:ok, _} = Lexer.tokenize(out, file: "c.cure")
  end
end
```

- [ ] **Step 2: Run to verify it fails** — `mix test test/cure/migrate/if_elif_to_pickup_test.exs` → FAIL (module missing).

- [ ] **Step 3: Implement the rule**

Create `lib/cure/migrate/rules/if_elif_to_pickup.ex`. Port `cure.rewrite`'s `rewrite/1`/`conditional_to_pickup/3`/`do_chain/4`. Add a paren-context guard: track whether a `{:conditional, …}` is a descendant of a `{:function_call, …}` argument (or other paren context); if so, do NOT rewrite that conditional (leave it, still returning `{:rewrite, …}` at the top level only when at least one non-paren conditional changed — but for a purely-paren-embedded conditional, return `:no_change` for the rewrite yet still surface the warning). Use `Trivia.carry/2` when replacing a `{:conditional}` node with a `{:pickup}` node so branch comments travel. Register `rule/0` in `Cure.Migrate.rules/0`.

- [ ] **Step 4: Run to verify it passes** — `mix test test/cure/migrate/if_elif_to_pickup_test.exs` → PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/migrate/rules/if_elif_to_pickup.ex lib/cure/migrate.ex test/cure/migrate/if_elif_to_pickup_test.exs
git commit -m "feat(migrate): if/elif->pickup rule with paren-context skip and comment carry"
```

### Task 9: Uppercase-type-var → lowercase rule

**Files:**
- Create: `lib/cure/migrate/rules/uppercase_type_var.ex`
- Test: `test/cure/migrate/uppercase_type_var_test.exs`

**Interfaces:**
- Produces: `Cure.Migrate.Rules.UppercaseTypeVar.rule() :: Rule.t` with `id: :W_uppercase_type_var`, `phase: :needs_resolution`.

Detection (spec §5.5): a *free* uppercase identifier in a type-parameter position that does NOT resolve to a known type constructor (consult `ctx`, the declared+imported type-name set). Lowercase the binder consistently across the signature. On a `T`+`t` collision, freshen with the smallest unused numeric suffix (`t` → `t1` → `t2`), recursively checked; never silently merge.

- [ ] **Step 1: Write failing tests (basic rename, ctx-respecting non-rename, T+t collision)**

```elixir
# test/cure/migrate/uppercase_type_var_test.exs
defmodule Cure.Migrate.UppercaseTypeVarTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Printer}
  alias Cure.Migrate

  defp migrate(src, file) do
    {:ok, toks} = Lexer.tokenize(src, file: file, emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    {new_ast, warns} = Migrate.run(ast, file: file)
    {Printer.quoted_to_string(new_ast), warns}
  end

  test "free uppercase type var is lowercased across the signature" do
    {out, warns} = migrate("mod M\nfn id(x: T) -> T = x\n", "a.cure")
    assert out =~ "x: t"
    assert out =~ "-> t"
    refute out =~ "T"
    assert Enum.any?(warns, &(&1.rule == :W_uppercase_type_var))
  end

  test "an uppercase name that resolves to a declared type is left alone" do
    {out, _} = migrate("mod M\ntype Foo = Int\nfn f(x: Foo) -> Foo = x\n", "b.cure")
    assert out =~ "Foo"
  end

  test "T and t in the same signature freshen rather than merge" do
    {out, _} = migrate("mod M\nfn f(x: T, y: t) -> T = x\n", "c.cure")
    # the freshened T binder does not collapse onto the existing t
    assert out =~ "t1"
  end
end
```

- [ ] **Step 2: Run to verify it fails** — `mix test test/cure/migrate/uppercase_type_var_test.exs` → FAIL (module missing).

- [ ] **Step 3: Implement the rule** — create the module; walk type-annotation positions; use `ctx` to distinguish free vars from known constructors; apply the consistent lowercase + freshen-on-collision scheme; register in `rules/0`.

- [ ] **Step 4: Run to verify it passes** — `mix test test/cure/migrate/uppercase_type_var_test.exs` → PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/migrate/rules/uppercase_type_var.ex lib/cure/migrate.ex test/cure/migrate/uppercase_type_var_test.exs
git commit -m "feat(migrate): uppercase-type-var->lowercase rule with ctx resolution and freshening"
```

### Task 10: `cure build` warn-and-tolerate consumer + parity test

**Files:**
- Modify: `lib/cure/cli.ex` (`compile_one/3`, after `Parser.parse` at cli.ex:749)
- Test: `test/cure/migrate/warn_tolerate_parity_test.exs`

**Interfaces:**
- Consumes: `Cure.Migrate.run/2`.
- Effect: `cure build`/`compile` runs `Migrate.run/2` on the parsed AST, prints each warning to stderr, and continues compiling with the tolerated (rewritten-in-memory) AST — the file is not modified.

- [ ] **Step 1: Write the failing parity test**

```elixir
# test/cure/migrate/warn_tolerate_parity_test.exs
defmodule Cure.Migrate.WarnTolerateParityTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Migrate

  # The set of rules that fire (warn) equals the set that rewrite: same
  # per-file ctx, same detect_and_rewrite. Assert identical fired-rule sets.
  test "warn-mode fires on exactly the inputs rewrite-mode changes" do
    src = "mod M\nfn id(x: T) -> T = if x_len(x) > 0 then 1 else 2\n"
    {:ok, toks} = Lexer.tokenize(src, file: "p.cure", emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: "p.cure", emit_events: false)

    {rewritten, warnings} = Migrate.run(ast, file: "p.cure")
    fired = warnings |> Enum.map(& &1.rule) |> Enum.sort()

    # rewrite happened iff a rule fired
    assert (rewritten != ast) == (fired != [])
    # both seed rules fired for this input
    assert :W_if_elif_pickup in fired
    assert :W_uppercase_type_var in fired
  end
end
```

- [ ] **Step 2: Run to verify it fails / passes at unit level** — `mix test test/cure/migrate/warn_tolerate_parity_test.exs`. (This asserts the registry-level parity; it should pass once Tasks 7–9 are done. If it passes immediately, that's correct — the parity is structural. Keep it as a regression guard.)

- [ ] **Step 3: Wire the build hook**

In `lib/cure/cli.ex`, in `compile_one/3` immediately after the `Parser.parse` success at line 749, insert:

```elixir
{ast, migrate_warnings} = Cure.Migrate.run(ast, file: path)
Enum.each(migrate_warnings, fn w ->
  IO.warn("#{w.file}:#{w.line}: #{w.message}", [])
end)
```

so compilation proceeds on the tolerated `ast`. (Match the surrounding `with` style; if `ast` is bound in a `with` clause, rebind in the body.)

- [ ] **Step 4: Run the full suite once** — `mix test`. Expected: green (no existing program regresses; warnings are informational).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/cli.ex test/cure/migrate/warn_tolerate_parity_test.exs
git commit -m "feat(migrate): cure build warn-and-tolerate consumer + parity guard"
```

---

## Phase 4 — `cure migrate` CLI + policy + git guard

### Task 11: Git-safety guard (preflight, precise cleanliness)

**Files:**
- Modify: `lib/cure/migrate.ex` (add `git_guard/1`)
- Test: `test/cure/cli/migrate_cli_test.exs`

**Interfaces:**
- Produces: `Cure.Migrate.git_guard(paths) :: :ok | {:error, {:dirty | :untracked | :not_a_repo, [path]}}`. Clean = `git status --porcelain -- <path>` yields empty output; tracked = `git ls-files --error-unmatch <path>` exits 0. Runs as a preflight over the whole set.

- [ ] **Step 1: Write failing tests using a temp git repo fixture**

```elixir
# test/cure/cli/migrate_cli_test.exs
defmodule Cure.Cli.MigrateCliTest do
  use ExUnit.Case, async: false
  alias Cure.Migrate

  setup do
    dir = Path.join(System.tmp_dir!(), "curemig_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    {_, 0} = System.cmd("git", ["init", "-q", dir])
    {_, 0} = System.cmd("git", ["-C", dir, "config", "user.email", "t@t"])
    {_, 0} = System.cmd("git", ["-C", dir, "config", "user.name", "t"])
    on_exit(fn -> File.rm_rf!(dir) end)
    {:ok, dir: dir}
  end

  test "untracked file is rejected", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\n")
    assert {:error, {:untracked, [^f]}} = Migrate.git_guard([f])
  end

  test "dirty (uncommitted) tracked file is rejected", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    File.write!(f, "mod A\n# changed\n")
    assert {:error, {:dirty, [^f]}} = Migrate.git_guard([f])
  end

  test "staged-only change (index dirty, no worktree diff) is still rejected", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    File.write!(f, "mod A\n# staged\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    assert {:error, {:dirty, [^f]}} = Migrate.git_guard([f])
  end

  test "clean tracked file passes", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    assert :ok = Migrate.git_guard([f])
  end
end
```

- [ ] **Step 2: Run to verify it fails** — `mix test test/cure/cli/migrate_cli_test.exs` → FAIL (`git_guard/1` missing).

- [ ] **Step 3: Implement `git_guard/1`** — for each path: `git ls-files --error-unmatch` (untracked → collect), then `git status --porcelain -- <path>` (non-empty → dirty). Return `:ok` only if all clean+tracked; else `{:error, {reason, paths}}`. Handle non-repo (git error) as `{:error, {:not_a_repo, paths}}`.

- [ ] **Step 4: Run to verify it passes** — `mix test test/cure/cli/migrate_cli_test.exs` → PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/migrate.ex test/cure/cli/migrate_cli_test.exs
git commit -m "feat(migrate): git-safety preflight guard (tracked + porcelain-clean)"
```

### Task 12: `cure migrate` command — in-place / `--check` / `--print` / `--strict` + batch atomicity

**Files:**
- Modify: `lib/cure/cli.ex` (dispatch `["migrate" | paths]`; add `cmd_migrate/2`)
- Test: `test/cure/cli/migrate_cli_test.exs`

**Interfaces:**
- Consumes: `Cure.Migrate.run/2`, `Cure.Migrate.git_guard/1`, `Trivia.attach/2`, `Printer.quoted_to_string/1`.
- Produces: `cmd_migrate(paths, opts)`. Default: rewrite in place (git-guarded). `--check`: list pending files, non-zero exit, no write. `--print`: stdout, no write. `--strict`: migration warnings become errors (non-zero exit). Target selection mirrors `cmd_fmt/2` (explicit paths, else `lib/**/*.cure` + `test/**/*.cure`). Batch atomicity (spec §5.8): run the full `lex→parse→attach→run→print→reparse-and-comment-check` in memory for **all** files first; only if every file passes does it write any; on any failure, write nothing and report the failing file(s).

- [ ] **Step 1: Write failing CLI-level tests**

```elixir
  # append to test/cure/cli/migrate_cli_test.exs
  alias Cure.Cli

  test "in-place migrate rewrites a clean tracked file and reparses", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])

    Cli.cmd_migrate([f], [])   # expose cmd_migrate or call the public entry with ["migrate", f]

    out = File.read!(f)
    assert out =~ "pickup"
  end

  test "batch atomicity: if one file fails, zero files are written", %{dir: dir} do
    good = Path.join(dir, "good.cure")
    bad = Path.join(dir, "bad.cure")
    File.write!(good, "mod G\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n")
    File.write!(bad, "mod B\nthis is not valid cure @@@\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "."])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])

    before_good = File.read!(good)
    _ = Cli.cmd_migrate([good, bad], [])
    # good is untouched because bad failed the in-memory preflight
    assert File.read!(good) == before_good
  end
```

(If `cmd_migrate/2` is private, test via the public `Cli.main(["migrate", f])` entry, or make `cmd_migrate/2` public. Prefer routing through `main/1` to test real dispatch.)

- [ ] **Step 2: Run to verify it fails** — `mix test test/cure/cli/migrate_cli_test.exs` → FAIL.

- [ ] **Step 3: Implement dispatch + `cmd_migrate/2`**

Add to the `cli.ex` command `case` (near the `["fmt" | paths]` arm, ~line 135): `["migrate" | paths] -> cmd_migrate(paths, opts)`. Ensure `migrate` opts include `check`, `print`, `strict` in the `OptionParser` switches (~cli.ex:35). Implement `cmd_migrate/2`: resolve targets (mirror `cmd_fmt/2`); unless `--check`/`--print`, run `git_guard/1` and abort on `{:error, …}` with a clear message; run the in-memory batch preflight for all files (lex→parse→attach→`Migrate.run`→print→reparse+comment-count check); if `--strict` and any warnings, exit non-zero; if any file fails preflight, report and exit non-zero writing nothing; else apply the mode (`--check` list + non-zero if pending; `--print` stdout; default write-all).

- [ ] **Step 4: Run to verify it passes** — `mix test test/cure/cli/migrate_cli_test.exs` → PASS.

- [ ] **Step 5: Run the full suite once** — `mix test`. Expected: green.

- [ ] **Step 6: Commit**

```bash
git add lib/cure/cli.ex test/cure/cli/migrate_cli_test.exs
git commit -m "feat(cli): cure migrate command with check/print/strict and batch atomicity"
```

### Task 13: Retire `mix cure.rewrite` in favor of the registry (optional cleanup)

**Files:**
- Modify: `lib/mix/tasks/cure.rewrite.ex` (delegate to `Cure.Migrate` or deprecate)

- [ ] **Step 1:** Add a moduledoc deprecation note pointing to `cure migrate`; make `mix cure.rewrite` delegate to `Cure.Migrate.run/2` for the `if/elif` rule so there is a single implementation (DRY). Keep its CLI surface for back-compat.
- [ ] **Step 2:** Run `mix test` once. Expected: green.
- [ ] **Step 3:** Commit: `git commit -am "refactor(migrate): route mix cure.rewrite through the shared registry"`.

---

## Self-Review

**Spec coverage:**
- §5.2 trivia model → Tasks 4–6. §5.3 Printer totality (raise catch-all + exhaustiveness + corpus gate) → Tasks 1–3. §5.4 blank-line policy → Task 6. §5.5 registry + two seed rules (incl. paren-context fix, T+t freshening) → Tasks 7–10. §5.6 CLI → Task 12. §5.7 git guard → Task 11. §5.8 batch atomicity → Task 12. §7 gates → Tasks 2, 3, 6, 10, 11, 12. §8 out-of-scope respected (no `cure fmt` rewire; one global `--strict`).
- **Known plan-shape caveat:** Task 3 is a TDD *loop* over ~25 node kinds rather than a fixed step count. This is deliberate — the exact per-node clause code depends on each node's shape in `parser.ex`, which the implementer verifies at the construction site. The method and one full worked example (`:pin`) are given; the loop's exit condition (both gates green) is concrete and falsifiable.

**Placeholder scan:** No "TBD"/"handle edge cases"/"similar to Task N". Task 3's per-kind steps are a genuine repeated TDD cycle with a worked example, not a placeholder.

**Type consistency:** `Cure.Migrate.run/2` → `{ast, [warning]}` used consistently in Tasks 7, 8, 9, 10, 12. `Rule` fields (`id`, `phase`, `detect_and_rewrite`, `warning_template`) consistent between Task 7 definition and Tasks 8/9 producers. `Trivia.attach/2` + `carry/2` and `git_guard/1` signatures consistent across producer and consumer tasks. Rule ids `:W_if_elif_pickup` / `:W_uppercase_type_var` consistent across Tasks 8/9/10.
