# SP2 Tier-3 slice 2 — `Std.Syntax` value + reflection bridge — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (autopilot Stage 4). Steps use `- [ ]`. Strict red-green TDD; commit per task. Second Tier-3 slice (the value model). Grounded by `docs/superpowers/specs/2026-07-12-tier3-computed-by-execution-design.md`.

**Goal:** Build the **generic `Syntax` value model** an elab function operates on, and the **reflection bridge** that converts a parser AST to/from it losslessly. This is the substrate for slice 3 (compile-time elab execution). NO execution here — just the type + a round-tripping reflection.

**Architecture:** Per the Tier-3 execution design note (Decision B): a single generic `Std.Syntax` ADT reflecting the parser's `{tag, meta, third}` node shape (typed per-category records are a deferred ergonomic layer). Two halves: **(1)** `Std.Syntax` in the stdlib (the value type the elab pattern-matches); **(2)** an Elixir bridge `Cure.Compiler.MacroSyntax.to_syntax/1` + `from_syntax/1` over an Elixir mirror repr, proven lossless by round-trip. Slice 3 connects the repr to actual Core values of `Std.Syntax` and runs the elab. **TCB delta zero** (a stdlib type + a frontend support module; no `lib/cure/core/*`).

**Tech Stack:** Cure (`lib/std/syntax.cure`); Elixir (`lib/cure/compiler/macro_syntax.ex`); ExUnit.

## Global Constraints

- **TCB delta ZERO.** `lib/std/*.cure` + `lib/cure/compiler/*` (+ tests) only. No `lib/cure/core/*`, no `lib/cure/elab/*`.
- **Ghost commits** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no Co-Authored-By. `git add -- <path>`, never `-A`.
- **One build at a time.** Scoped test files; `mix test test/cure/stdlib/ test/cure/compiler/` for regression.
- **Run mix from the worktree root** (`.claude/worktrees/core-let-binder`), NEVER the parent clone.
- **Tests immutable once green.**

## Verified grounding (probed live)

- **Meta is load-bearing (design flaw in the note's sketch, corrected here):** semantic info lives in a node's META, not just tag/children — `{:function_call, [name: "g", …], [args]}` (name in meta), `{:binary_op, [operator: :+, …], […]}` (operator), `{:literal, [subtype: :integer, …], 5}` (subtype). So `Syntax` MUST carry an `attrs` field or reflection loses function names/operators. Positions (`:line`/`:col`) may drop (K3 re-elaborates the expansion — design note §3).
- Parser node shape: `{tag :: atom, meta :: keyword, third}` where `third` is a **list of child nodes** (`:binary_op`, `:function_call`, `:list`, `:tuple`, `:block`, `:hole`→`[]`, …) OR a **scalar** (`:literal` → int/float/string/bool/atom/char; `:variable` → string name).
- **Exotic shapes to scope out (probed via the M3 `expand_example` crash work):** a `:regex` value is a `{body, flags}` TUPLE, a `:string_interpolation` value is a LIST of parts — neither a clean child-list nor a scalar-lit. This slice's bridge covers the common shapes and represents an unrecognised `third` opaquely (`SOpaque`), losslessly enough to round-trip without crashing; faithful regex/interpolation reflection is a later refinement.
- Stdlib ADT pattern (`lib/std/json.cure` `type Value`): `type Name = | Ctor | Ctor(FieldType, …)` inside `mod Std.X`, `@group(:x)` header, `use Std.String`/etc. for referenced types. `Node(Atom, List(Attr), List(Syntax))` nests the family in `List`'s (strictly-positive) parameter — the SAME nested-positivity `Std.Json`'s `Arr(List(Value))` already proves the kernel accepts.
- Elaborates-test pattern (`test/cure/stdlib/json_elaborates_test.exs`): `assert {:ok, _env} = Program.elaborate(File.read!("lib/std/<mod>.cure"))`.

## The `Std.Syntax` ADT

```cure
type Syntax =
  | Node(Atom, List(Attr), List(Syntax))   # {tag, meta, [children]}
  | Leaf(Atom, List(Attr), SynLit)         # {tag, meta, scalar}
type Attr = KV(Atom, SynLit)               # one semantic meta entry (name/operator/subtype/…)
type SynLit =
  | SInt(Int)
  | SFloat(Float)
  | SStr(String)
  | SBool(Bool)
  | SAtom(Atom)
  | SOpaque                                # unrepresentable/exotic value (regex/interp) — placeholder
```

Elixir mirror repr (bridge-side, slice-2 only; slice 3 maps it to Core values):
`{:syn_node, tag, [{k, synlit}], [repr]}` / `{:syn_leaf, tag, [{k, synlit}], synlit}`,
`synlit` ∈ `{:s_int,n}|{:s_float,f}|{:s_str,s}|{:s_bool,b}|{:s_atom,a}|:s_opaque`.

---

### Task 1: `Std.Syntax` stdlib type

**Files:**
- Create: `lib/std/syntax.cure`
- Test: `test/cure/stdlib/syntax_elaborates_test.exs`

**Interfaces:**
- Produces the `Syntax` / `Attr` / `SynLit` types (consumed by slice 3's elab machinery). No functions this slice.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/stdlib/syntax_elaborates_test.exs
defmodule Cure.Stdlib.SyntaxElaboratesTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "Std.Syntax elaborates on the dependent pipeline" do
    assert {:ok, _env} = Program.elaborate(File.read!("lib/std/syntax.cure"))
  end
end
```

- [ ] **Step 2: Run it — expect FAIL** (`lib/std/syntax.cure` does not exist → `File.read!` raises).

Run: `mix test test/cure/stdlib/syntax_elaborates_test.exs` → FAIL.

- [ ] **Step 3: Write `lib/std/syntax.cure`**

```cure
@group(:syntax)
mod Std.Syntax
  ## The generic quoted-AST value a Tier-3 `computed by` elab receives and
  ## returns (macro-facility design §3, generic layer). Reflects the parser's
  ## `{tag, meta, third}` node: `Node` for a child list, `Leaf` for a scalar.
  ## `attrs` carries the semantic meta (a function's name, an operator, a
  ## literal's subtype) — dropping it would lose those. Source positions are
  ## not represented (the expansion is re-elaborated, K3 firewall).
  use Std.String

  type Syntax =
    | Node(Atom, List(Attr), List(Syntax))
    | Leaf(Atom, List(Attr), SynLit)

  type Attr = KV(Atom, SynLit)

  type SynLit =
    | SInt(Int)
    | SFloat(Float)
    | SStr(String)
    | SBool(Bool)
    | SAtom(Atom)
    | SOpaque
```

- [ ] **Step 4: Run the test — expect PASS**

Run: `mix test test/cure/stdlib/syntax_elaborates_test.exs` → PASS. (If a nested-positivity or missing-import error appears, mirror `Std.Json`'s fix — add the needed `use Std.*` and confirm the `List(Syntax)`/`List(Attr)` nesting matches `Json`'s proven `Arr(List(Value))` shape; do NOT touch `lib/cure/core/*`.)

- [ ] **Step 5: Stdlib regression — the new module doesn't break the stdlib build**

Run: `mix test test/cure/stdlib/` → all pass (the new `Std.Syntax` compiles cleanly alongside the rest).

- [ ] **Step 6: Commit**

```bash
git add -- lib/std/syntax.cure test/cure/stdlib/syntax_elaborates_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(std): Std.Syntax generic quoted-AST value type (SP2 Tier-3)"
```

---

### Task 2: `to_syntax` / `from_syntax` reflection bridge (lossless round-trip)

**Files:**
- Create: `lib/cure/compiler/macro_syntax.ex`
- Test: `test/cure/compiler/macro_syntax_test.exs`

**Interfaces:**
- `Cure.Compiler.MacroSyntax.to_syntax(parser_ast) :: repr` and `from_syntax(repr) :: parser_ast`, where `repr` is the Elixir mirror above. `from_syntax(to_syntax(ast))` equals `ast` up to `:line`/`:col` (proven by `strip_pos/1`).

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/compiler/macro_syntax_test.exs
defmodule Cure.Compiler.MacroSyntaxTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, MacroSyntax}

  # Parse the RHS of `fn f() = <expr>` to get a real expression AST.
  defp expr!(src) do
    {:ok, tokens} = Lexer.tokenize("fn f() = #{src}\n", emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    find = fn find, n ->
      case n do
        {:function_def, _, [body]} -> body
        {_t, _m, ch} when is_list(ch) -> Enum.find_value(ch, &find.(find, &1))
        _ -> nil
      end
    end
    find.(find, ast)
  end

  # Recursively drop :line/:col so round-trip equality is position-insensitive.
  defp strip(t) when is_list(t), do: Enum.reject(t, &match?({k, _} when k in [:line, :col], &1)) |> Enum.map(&strip/1)
  defp strip(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.map(&strip/1) |> List.to_tuple()
  defp strip(t), do: t

  test "to_syntax builds a Node/Leaf repr preserving tag + semantic attrs" do
    ast = expr!("g(1, x)")
    # {:function_call, [name: "g", ...], [{:literal,_,1}, {:variable,_,"x"}]}
    repr = MacroSyntax.to_syntax(ast)
    assert {:syn_node, :function_call, attrs, [arg1, arg2]} = repr
    assert {:name, {:s_str, "g"}} in attrs
    assert {:syn_leaf, :literal, _, {:s_int, 1}} = arg1
    assert {:syn_leaf, :variable, _, {:s_str, "x"}} = arg2
  end

  test "from_syntax(to_syntax(ast)) round-trips up to source position" do
    for src <- ["g(1, x + 2)", "[1, 2, 3]", "\"hi\"", ":ok", "true", "3.5", "f()"] do
      ast = expr!(src)
      assert strip(MacroSyntax.from_syntax(MacroSyntax.to_syntax(ast))) == strip(ast),
             "round-trip failed for #{src}"
    end
  end

  test "an exotic third element (regex tuple) reflects opaquely without crashing" do
    ast = expr!("~r/foo/")
    repr = MacroSyntax.to_syntax(ast)
    assert {:syn_leaf, :regex, _, :s_opaque} = repr
    # round-trips to a regex leaf (value not faithfully recovered — opaque this slice)
    assert {:regex, _, _} = MacroSyntax.from_syntax(repr)
  end
end
```

- [ ] **Step 2: Run it — expect FAIL** (`Cure.Compiler.MacroSyntax` undefined).

Run: `mix test test/cure/compiler/macro_syntax_test.exs` → FAIL.

- [ ] **Step 3: Write `lib/cure/compiler/macro_syntax.ex`**

```elixir
# lib/cure/compiler/macro_syntax.ex
defmodule Cure.Compiler.MacroSyntax do
  @moduledoc """
  Reflection bridge between the parser AST and the generic `Std.Syntax` value a
  Tier-3 `computed by` elab operates on (macro-facility design §3). TCB delta
  zero — pure frontend reflection; the elab's output is re-elaborated + kernel
  checked (K3 firewall). This slice handles the Elixir mirror repr; slice 3
  maps it to Core values of `Std.Syntax` and runs the elab.
  """

  @type synlit ::
          {:s_int, integer} | {:s_float, float} | {:s_str, String.t()}
          | {:s_bool, boolean} | {:s_atom, atom} | :s_opaque
  @type repr ::
          {:syn_node, atom, [{atom, synlit}], [repr]}
          | {:syn_leaf, atom, [{atom, synlit}], synlit}

  # -- to_syntax: parser AST -> repr -----------------------------------------

  @spec to_syntax(tuple()) :: repr
  def to_syntax({tag, meta, third}) when is_list(third) do
    {:syn_node, tag, attrs(meta), Enum.map(third, &to_syntax/1)}
  end

  def to_syntax({tag, meta, scalar}) do
    {:syn_leaf, tag, attrs(meta), synlit(scalar)}
  end

  # A node whose semantic meta carries values; drop line/col, keep the rest as
  # {key, synlit}. Unrepresentable meta values become :s_opaque.
  defp attrs(meta) when is_list(meta) do
    for {k, v} <- meta, k not in [:line, :col], do: {k, synlit(v)}
  end

  defp attrs(_), do: []

  defp synlit(v) when is_integer(v), do: {:s_int, v}
  defp synlit(v) when is_float(v), do: {:s_float, v}
  defp synlit(v) when is_binary(v), do: {:s_str, v}
  defp synlit(v) when is_boolean(v), do: {:s_bool, v}
  defp synlit(v) when is_atom(v), do: {:s_atom, v}
  defp synlit(_), do: :s_opaque

  # -- from_syntax: repr -> parser AST ---------------------------------------

  @spec from_syntax(repr) :: tuple()
  def from_syntax({:syn_node, tag, attrs, kids}) do
    {tag, from_attrs(attrs), Enum.map(kids, &from_syntax/1)}
  end

  def from_syntax({:syn_leaf, tag, attrs, lit}) do
    {tag, from_attrs(attrs), from_synlit(lit)}
  end

  defp from_attrs(attrs), do: for({k, lit} <- attrs, do: {k, from_synlit(lit)})

  defp from_synlit({:s_int, n}), do: n
  defp from_synlit({:s_float, f}), do: f
  defp from_synlit({:s_str, s}), do: s
  defp from_synlit({:s_bool, b}), do: b
  defp from_synlit({:s_atom, a}), do: a
  defp from_synlit(:s_opaque), do: nil
end
```

Note on the regex round-trip test: `~r/foo/`'s value is a `{body, flags}` tuple → `synlit` returns `:s_opaque`; `from_synlit(:s_opaque)` → `nil`, so `from_syntax` yields `{:regex, [], nil}` — round-trips to a regex leaf (structure), value not recovered. This is the honest opaque behaviour (faithful regex reflection deferred). The round-trip test asserts only the `{:regex, _, _}` shape, not value fidelity.

- [ ] **Step 4: Run the test — expect PASS**

Run: `mix test test/cure/compiler/macro_syntax_test.exs` → PASS (all three).

- [ ] **Step 5: Full regression + warnings**

Run: `mix test test/cure/compiler/ test/cure/stdlib/` → all pass. Then `mix compile --warnings-as-errors --force` → clean.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/compiler/macro_syntax.ex test/cure/compiler/macro_syntax_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(macros): to_syntax/from_syntax reflection bridge, lossless round-trip (SP2 Tier-3)"
```

---

## Slice boundary — what slice 3 (execution) adds

This slice delivers the `Syntax` value model: the `Std.Syntax` type + a lossless parser-AST↔repr
reflection. It does NOT run any elab. Slice 3 (the big one):

- **Connect the Elixir repr to Core values** of `Std.Syntax` — build the `Node`/`Leaf`/`SynLit`
  constructor Core terms from a `to_syntax` repr, and read a normal-form `Syntax` value back via
  `from_syntax`.
- **Harvest `:computed` rules + emit `{:computed_use}`** at use-sites (reversing slice-1's total
  inertness).
- **The elaboration-time expansion pass** — elaborate the elab, `normalise(app(elab, syntax_input))`,
  `from_syntax`, splice, re-elaborate (K3 firewall). End-to-end: a `computed by` macro expands.

Then `quote`/`$()` sugar, `check … else fail C`, typed per-category records (deferred), and the wiring
slice. When all SP2 mechanisms land → SP2 Stage 6 → SP2 complete → SP3.
