defmodule Cure.Compiler.WithParseTest do
  @moduledoc """
  `with`-abstraction (capability A) surface parsing. `with` is a CONTEXTUAL
  keyword: it is a with-abstraction only in expression-prefix position; its
  existing FSM/actor payload-binder identifier use is unaffected.
  """
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    Parser.parse(toks, emit_events: false)
  end

  # Collect every {tag, meta, children} 3-tuple in the AST.
  defp collect(node, acc) do
    acc = if is_tuple(node) and tuple_size(node) == 3, do: [node | acc], else: acc

    cond do
      is_tuple(node) -> Enum.reduce(Tuple.to_list(node), acc, &collect/2)
      is_list(node) -> Enum.reduce(node, acc, &collect/2)
      true -> acc
    end
  end

  test "block-form `with e <arms>` parses to a :with_abs node" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      fn foo(n: Nat) -> Nat =
        with n
          Z() -> Z()
          S(k) -> S(k)
    """

    assert {:ok, ast} = parse(src)

    node =
      collect(ast, [])
      |> Enum.find(fn t -> match?({:with_abs, _, [_ | _]}, t) end)

    assert {:with_abs, _meta, [scrut | arms]} = node
    assert {:variable, _, "n"} = scrut
    assert length(arms) == 2
    assert Enum.all?(arms, &match?({:match_arm, _, [_]}, &1))
  end

  # Regression: `with` is still the FSM/actor payload-binder identifier.
  test "`actor Name with Payload` still parses (with-abstraction is contextual)" do
    src = """
    actor Counter with 0
      on_message
        (:inc, n) -> n + 1
    """

    assert {:ok, ast} = parse(src)

    node =
      collect(ast, [])
      |> Enum.find(fn t -> match?({:container, _, _}, t) end)

    assert {:container, meta, _body} = node
    assert Keyword.get(meta, :container_type) == :actor
    # The payload came from the `with 0` clause.
    assert {:literal, lit_meta, 0} = Keyword.get(meta, :init)
    assert Keyword.get(lit_meta, :subtype) == :integer
  end
end
