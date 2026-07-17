defmodule Cure.Compiler.ContextualKeywordTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  test "proof is lexed as an identifier" do
    assert {:ok, [token | _]} = Lexer.tokenize("proof", emit_events: false)
    assert token.type == :identifier
    assert token.value == "proof"
    assert :proof in Lexer.contextual_keywords()
  end

  test "proof still introduces a proof container at a declaration-shaped head" do
    source = "proof Laws\n  fn reflexive(x: Int) -> Equivalent(Int, x, x) = reflexive(x)\n"

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:container, meta, _body}} = Parser.parse(tokens, emit_events: false)
    assert meta[:container_type] == :proof
    assert meta[:name] == "Laws"
  end

  test "proof remains an ordinary parameter and value" do
    source = "fn keep(proof: Int) -> Int = proof\n"

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:function_def, meta, [body]}} = Parser.parse(tokens, emit_events: false)
    assert [{:param, _, "proof"}] = meta[:params]
    assert {:variable, _, "proof"} = body
  end
end
