defmodule Cure.Compiler.ProofChainTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser, Printer, SourceSpans}
  alias Cure.MetaAST.{Metadata, SourceInfo}

  defp parse!(source) do
    assert {:ok, tokens} = Lexer.tokenize(source, file: "chain.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "chain.cure", emit_events: false)
    ast
  end

  @chain """
  proof chain
    first
      == second
      because first_step

    _ == third
      because second_step
  """

  test "proof chain has dedicated first/step AST nodes and complete source roles" do
    assert {:proof_chain, meta, [first, step1, step2]} = parse!(@chain)
    assert {:variable, _, "first"} = first

    for step <- [step1, step2] do
      assert {:proof_step, step_meta, [{:proof_chain_previous, _, []}, {:variable, _, _}, {:variable, _, _}]} = step
      assert %SourceInfo{whole: whole, operator: relation, body: because_body} = Metadata.source_info(step_meta)
      assert whole && relation && because_body
    end

    assert %SourceInfo{whole: whole, body: first_span} = Metadata.source_info(meta)
    assert whole && first_span
  end

  test "canonical printing is stable and preserves proof chain vocabulary" do
    ast = parse!(@chain)
    printed = Printer.quoted_to_string(ast)

    assert printed == String.trim_trailing(@chain)

    assert SourceSpans.strip_diagnostic_meta(parse!(printed)) ==
             SourceSpans.strip_diagnostic_meta(ast)
  end

  test "proof and chain remain ordinary identifiers outside the distinctive block head" do
    assert {:function_def, meta, [{:variable, _, "proof"}]} =
             parse!("fn keep(proof: Int, chain: Int) -> Int = proof\n")

    assert [{:param, _, "proof"}, {:param, _, "chain"}] = meta[:params]
  end

  test "empty and malformed chains are rejected" do
    for source <- [
          "proof chain\n",
          "proof chain\n  first\n",
          "proof chain\n  first\n    == second\n",
          "proof chain\n  first\n    second because proof\n"
        ] do
      case Lexer.tokenize(source, emit_events: false) do
        {:ok, tokens} -> assert {:error, _} = Parser.parse(tokens, emit_events: false)
        {:error, _} -> :ok
      end
    end
  end
end
