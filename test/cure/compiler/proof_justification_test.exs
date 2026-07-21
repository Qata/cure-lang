defmodule Cure.Compiler.ProofJustificationTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser, Printer, SourceSpans}
  alias Cure.MetaAST.{Metadata, SourceInfo}

  @source """
  proof chain
    x == x
    because
      have fact: Equivalent(Int, x, x) = reflexive(x)
      fact
  """

  defp parse!(source) do
    assert {:ok, tokens} = Lexer.tokenize(source, file: "because.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "because.cure", emit_events: false)
    ast
  end

  test "multiline because has a dedicated statement-list node and complete range" do
    assert {:proof_chain, _, [_, {:proof_step, _, [_, _, justification]}]} = parse!(@source)
    assert {:proof_justification, meta, [have, {:variable, _, "fact"}]} = justification
    assert {:assignment, have_meta, _} = have
    assert have_meta[:have]
    assert %SourceInfo{whole: whole, body: body} = Metadata.source_info(meta)
    assert whole && body
  end

  test "formatter emits the canonical compact proposition layout and round-trips" do
    ast = parse!(@source)
    printed = Printer.quoted_to_string(ast)
    assert printed == String.trim_trailing(@source)

    assert SourceSpans.strip_diagnostic_meta(parse!(printed)) ==
             SourceSpans.strip_diagnostic_meta(ast)
  end

  test "directed rewrite commands parse, retain selectors, and print canonically" do
    source = """
    proof chain
      x == y
      because
        rewrite using forward_proof
        rewrite backwards using reverse_proof at 2
        rewrite using local_proof in hypothesis
        final_proof
    """

    assert {:proof_chain, _, [_, {:proof_step, _, [_, _, {:proof_justification, _, statements}]}]} =
             ast = parse!(source)

    assert [forward_command, backward_command, local_command, {:variable, _, "final_proof"}] = statements
    assert {:rewrite_command, forward, [_]} = forward_command
    assert {:rewrite_command, backward, [_]} = backward_command
    assert {:rewrite_command, local, [_]} = local_command

    assert forward[:direction] == :forward and forward[:target] == :goal
    assert backward[:direction] == :backwards and backward[:target] == {:at, 2}
    assert local[:direction] == :forward and local[:target] == {:in, "hypothesis"}

    assert Enum.all?(
             [forward, backward, local],
             &match?(%SourceInfo{whole: %Cure.Diagnostic.Span{}}, Metadata.source_info(&1))
           )

    printed = Printer.quoted_to_string(ast)
    assert printed == String.trim_trailing(source)
    assert SourceSpans.strip_diagnostic_meta(parse!(printed)) == SourceSpans.strip_diagnostic_meta(ast)
  end
end
