defmodule Cure.MetaAST.MetadataInvarianceTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program
  alias Cure.MetaAST.{Metadata, SourceDecorator}

  test "recursive source decoration preserves an accepted program verdict and semantics" do
    source = "mod Invariance\n  fn id(x: Int) -> Int = x\n"
    {ast, decorated} = parse_pair(source)

    assert Metadata.semantic_equal?(ast, Metadata.strip_diagnostics(decorated))
    assert {:ok, _env} = Program.check_ast(ast)
    assert {:ok, _env} = Program.check_ast(decorated)
  end

  test "recursive source decoration preserves a rejected program category" do
    source = "mod InvarianceReject\n  fn bad() -> Int = missing_name\n"
    {ast, decorated} = parse_pair(source)

    assert {:error, original} = Program.check_ast(ast)
    assert {:error, decorated_error} = Program.check_ast(decorated)
    assert Program.semantic_error(original) |> error_head() == error_head(Program.semantic_error(decorated_error))
  end

  defp parse_pair(source) do
    assert {:ok, tokens} = Lexer.tokenize(source, file: "invariance.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "invariance.cure", emit_events: false)
    {ast, SourceDecorator.decorate(ast)}
  end

  defp error_head({tag, _rest}) when is_atom(tag), do: tag
  defp error_head({tag, _, _}) when is_atom(tag), do: tag
  defp error_head(other), do: other
end
