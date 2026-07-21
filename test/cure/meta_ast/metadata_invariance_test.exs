defmodule Cure.MetaAST.MetadataInvarianceTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Emit, Erase, Program}
  alias Cure.MetaAST.{Metadata, SourceDecorator}

  test "recursive source decoration preserves an accepted program verdict and semantics" do
    source = "mod Invariance\n  fn id(x: Int) -> Int = x\n"
    {ast, decorated} = parse_pair(source)
    stripped = Metadata.strip_diagnostics(decorated)

    assert Metadata.semantic_equal?(ast, stripped)
    assert {:ok, plain_env} = Program.check_ast(ast)
    assert {:ok, decorated_env} = Program.check_ast(decorated)
    assert {:ok, stripped_env} = Program.check_ast(stripped)
    assert plain_env == decorated_env
    assert plain_env == stripped_env

    module = Program.module_atom(ast)

    function =
      Enum.find_value(plain_env.defs, fn {_key, %{name: name}} ->
        if String.ends_with?(to_string(name), "#id"), do: name
      end)

    assert function
    assert {:ok, plain_forms} = Emit.compile_forms(plain_env, module, [function])
    assert {:ok, decorated_forms} = Emit.compile_forms(decorated_env, module, [function])
    assert {:ok, stripped_forms} = Emit.compile_forms(stripped_env, module, [function])
    assert plain_forms == decorated_forms
    assert plain_forms == stripped_forms

    plain_def =
      Enum.find_value(plain_env.defs, fn {_key, %{name: name} = definition} -> if name == function, do: definition end)

    decorated_def =
      Enum.find_value(decorated_env.defs, fn {_key, %{name: name} = definition} ->
        if name == function, do: definition
      end)

    stripped_def =
      Enum.find_value(stripped_env.defs, fn {_key, %{name: name} = definition} ->
        if name == function, do: definition
      end)

    assert Erase.erase(plain_env, plain_def.body) == Erase.erase(decorated_env, decorated_def.body)
    assert Erase.erase(plain_env, plain_def.body) == Erase.erase(stripped_env, stripped_def.body)
  end

  test "recursive source decoration preserves a rejected program category" do
    source = "mod InvarianceReject\n  fn bad() -> Int = missing_name\n"
    {ast, decorated} = parse_pair(source)
    stripped = Metadata.strip_diagnostics(decorated)

    assert {:error, original} = Program.check_ast(ast)
    assert {:error, decorated_error} = Program.check_ast(decorated)
    assert {:error, stripped_error} = Program.check_ast(stripped)

    assert Program.semantic_error(original) |> error_head() ==
             error_head(Program.semantic_error(decorated_error))

    assert Program.semantic_error(original) |> error_head() ==
             error_head(Program.semantic_error(stripped_error))
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
