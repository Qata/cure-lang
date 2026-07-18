defmodule Cure.Compiler.ArgumentLabelsParseTest do
  @moduledoc """
  Surface syntax for Swift-style argument labels (Ph2 of the
  overloading-and-argument-labels design). Two shapes:

  - Two-name DECL binder `fn f(to dest: T)` — the first identifier is the
    EXTERNAL label (caller-facing), the second the INTERNAL binder (body-facing).
    The label rides in the param node's meta under `:label`; the child name stays
    the internal binder.
  - Labelled CALL argument `f(to: v)` — the written labels ride in the
    `{:function_call, …}` meta under `:arg_labels`, a list position-aligned with
    the argument list (`nil` where an argument is unlabelled). The argument
    expressions themselves are unchanged, so positional elaboration is untouched.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  test "two-name declaration binder carries the external label in param meta" do
    {:function_def, meta, _body} = parse!("fn move(to dest: Point) -> Point = dest")
    assert [{:param, pmeta, "dest"}] = Keyword.get(meta, :params)
    assert Keyword.get(pmeta, :label) == "to"
    # The internal binder name and its type are unchanged.
    assert {:variable, _, "Point"} = Keyword.get(pmeta, :type)
  end

  test "single-name declaration binder has no external label" do
    {:function_def, meta, _body} = parse!("fn f(x: Int) -> Int = x")
    assert [{:param, pmeta, "x"}] = Keyword.get(meta, :params)
    assert Keyword.get(pmeta, :label) == nil
  end

  test "labelled call argument rides in function_call meta arg_labels" do
    {:function_call, meta, args} = parse!("move(to: p, from: q)")
    assert Keyword.get(meta, :arg_labels) == ["to", "from"]
    # Argument expressions are the plain values, unchanged.
    assert [{:variable, _, "p"}, {:variable, _, "q"}] = args
  end

  test "a mix of labelled and positional args aligns labels by position with nil" do
    {:function_call, meta, args} = parse!("g(1, to: p)")
    assert Keyword.get(meta, :arg_labels) == [nil, "to"]
    assert [{:literal, _, 1}, {:variable, _, "p"}] = args
  end

  test "an all-positional call carries no arg_labels key" do
    {:function_call, meta, _args} = parse!("h(a, b)")
    assert Keyword.get(meta, :arg_labels) == nil
  end
end
