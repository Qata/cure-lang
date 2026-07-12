defmodule Cure.Compiler.MacroReducerTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.MacroReducer
  alias Cure.Core.{Context, Eval}
  alias Cure.Elab.{Elaborator, Program}

  test "builds a complete constructor reducer and the elaborator accepts it" do
    assert {:ok, env} = Program.elaborate("mod M\n  type Flag = Off | On\n")

    scrutinee = {:variable, [scope: :local], "flag"}

    assert {:ok, ast} =
             MacroReducer.build_match(
               "Flag",
               scrutinee,
               [
                 %{constructor: :Off, body: {:literal, [subtype: :integer], 0}},
                 %{constructor: :On, body: {:literal, [subtype: :integer], 1}}
               ],
               env
             )

    flag_type = Eval.eval({:data, :Flag, [], []}, env)
    ctx = Context.extend(Context.empty(env), flag_type)
    assert {:ok, _term, {:vint_type}} = Elaborator.elaborate_expr_typed(ast, ["flag"], ctx, env)
  end

  test "rejects incomplete, duplicate, unknown, and wrongly shaped constructor arms" do
    assert {:ok, env} = Program.elaborate("mod M\n  type Flag = Off | On\n")
    body = {:literal, [subtype: :integer], 0}

    assert {:error, {:incomplete_reducer, [:On]}} =
             MacroReducer.build_match("Flag", {:variable, [], "flag"}, [%{constructor: :Off, body: body}], env)

    assert {:error, :duplicate_reducer_constructor} =
             MacroReducer.build_match(
               "Flag",
               {:variable, [], "flag"},
               [%{constructor: :Off, body: body}, %{constructor: :Off, body: body}],
               env
             )

    assert {:error, {:unknown_reducer_constructor, [:Missing]}} =
             MacroReducer.build_match(
               "Flag",
               {:variable, [], "flag"},
               [%{constructor: :Off, body: body}, %{constructor: :Missing, body: body}],
               env
             )
  end
end
