defmodule Cure.Compiler.MacroFuzzTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.MacroFuzz
  alias Cure.Core.{Context, Eval, Kernel}

  test "samples well-typed Core fillers for supported grammar categories" do
    for category <- ["Nat", "Bd", "Vec"] do
      assert {:ok, %{ctx: ctx, goal: goal}, terms} = MacroFuzz.sample_holes(category, 12, 19)
      goal_value = Eval.eval(goal, Context.env(ctx))

      assert length(terms) == 12
      assert Enum.all?(terms, &(Kernel.check(ctx, &1, goal_value) == :ok))
    end
  end

  test "unsupported grammar categories are reported as coverage gaps" do
    assert {:error, {:unsupported_hole_type, "Code"}} = MacroFuzz.hole_generator("Code")
  end
end
