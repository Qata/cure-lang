defmodule Cure.Core.PrimBoolInductiveTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Env, Kernel}

  setup do
    %{ctx: Context.empty(Builtins.seed(Env.empty()))}
  end

  test "a comparison infers to the Bool inductive, not {:vbool_type}", %{ctx: ctx} do
    {:ok, ty} = Kernel.infer(ctx, {:prim, :lt, [{:int_lit, 3}, {:int_lit, 5}]})
    assert ty == {:vdata, :Bool, []}
  end

  test "equality infers to the Bool inductive", %{ctx: ctx} do
    {:ok, ty} = Kernel.infer(ctx, {:prim, :eq, [{:int_lit, 3}, {:int_lit, 3}]})
    assert ty == {:vdata, :Bool, []}
  end

  test "the connective primitives are retired: a residual :and prim is rejected", %{ctx: ctx} do
    tt = {:prim, :lt, [{:int_lit, 1}, {:int_lit, 2}]}
    # `and` is now the Std.Bool case-def `booland`, not a primitive.
    assert {:error, {:unknown_prim, :and}} = Kernel.infer(ctx, {:prim, :and, [tt, tt]})
  end
end
