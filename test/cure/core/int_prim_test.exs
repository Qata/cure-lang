defmodule Cure.Core.IntPrimTest do
  @moduledoc """
  Primitive `Int` in the kernel (design decision 2026-07-01): the trusted core
  gains integer literals and arithmetic so arithmetic type indices
  (`Vector(T, m + n)`) reduce and compare *inside the kernel* — the single source
  of truth the `Cure.Types.*` layer delegates to.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Conv, Eval, Kernel, Quote}

  test "eval folds integer arithmetic on literals" do
    assert Eval.eval({:prim, :add, [{:int_lit, 3}, {:int_lit, 5}]}, []) == {:vint, 8}
    assert Eval.eval({:prim, :sub, [{:int_lit, 10}, {:int_lit, 3}]}, []) == {:vint, 7}
    assert Eval.eval({:prim, :mul, [{:int_lit, 4}, {:int_lit, 6}]}, []) == {:vint, 24}
    assert Eval.eval({:prim, :div, [{:int_lit, 20}, {:int_lit, 4}]}, []) == {:vint, 5}
  end

  test "eval leaves arithmetic over a free variable stuck as a neutral" do
    v = Eval.eval({:prim, :add, [{:var, 0}, {:int_lit, 1}]}, [{:vneutral, {:nvar, 0}}])
    assert {:vneutral, {:nprim, :add, [{:vneutral, {:nvar, 0}}, {:vint, 1}]}} = v
  end

  test "division by zero stays stuck rather than crashing" do
    v = Eval.eval({:prim, :div, [{:int_lit, 1}, {:int_lit, 0}]}, [])
    assert {:vneutral, {:nprim, :div, [{:vint, 1}, {:vint, 0}]}} = v
  end

  test "reify round-trips Int type, literals, and stuck prims" do
    assert Quote.reify({:vint_type}) == {:int_type}
    assert Quote.reify({:vint, 8}) == {:int_lit, 8}

    stuck = {:vneutral, {:nprim, :add, [{:vneutral, {:nvar, 0}}, {:vint, 1}]}}
    assert Quote.reify(stuck, 1) == {:prim, :add, [{:var, 0}, {:int_lit, 1}]}
  end

  test "definitional equality: 3 + 5 converts with 8; 7 does not" do
    assert Conv.conv?({:prim, :add, [{:int_lit, 3}, {:int_lit, 5}]}, {:int_lit, 8}, [], 0)
    refute Conv.conv?({:int_lit, 7}, {:int_lit, 8}, [], 0)
  end

  test "kernel infers Int for literals and arithmetic, and Int : Type0" do
    ctx = Context.empty()
    assert {:ok, {:vint_type}} = Kernel.infer(ctx, {:int_lit, 42})
    assert {:ok, {:vint_type}} = Kernel.infer(ctx, {:prim, :add, [{:int_lit, 1}, {:int_lit, 2}]})
    assert {:ok, {:vtype, 0}} = Kernel.infer(ctx, {:int_type})
  end

  test "kernel rejects arithmetic on a non-Int argument" do
    ctx = Context.empty()
    assert {:error, _} = Kernel.infer(ctx, {:prim, :add, [{:int_lit, 1}, {:type, 0}]})
  end
end
