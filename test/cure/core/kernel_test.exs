defmodule Cure.Core.KernelTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Kernel, Context}

  describe "infer/check for Type / var / Pi (M2.2)" do
    test "infer Type0 : Type1" do
      assert {:ok, {:vtype, 1}} == Kernel.infer(Context.empty(), {:type, 0})
    end

    test "infer a variable returns its context type" do
      ctx = Context.extend(Context.empty(), {:vtype, 0})
      assert {:ok, {:vtype, 0}} == Kernel.infer(ctx, {:var, 0})
    end

    test "infer Pi uses the max-level rule" do
      assert {:ok, {:vtype, 1}} == Kernel.infer(Context.empty(), {:pi, {:type, 0}, {:var, 0}})
    end

    test "check is cumulative on sorts: Type0 : Type1 <= Type2" do
      assert :ok == Kernel.check(Context.empty(), {:type, 0}, {:vtype, 2})
    end

    test "check fails on a real mismatch (Type1 : Type2 is not <= Type0)" do
      assert {:error, _} = Kernel.check(Context.empty(), {:type, 1}, {:vtype, 0})
    end
  end
end
