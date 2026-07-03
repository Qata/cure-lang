defmodule Antigen.Assays.NormalizerTest do
  use ExUnit.Case, async: true
  alias Antigen.{Assays.Normalizer, Challenge}
  alias Antigen.Generators.SurfaceExpr

  # {:binary_op, [operator: :+], [3, 5]} and its independent core encoding.
  # NOTE: the core-side op atom is `:add`, NOT the surface `:+` — `CoreBridge.to_core`
  # translates through its `@binops` table, and `Eval.fold/2` only has clauses for
  # the translated core names. `{:prim, :+, [...]}` would never fold (see Interfaces).
  defp lit(n), do: {:literal, [subtype: :integer], n}
  defp add(a, b), do: {:binary_op, [operator: :+], [a, b]}

  defp diff_ch(ast, bindings, core_expected) do
    Challenge.new(kind: :surface_expr, assay: "normalizer/differential",
      label: :translatable, payload: %{ast: ast, bindings: bindings, core_expected: core_expected}, seed: 1)
  end

  test "V1a baseline: normalize(3+5) agrees with the kernel norm of the independent encoding" do
    ch = diff_ch(add(lit(3), lit(5)), %{}, {:prim, :add, [{:int_lit, 3}, {:int_lit, 5}]})
    assert Normalizer.run(ch) == :ok
  end

  test "V1a from_core-style negative control: a normalize stub with a corrupted result infects" do
    ch = diff_ch(add(lit(3), lit(5)), %{}, {:prim, :add, [{:int_lit, 3}, {:int_lit, 5}]})
    k = %{Normalizer.__real__() | normalize: fn _ast, _b -> lit(7) end}  # wrong: says 7, not 8
    assert {:violation, {:normalize_disagrees_with_kernel, _, _}} = Normalizer.run(ch, k)
  end

  test "V1a substitution negative control: a normalize stub that drops a binding infects" do
    # ast = n + 1 with n=4 ; core_expected folds n->4 => 4+1. A stub that leaves `n`
    # unsubstituted returns `n + 1` (a {:variable} survives) -> to_core gives a
    # {:global,:n} the kernel norm of core_expected (5) is not convertible to.
    ast = add({:variable, [], "n"}, lit(1))
    ch = diff_ch(ast, %{"n" => lit(4)}, {:prim, :add, [{:int_lit, 4}, {:int_lit, 1}]})
    k = %{Normalizer.__real__() | normalize: fn a, _b -> a end}  # identity: never substitutes
    assert {:violation, {:normalize_disagrees_with_kernel, _, _}} = Normalizer.run(ch, k)
  end

  test "V1a untranslatable-result negative control: a normalize stub returning an untranslatable AST infects" do
    # {:refinement, ...} is outside CoreBridge.to_core's grammar (to_core -> :error),
    # so this exercises the `with ... else :error -> ...` branch that no other test
    # here reaches (Reduce.normalize itself always stays inside the translatable
    # fragment for a translatable input; only a broken stub can violate that).
    ch = diff_ch(add(lit(3), lit(5)), %{}, {:prim, :add, [{:int_lit, 3}, {:int_lit, 5}]})
    k = %{Normalizer.__real__() | normalize: fn _ast, _b -> {:refinement, [], [lit(8)]} end}
    assert {:violation, {:normalize_disagrees_with_kernel, _, {:untranslatable_result, _}}} =
             Normalizer.run(ch, k)
  end

  describe "normalizer/equal (V1b soundness)" do
    defp eq_ch(a, ca, b, cb, label) do
      Challenge.new(kind: :surface_expr, assay: "normalizer/equal", label: label,
        payload: %{a: a, b: b, bindings: %{}, core_a: ca, core_b: cb}, seed: 1)
    end

    # Same `:add`-not-`:+` note as Task 1 applies to every hand-built core_a/core_b here.
    test "baseline: equal?(3+5, 8)=true and kernel agrees; equal?(3+5, 9)=false and kernel agrees" do
      t = eq_ch(add(lit(3), lit(5)), {:prim, :add, [{:int_lit,3},{:int_lit,5}]}, lit(8), {:int_lit, 8}, :kernel_equal)
      f = eq_ch(add(lit(3), lit(5)), {:prim, :add, [{:int_lit,3},{:int_lit,5}]}, lit(9), {:int_lit, 9}, :kernel_unequal)
      assert Normalizer.run(t) == :ok
      assert Normalizer.run(f) == :ok
    end

    test "unsound negative control: equal? returns true for a kernel-unequal pair infects" do
      f = eq_ch(add(lit(3), lit(5)), {:prim, :add, [{:int_lit,3},{:int_lit,5}]}, lit(9), {:int_lit, 9}, :kernel_unequal)
      k = %{Normalizer.__real__() | equal: fn _a, _b, _bnd -> true end}  # unsound: claims 8 == 9
      assert {:violation, {:equal_unsound, _, _}} = Normalizer.run(f, k)
    end
  end
end
