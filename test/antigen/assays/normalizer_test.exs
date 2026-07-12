defmodule Antigen.Assays.NormalizerTest do
  use ExUnit.Case, async: true
  alias Antigen.{Assays.Normalizer, Challenge}
  alias Antigen.Generators.SurfaceExpr

  # {:binary_op, [operator: :+], [3, 5]} and its independent core encoding.
  # NOTE (K2, spec 2026-07-09 §1.4): the core side is a builtin-op GLOBAL spine
  # (`int_add`, shape-dispatched int_*/float_*), NOT the surface `:+` — the
  # certified-δ hook folds registry-keyed spines; a `{:global, :+}` head would
  # never fold. `and`/`or` are no longer bridged (Reduce folds them surface-side).
  defp lit(n), do: {:literal, [subtype: :integer], n}
  defp add(a, b), do: {:binary_op, [operator: :+], [a, b]}

  defp diff_ch(ast, bindings, core_expected) do
    Challenge.new(
      kind: :surface_expr,
      assay: "normalizer/differential",
      label: :translatable,
      payload: %{ast: ast, bindings: bindings, core_expected: core_expected},
      seed: 1
    )
  end

  test "V1a baseline: normalize(3+5) agrees with the kernel norm of the independent encoding" do
    ch = diff_ch(add(lit(3), lit(5)), %{}, {:app, {:app, {:global, :int_add}, {:int_lit, 3}}, {:int_lit, 5}})
    assert Normalizer.run(ch) == :ok
  end

  test "V1a from_core-style negative control: a normalize stub with a corrupted result infects" do
    ch = diff_ch(add(lit(3), lit(5)), %{}, {:app, {:app, {:global, :int_add}, {:int_lit, 3}}, {:int_lit, 5}})
    # wrong: says 7, not 8
    k = %{Normalizer.__real__() | normalize: fn _ast, _b -> lit(7) end}
    assert {:violation, {:normalize_disagrees_with_kernel, _, _}} = Normalizer.run(ch, k)
  end

  test "V1a substitution negative control: a normalize stub that drops a binding infects" do
    # ast = n + 1 with n=4 ; core_expected folds n->4 => 4+1. A stub that leaves `n`
    # unsubstituted returns `n + 1` (a {:variable} survives) -> to_core gives a
    # {:global,:n} the kernel norm of core_expected (5) is not convertible to.
    ast = add({:variable, [], "n"}, lit(1))
    ch = diff_ch(ast, %{"n" => lit(4)}, {:app, {:app, {:global, :int_add}, {:int_lit, 4}}, {:int_lit, 1}})
    # identity: never substitutes
    k = %{Normalizer.__real__() | normalize: fn a, _b -> a end}
    assert {:violation, {:normalize_disagrees_with_kernel, _, _}} = Normalizer.run(ch, k)
  end

  test "V1a untranslatable-result negative control: a normalize stub returning an untranslatable AST infects" do
    # {:untranslatable_probe, ...} is outside CoreBridge.to_core's grammar (to_core -> :error),
    # so this exercises the `with ... else :error -> ...` branch that no other test
    # here reaches (Reduce.normalize itself always stays inside the translatable
    # fragment for a translatable input; only a broken stub can violate that).
    ch = diff_ch(add(lit(3), lit(5)), %{}, {:app, {:app, {:global, :int_add}, {:int_lit, 3}}, {:int_lit, 5}})
    k = %{Normalizer.__real__() | normalize: fn _ast, _b -> {:untranslatable_probe, [], [lit(8)]} end}

    assert {:violation, {:normalize_disagrees_with_kernel, _, {:untranslatable_result, _}}} =
             Normalizer.run(ch, k)
  end

  describe "normalizer/equal (V1b soundness)" do
    defp eq_ch(a, ca, b, cb, label) do
      Challenge.new(
        kind: :surface_expr,
        assay: "normalizer/equal",
        label: label,
        payload: %{a: a, b: b, bindings: %{}, core_a: ca, core_b: cb},
        seed: 1
      )
    end

    # Same spine-not-`:+` note as above applies to every hand-built core_a/core_b here.
    test "baseline: equal?(3+5, 8)=true and kernel agrees; equal?(3+5, 9)=false and kernel agrees" do
      t =
        eq_ch(
          add(lit(3), lit(5)),
          {:app, {:app, {:global, :int_add}, {:int_lit, 3}}, {:int_lit, 5}},
          lit(8),
          {:int_lit, 8},
          :kernel_equal
        )

      f =
        eq_ch(
          add(lit(3), lit(5)),
          {:app, {:app, {:global, :int_add}, {:int_lit, 3}}, {:int_lit, 5}},
          lit(9),
          {:int_lit, 9},
          :kernel_unequal
        )

      assert Normalizer.run(t) == :ok
      assert Normalizer.run(f) == :ok
    end

    test "unsound negative control: equal? returns true for a kernel-unequal pair infects" do
      f =
        eq_ch(
          add(lit(3), lit(5)),
          {:app, {:app, {:global, :int_add}, {:int_lit, 3}}, {:int_lit, 5}},
          lit(9),
          {:int_lit, 9},
          :kernel_unequal
        )

      # unsound: claims 8 == 9
      k = %{Normalizer.__real__() | equal: fn _a, _b, _bnd -> true end}
      assert {:violation, {:equal_unsound, _, _}} = Normalizer.run(f, k)
    end
  end

  describe "normalizer/intrinsic (V1c)" do
    # {:untranslatable_probe, ...} is outside CoreBridge's grammar (to_core -> :error).
    defp intr_ch(ast) do
      Challenge.new(
        kind: :surface_expr,
        assay: "normalizer/intrinsic",
        label: :untranslatable,
        payload: %{ast: ast},
        seed: 1
      )
    end

    defp untranslatable(inner), do: {:untranslatable_probe, [], [inner]}

    test "baseline: normalize is a fixpoint and does not grow the term" do
      assert Normalizer.run(intr_ch(untranslatable(add(lit(3), lit(5))))) == :ok
    end

    test "not-idempotent negative control" do
      # Must NOT also grow the term, or it trips :size_increased first (the
      # implementation checks size before idempotence — see Step 3's note). This
      # stub retags {:untranslatable_probe,...} <-> {:not_fixed,...} with the SAME child
      # count each call (term_size is tag-blind), so the size guard passes and
      # the oscillation exposes genuine non-idempotence: once != p.ast's shape,
      # twice flips back, so twice != once.
      k = %{
        Normalizer.__real__()
        | normalize: fn
            {:untranslatable_probe, m, [inner]}, _b -> {:not_fixed, m, [inner]}
            {:not_fixed, m, [inner]}, _b -> {:untranslatable_probe, m, [inner]}
            ast, _b -> ast
          end
      }

      assert {:violation, {:not_idempotent, _, _}} = Normalizer.run(intr_ch(untranslatable(lit(1))), k)
    end

    test "size-increase negative control" do
      # strictly larger
      k = %{Normalizer.__real__() | normalize: fn ast, _b -> {:dup, [], [ast, ast]} end}
      assert {:violation, {:size_increased, _, _}} = Normalizer.run(intr_ch(untranslatable(lit(1))), k)
    end
  end

  describe "generator + runner wiring" do
    alias Antigen.Runner

    test "each catalog is non-empty and correctly tagged" do
      assert SurfaceExpr.differential_challenges() != []
      assert Enum.all?(SurfaceExpr.differential_challenges(), &(&1.assay == "normalizer/differential"))
      assert Enum.all?(SurfaceExpr.equal_challenges(), &(&1.assay == "normalizer/equal"))
      assert Enum.all?(SurfaceExpr.intrinsic_challenges(), &(&1.assay == "normalizer/intrinsic"))
    end

    test "runner dispatches each normalizer/* id and every catalog entry is clean under the real kernel" do
      all =
        SurfaceExpr.differential_challenges() ++ SurfaceExpr.equal_challenges() ++ SurfaceExpr.intrinsic_challenges()

      assert Enum.all?(all, fn c -> Runner.replay_one(c) == :ok end)
    end
  end
end
