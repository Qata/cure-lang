defmodule Antigen.Generators.SurfaceExpr do
  @moduledoc """
  Fixed catalogs of type-level surface expressions for the `Antigen.Assays.Normalizer`
  families (spec: antigen-normalizer-soundness). Mirrors the elab family's
  fixed-catalog pattern (deterministic, no corpus banking).

    * `differential_challenges/0` — `:translatable` `{ast, bindings, core_expected}`
      triples for `normalizer/differential` (V1a).
    * `equal_challenges/0` — should-be-equal and should-be-unequal pairs for
      `normalizer/equal` (V1b).
    * `intrinsic_challenges/0` — untranslatable-headed terms for
      `normalizer/intrinsic` (V1c).

  `core_expected`/`core_a`/`core_b` are ALWAYS built via `encode/2` — the module's
  own independent surface->Core encoder — never hand-written `{:prim, surface_op, …}`
  literals, since `encode/2` is the one place the surface->core operator-name
  translation (`@ops`) is applied. `encode/2` is independent CODE from
  `Cure.Types.CoreBridge.to_core`, so a CoreBridge/substitution bug surfaces as a
  real mismatch in V1a/V1b rather than a mirrored one.
  """
  alias Antigen.Challenge

  # This module's OWN copy of the surface->core operator tables — separate data
  # from CoreBridge's private maps, but MUST carry the same mapping and the same
  # SHAPE dispatch (either converted operand `{:float_lit,_}` → float_*, else
  # int_* — K2 §1.4), because the certified-δ hook folds registry-keyed
  # builtin-op GLOBAL spines, not surface symbols. `and`/`or` rows are DROPPED:
  # CoreBridge.to_core no longer bridges them (`:error` — Reduce folds Boolean
  # literal connectives surface-side) and no catalog row used them.
  @int_ops %{
    +: :int_add, -: :int_sub, *: :int_mul, /: :int_div, %: :int_rem,
    ==: :int_eq, !=: :int_ne, <: :int_lt, <=: :int_le, >: :int_gt, >=: :int_ge
  }

  @float_ops %{
    +: :float_add, -: :float_sub, *: :float_mul, /: :float_div, %: :int_rem,
    ==: :float_eq, !=: :float_ne, <: :float_lt, <=: :float_le, >: :float_gt, >=: :float_ge
  }

  @doc "Independent surface->Core encoder (folds `bindings` in directly)."
  def encode({:variable, _m, name}, b) do
    case Map.fetch(b, name) do
      {:ok, bound} -> encode(bound, b)
      :error -> {:global, String.to_atom(name)}
    end
  end

  def encode({:literal, _m, n}, _b) when is_integer(n), do: {:int_lit, n}
  def encode({:literal, _m, x}, _b) when is_boolean(x), do: {:ctor, (if x, do: :True, else: :False), []}

  def encode({:binary_op, meta, [l, r]}, b) do
    cl = encode(l, b)
    cr = encode(r, b)

    map =
      if match?({:float_lit, _}, cl) or match?({:float_lit, _}, cr),
        do: @float_ops,
        else: @int_ops

    {:app, {:app, {:global, Map.fetch!(map, Keyword.fetch!(meta, :operator))}, cl}, cr}
  end

  def encode({:tuple, _m, [a, c]}, b), do: {:ctor, :mk_pair, [encode(a, b), encode(c, b)]}

  # -- surface AST helpers ------------------------------------------------------
  defp lit(n), do: {:literal, [subtype: :integer], n}
  defp bin(op, a, b), do: {:binary_op, [operator: op], [a, b]}
  defp var(name), do: {:variable, [], name}

  # -- catalogs -----------------------------------------------------------------

  @doc "V1a differential catalog."
  @spec differential_challenges() :: [Challenge.t()]
  def differential_challenges do
    [
      {bin(:+, lit(3), lit(5)), %{}},
      {bin(:*, lit(4), lit(6)), %{}},
      {bin(:-, lit(10), lit(3)), %{}},
      {bin(:+, var("n"), lit(1)), %{"n" => lit(4)}},
      {bin(:+, bin(:*, lit(2), lit(3)), var("k")), %{"k" => lit(7)}}
    ]
    |> Enum.with_index()
    |> Enum.map(fn {{ast, bindings}, i} ->
      Challenge.new(kind: :surface_expr, assay: "normalizer/differential", label: :translatable,
        payload: %{ast: ast, bindings: bindings, core_expected: encode(ast, bindings)}, seed: i)
    end)
  end

  @doc "V1b equal catalog (should-be-equal + should-be-unequal pairs)."
  @spec equal_challenges() :: [Challenge.t()]
  def equal_challenges do
    [
      {bin(:+, lit(3), lit(5)), lit(8), :kernel_equal},
      {bin(:+, lit(3), lit(5)), lit(9), :kernel_unequal},
      {bin(:*, lit(2), lit(4)), lit(8), :kernel_equal},
      {bin(:*, lit(2), lit(4)), lit(7), :kernel_unequal}
    ]
    |> Enum.with_index()
    |> Enum.map(fn {{a, b, label}, i} ->
      Challenge.new(kind: :surface_expr, assay: "normalizer/equal", label: label,
        payload: %{a: a, b: b, bindings: %{}, core_a: encode(a, %{}), core_b: encode(b, %{})}, seed: i)
    end)
  end

  @doc "V1c intrinsic catalog (untranslatable-headed terms)."
  @spec intrinsic_challenges() :: [Challenge.t()]
  def intrinsic_challenges do
    [
      {:refinement, [], [bin(:+, lit(3), lit(5))]},
      {:refinement, [], [lit(1)]},
      {:named_ref, [], [var("T")]}
    ]
    |> Enum.with_index()
    |> Enum.map(fn {ast, i} ->
      Challenge.new(kind: :surface_expr, assay: "normalizer/intrinsic", label: :untranslatable,
        payload: %{ast: ast}, seed: i)
    end)
  end
end
