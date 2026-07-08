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

  # This module's OWN copy of the surface->core operator table — separate data
  # from CoreBridge's private @binops, but MUST carry the same mapping, because
  # Cure.Core.Eval.fold/2 folds on the CORE names, not the surface symbols.
  @ops %{
    +: :add, -: :sub, *: :mul, /: :div, %: :rem,
    ==: :eq, !=: :ne, <: :lt, <=: :le, >: :gt, >=: :ge,
    and: :and, or: :or
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

  def encode({:binary_op, meta, [l, r]}, b),
    do: {:prim, Map.fetch!(@ops, Keyword.fetch!(meta, :operator)), [encode(l, b), encode(r, b)]}

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
