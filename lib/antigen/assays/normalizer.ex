defmodule Antigen.Assays.Normalizer do
  @moduledoc """
  Property tests for the untrusted type-level normalizer `Cure.Types.Reduce`
  against the trusted `Cure.Core` kernel (spec: antigen-normalizer-soundness).

    * normalizer/differential — `Reduce.normalize(ast)` agrees with the kernel
      normal form of an INDEPENDENT surface->Core encoding (V1a).
    * normalizer/equal — `Reduce.equal?` never returns a false `true` vs the
      kernel (V1b, the soundness direction).
    * normalizer/intrinsic — on the untranslatable fragment, `normalize` is a
      fixpoint and never grows the term (V1c).

  All kernel ops go through an injectable `@real` map (run/2) so negative
  controls can weaken the thing under test without touching `Cure.Types`/`Cure.Core`
  or using `:meck`.
  """
  alias Antigen.Challenge
  alias Cure.Types.{Reduce, CoreBridge}
  alias Cure.Core.{Eval, Quote, Conv}

  @assay_fuel 500_000
  @real %{
    normalize: &Reduce.normalize/2,
    equal: &Reduce.equal?/3,
    to_core: &CoreBridge.to_core/1,
    eval: &Eval.eval/2,
    reify: &Quote.reify/1,
    conv: &Conv.conv?/5
  }
  @doc false
  def __real__, do: @real

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :surface_expr} = c), do: run(c, @real)

  def run(%Challenge{kind: :surface_expr, assay: "normalizer/differential", payload: p}, k) do
    actual = k.normalize.(p.ast, p.bindings)

    with {:ok, actual_core} <- k.to_core.(actual) do
      expected_core = k.reify.(k.eval.(p.core_expected, []))

      if Cure.Core.Normalise.with_fuel(@assay_fuel, fn -> k.conv.(actual_core, expected_core, [], 0, nil) end) == true do
        :ok
      else
        {:violation, {:normalize_disagrees_with_kernel, p.ast, %{actual: actual, expected: expected_core}}}
      end
    else
      :error -> {:violation, {:normalize_disagrees_with_kernel, p.ast, {:untranslatable_result, actual}}}
    end
  end
end
