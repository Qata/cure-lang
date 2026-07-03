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

  def run(%Challenge{kind: :surface_expr, assay: "normalizer/equal", payload: p}, k) do
    surface_eq = k.equal.(p.a, p.b, p.bindings)
    kernel_eq = Cure.Core.Normalise.with_fuel(@assay_fuel, fn -> k.conv.(p.core_a, p.core_b, [], 0, nil) end)

    # Soundness direction ONLY (V1b, per the moduledoc): `equal?` must never claim
    # `true` when the kernel disagrees. The converse ("surface says false, kernel
    # says true") is a completeness/reach-gap question, out of scope here — and
    # MUST NOT be surfaced as a third outcome kind: `Runner.explore/1`'s dispatch
    # `case` recognizes only `:ok` and `{:violation, _}` with no catch-all, and the
    # `@spec` is `:ok | {:violation, term()}`.
    if surface_eq and kernel_eq != true do
      {:violation, {:equal_unsound, p.a, p.b}}
    else
      :ok
    end
  end
end
