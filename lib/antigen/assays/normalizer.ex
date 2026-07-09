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
  alias Cure.Core.{Builtins, Context, Conv, Env, Eval, Normalise, Quote}

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

  # K2 (spec 2026-07-09 §1.4): the independent encoding is now builtin-op
  # GLOBAL spines, which fold only under the SIGNATURE-CARRYING certified-δ
  # engine — the kernel-side expectation therefore normalizes/converts over a
  # builtins-seeded env (bare `Eval.eval([])`/nil-sig conv would leave every
  # spine stuck and the differential vacuous).
  defp sig, do: Builtins.seed(Env.empty())

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :surface_expr} = c), do: run(c, @real)

  def run(%Challenge{kind: :surface_expr, assay: "normalizer/differential", payload: p}, k) do
    actual = k.normalize.(p.ast, p.bindings)

    with {:ok, actual_core} <- k.to_core.(actual) do
      s = sig()
      expected_core = Normalise.nf(Context.empty(s), p.core_expected, delta: :certified)

      if Normalise.with_fuel(@assay_fuel, fn -> k.conv.(actual_core, expected_core, [], 0, s) end) == true do
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
    kernel_eq = Normalise.with_fuel(@assay_fuel, fn -> k.conv.(p.core_a, p.core_b, [], 0, sig()) end)

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

  def run(%Challenge{kind: :surface_expr, assay: "normalizer/intrinsic", payload: p}, k) do
    once = k.normalize.(p.ast, %{})
    twice = k.normalize.(once, %{})

    # Size guard FIRST: a stub that both grows and is non-idempotent reports
    # :size_increased deterministically.
    cond do
      term_size(once) > term_size(p.ast) ->
        {:violation, {:size_increased, p.ast, %{in: term_size(p.ast), out: term_size(once)}}}

      twice != once ->
        {:violation, {:not_idempotent, p.ast, %{once: once, twice: twice}}}

      true ->
        :ok
    end
  end

  # node count over the {tag, meta, children} grammar; meta excluded, scalar leaves
  # count 1. A scalar-payload node like {:literal, meta, 3} has a non-list third
  # element, so it falls to the leaf clause (size 1), not the composite one.
  defp term_size({_tag, _meta, children}) when is_list(children),
    do: 1 + Enum.sum(Enum.map(children, &term_size/1))

  defp term_size(_leaf), do: 1
end
