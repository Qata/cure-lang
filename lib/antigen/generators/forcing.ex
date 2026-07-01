defmodule Antigen.Generators.Forcing do
  @moduledoc """
  Forcing generator for `reflexivity-as-normalization` (spec §5.3). Reuses the
  Totality generator's confirmed diverging mutual pair `f = λx. g x`, `g = λx. f x`,
  then builds two **structurally distinct** terms that force the cycle through δ:

    * `t  = f n`                       (unsubstituted application, head `f`)
    * `t' = (f's body)[x := n] = g n`  (one manual β step, head `g`)

  The asymmetry is required: `Cure.Core.Conv.same_neutral_no_delta?/3` would
  short-circuit two *identical* neutrals as equal before δ, so `conv(t, t)` would
  test nothing. `t` (head `f`) vs `t'` (head `g`) can only be resolved *through*
  δ-unfolding — which never terminates while the group is wrongly certified.
  """
  alias Antigen.{Gen, Challenge}
  alias Antigen.Generators.Totality
  alias Cure.Core.{Env, Certificate, Term}

  # A closed Dec value to apply the cycle to (the group's domain is `Dec`).
  @n {:ctor, :Causal, []}

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []), do: Gen.return(forcing_pair())

  @doc "Build the `:forcing_pair` challenge from the confirmed diverging mutual group."
  @spec forcing_pair() :: Challenge.t()
  def forcing_pair do
    group = Totality.diverging_mutual_pair()
    %{defs: defs, focus: focus} = group.payload
    body_f = Enum.find(defs, &(&1.name == :f)).body

    # β step: apply f's body (a lambda) to n by substituting de Bruijn 0.
    {:lam, _dom, inner} = body_f
    t = {:app, {:global, :f}, @n}
    tprime = Term.subst(inner, 0, @n)

    Challenge.new(
      kind: :forcing_pair,
      assay: "reflexivity",
      label: :diverging,
      payload: %{defs: defs, focus: focus, t: t, tprime: tprime},
      note: "forces the wrongly-certified f→g→f cycle through δ"
    )
  end

  @doc """
  Rebuild the `Env` and certify each focus member for which the *real* certifier
  vouches. While the mutual-recursion hole was live this wrongly certified the
  diverging cycle (reproducing the hole's δ-unfolding effect); now that the
  certifier is fixed it certifies nothing here — so conversion no longer unfolds
  the cycle and the reflexivity assay correctly reports no infection.
  """
  @spec certified_env_of(Challenge.t()) :: Env.t()
  def certified_env_of(%Challenge{payload: %{defs: defs, focus: focus}}) do
    env = Enum.reduce(defs, Env.empty(), fn d, e -> Env.add_def(e, d.name, d.type, d.body) end)

    Enum.reduce(focus, env, fn name, e ->
      if Certificate.terminating?(name, Env.get_def(e, name).body, e), do: Env.certify(e, name), else: e
    end)
  end
end
