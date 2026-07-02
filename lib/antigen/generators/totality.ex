defmodule Antigen.Generators.Totality do
  @moduledoc """
  Known-label totality generator (spec §5.1). Emits `:def_group` challenges whose
  ground-truth label (`:terminating` | `:diverging`) is correct **by construction**
  — the generator IS the oracle (umbrella §6), so the deterministic constructors
  below are cross-checked against the real certifier in the Task-12 self-tests.

  Def/family names are a fixed, literal, closed set (`:f`, `:g`, `:h`) so the atoms
  exist the instant this module is loaded — required for `:safe` corpus replay in a
  process that never ran the generator (see `Antigen.Corpus`, Task 5 safety note).
  """
  alias Antigen.{Gen, Challenge}
  alias Cure.Core.Env

  @dec {:data, :Dec, [], []}
  @nat {:data, :Nat, [], []}

  @doc "A Gen program over the known-label def groups."
  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.frequency([
      {1, Gen.return(diverging_mutual_pair())},
      {1, Gen.return(structural_terminating())}
    ])
  end

  @doc """
  The banked 2-cycle: `f = λx. g x`, `g = λx. f x` over `Dec → Dec`. Neither body
  references its own name, so single-body analysis alone cannot witness the cycle;
  `Cure.Core.Certificate` detects it through the signature (mutual-cycle detection,
  the fix for the once-live hole — see `d13d718`) and certifies neither. The pair
  genuinely diverges under δ. Label `:diverging`. Kept forever as the permanent
  regression guard for that fix.
  """
  @spec diverging_mutual_pair() :: Challenge.t()
  def diverging_mutual_pair do
    ty = {:pi, @dec, @dec}
    bf = {:lam, @dec, {:app, {:global, :g}, {:var, 0}}}
    bg = {:lam, @dec, {:app, {:global, :f}, {:var, 0}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{
        defs: [%{name: :f, type: ty, body: bf}, %{name: :g, type: ty, body: bg}],
        focus: [:f, :g]
      },
      note: "mutual cycle f->g->f (hole fixed d13d718; permanent regression guard)"
    )
  end

  @doc """
  A genuinely structural-recursive total def: `h = λn. case n of {Z -> Z; S y -> h y}`
  over `Nat → Nat`. The self-call is on the `S`-branch-bound subterm, so the
  certifier accepts it correctly. Label `:terminating` — guards the eventual
  mutual-recursion fix against over-correction (umbrella §6).
  """
  @spec structural_terminating() :: Challenge.t()
  def structural_terminating do
    motive = {:lam, @nat, @nat}

    body =
      {:lam, @nat,
       {:case, {:var, 0}, motive,
        [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:app, {:global, :h}, {:var, 0}}}]}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{defs: [%{name: :h, type: {:pi, @nat, @nat}, body: body}], focus: [:h]},
      note: "structural recursion h(S y) = h y"
    )
  end

  @doc "Rebuild the def-group's `Env` by folding `Env.add_def/4` over the payload."
  @spec env_of(Challenge.t()) :: Env.t()
  def env_of(%Challenge{payload: %{defs: defs}}) do
    Enum.reduce(defs, Env.empty(), fn d, env -> Env.add_def(env, d.name, d.type, d.body) end)
  end
end
