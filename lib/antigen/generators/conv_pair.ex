defmodule Antigen.Generators.ConvPair do
  @moduledoc """
  Known-label generator for the `conv/decision` vertical (`Antigen.Assays.Conv`):
  pairs of closed-up-to-context Core terms with a correct-by-construction
  convertibility verdict, decided by `Cure.Core.Conv.conv?/5` against a context of
  fresh neutral variables (sig = nil, so globals stay opaque and δ is off).

  `conv?` is type-free (η is the §4.5 λ-vs-neutral trick), so these terms need not
  type-check — they only need to *evaluate* to the value shapes whose comparison
  clauses were otherwise cold: stuck projections/primitives (`conv_neutral?`'s
  `nfst`/`nsnd`/`nprim` + the head-mismatch fallback), η (λ-vs-neutral, λ-vs-λ,
  λ-vs-non-λ), Σ-pairs and `refl` (`conv_struct?`), and `same_value_no_delta?`'s
  recursion through a stuck application's argument (type/int/float/data/ctor/λ).
  """
  alias Antigen.{Gen, Challenge}

  # v0..v2: three free variables, materialised as fresh neutrals by the assay.
  @ctx 3

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(shape(), fn {t1, t2, expect, note} ->
      Gen.return(
        Challenge.new(
          kind: :conv_pair,
          assay: "conv/decision",
          label: if(expect, do: :convertible, else: :distinct),
          payload: %{t1: t1, t2: t2, ctx: @ctx, expect: expect},
          note: note
        )
      )
    end)
  end

  defp v(i), do: {:var, i}

  defp shape do
    Gen.frequency([
      # -- stuck-neutral discrimination (conv_neutral?) --
      {2, ret({:fst, v(0)}, {:fst, v(1)}, false, "nfst distinct inner (135)")},
      {2, ret({:snd, v(0)}, {:snd, v(1)}, false, "nsnd distinct inner (136)")},
      {2, ret({:fst, v(0)}, {:snd, v(0)}, false, "nfst vs nsnd head mismatch (150)")},
      {2, ret({:prim, :add, [v(0), v(1)]}, {:prim, :add, [v(0), v(2)]}, false, "nprim distinct arg (139)")},
      # -- η (conv_struct? RHS-λ + eta_eq?) --
      {2, ret(v(0), {:lam, {:type, 0}, {:app, v(1), v(0)}}, true, "η neutral-vs-λ (70,108)")},
      {2, ret({:lam, {:type, 0}, v(1)}, {:lam, {:type, 0}, v(1)}, true, "λ-vs-λ η (107)")},
      {2, ret({:lam, {:type, 0}, v(1)}, {:type, 0}, false, "λ-vs-non-λ (109)")},
      # -- Σ-pair / refl (conv_struct?) --
      {2, ret({:pair, v(0), v(1)}, {:pair, v(0), v(1)}, true, "pair reflexive (83)")},
      {2, ret({:ctor, :reflexive, [v(0)]}, {:ctor, :reflexive, [v(0)]}, true, "reflexive-ctor reflexive (102)")},
      # -- β for projections: fst/snd of an actual pair reduce (Eval vfst/vsnd) --
      {2, ret({:fst, {:pair, v(0), v(1)}}, v(0), true, "fst(pair a b) = a (vfst β)")},
      {2, ret({:snd, {:pair, v(0), v(1)}}, v(1), true, "snd(pair a b) = b (vsnd β)")},
      # -- an out-of-context de Bruijn var evaluates to a fresh neutral (Eval :var nil arm) --
      {1, ret({:var, 5}, {:var, 5}, true, "out-of-ctx var → neutral (eval)")},
      # -- same_value_no_delta? over a stuck app's argument --
      {1, app_refl({:type, 0}, "vtype (187)")},
      {1, app_refl({:int_type}, "vint_type (188)")},
      {1, Gen.bind(Gen.int(-9, 9), fn k -> app_refl({:int_lit, k}, "vint (189)") end)},
      {1, app_refl({:float_type}, "vfloat_type (190)")},
      {1, Gen.bind(Gen.int(-9, 9), fn k -> app_refl({:float_lit, k / 2}, "vfloat (191)") end)},
      {1, app_refl({:data, :Nat, [], []}, "vdata (193)")},
      {1, app_refl({:ctor, :Z, []}, "vctor (196)")},
      {1, app_refl({:lam, {:type, 0}, {:type, 0}}, "vλ fallback → conv_struct η (199)")}
    ])
  end

  # `v0 arg` compared to itself: same_neutral_no_delta? recurses through the napp
  # spine into same_value_no_delta? on the argument value.
  defp app_refl(arg, note) do
    t = {:app, v(0), arg}
    ret(t, t, true, "app-arg " <> note)
  end

  defp ret(t1, t2, expect, note), do: Gen.return({t1, t2, expect, note})
end
