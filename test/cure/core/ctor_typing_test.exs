defmodule Cure.Core.CtorTypingTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Inductive, Env, Kernel, Context, Eval}

  @svdesc {:data, :SVDesc, [], []}
  @dec {:data, :Dec, [], []}
  @causal {:ctor, :Causal, []}

  defp build_env do
    sf = Inductive.family(:SF, [], [{:as, @svdesc}, {:bs, @svdesc}, {:d, @dec}], 0)

    # seq result index d := d1 (direct). The computed `and(d1,d2)` form requires
    # δ (M7) / case-ι (M4); it is exercised end-to-end in the M10 acceptance test.
    seq =
      Inductive.ctor(
        :seq,
        [
          {:as, @svdesc},
          {:bs, @svdesc},
          {:cs, @svdesc},
          {:d1, @dec},
          {:d2, @dec},
          {:l, {:data, :SF, [], [{:var, 4}, {:var, 3}, {:var, 1}]}},
          {:r, {:data, :SF, [], [{:var, 4}, {:var, 3}, {:var, 1}]}}
        ],
        [{:var, 6}, {:var, 4}, {:var, 3}]
      )

    Env.empty()
    |> Inductive.declare(Inductive.family(:SVDesc, [], [], 0), [])
    |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [
      Inductive.ctor(:Dcoupled, [], []),
      Inductive.ctor(:Causal, [], [])
    ])
    |> Inductive.declare(sf, [seq])
  end

  defp svd(ctx), do: Context.extend(ctx, Eval.eval(@svdesc, []))

  # SF(#a_idx, #b_idx, Causal) as a value in `ctx`.
  defp sf_val(ctx, a_idx, b_idx),
    do: Eval.eval({:data, :SF, [], [{:var, a_idx}, {:var, b_idx}, @causal]}, Context.env(ctx))

  test "infers a constructor application's type, computing the result indices" do
    e = build_env()
    # ctx: as,bs,cs : SVDesc ; l : SF(as,bs,Causal) ; r : SF(bs,cs,Causal)
    c = e |> Context.empty() |> svd() |> svd() |> svd()
    # in c (3 vars): as=#2, bs=#1, cs=#0
    c = Context.extend(c, sf_val(c, 2, 1))
    # in c (4 vars): as=#3, bs=#2, cs=#1, l=#0
    c = Context.extend(c, sf_val(c, 2, 1))
    # in c (5 vars): as=#4, bs=#3, cs=#2, l=#1, r=#0
    app = {:ctor, :seq, [{:var, 4}, {:var, 3}, {:var, 2}, @causal, @causal, {:var, 1}, {:var, 0}]}

    assert {:ok, {:vdata, :SF, [as, cs, dec]}} = Kernel.infer(c, app)
    assert as == {:vneutral, {:nvar, 0}}
    assert cs == {:vneutral, {:nvar, 2}}
    assert dec == {:vctor, :Causal, []}
  end

  test "negative: a middle-index disagreement is an :index_mismatch" do
    e = build_env()
    # ctx: as,bs,bs',cs : SVDesc ; l : SF(as,bs,Causal) ; r' : SF(bs',cs,Causal)
    c = e |> Context.empty() |> svd() |> svd() |> svd() |> svd()
    # in c (4 vars): as=#3, bs=#2, bs'=#1, cs=#0
    c = Context.extend(c, sf_val(c, 3, 2))
    # in c (5 vars): as=#4, bs=#3, bs'=#2, cs=#1, l=#0
    c = Context.extend(c, sf_val(c, 2, 1))
    # in c (6 vars): as=#5, bs=#4, bs'=#3, cs=#2, l=#1, r'=#0
    # seq expects r : SF(bs,cs,..) but r' : SF(bs',cs,..); bs(#4) ≠ bs'(#3).
    app = {:ctor, :seq, [{:var, 5}, {:var, 4}, {:var, 2}, @causal, @causal, {:var, 1}, {:var, 0}]}

    assert {:error, :index_mismatch} = Kernel.infer(c, app)
  end
end
