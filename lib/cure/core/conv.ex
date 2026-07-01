defmodule Cure.Core.Conv do
  @moduledoc """
  Definitional equality (conversion) by normalization-by-evaluation
  (design spec §4.5; mirrors Idris `Core/Normalise/Convert.idr` and Lean
  `type_checker.cpp`'s `is_def_eq`).

  `conv?/4,5` evaluates both terms under the shared value environment and
  compares the resulting values up to β, ι (incl. `case`-ι), η, and **δ**.

  δ (global unfolding) is **lazy** and **gated**: a value headed by a global is
  unfolded only when that global is totality-certified in the signature
  (`Cure.Core.Env`, populated by `Kernel.validate_certificate`, M7.2). Until
  then two `:nglobal` heads are convertible iff they are the same name. The
  signature is the optional last argument; with no signature, no δ is performed
  (β/ι/η only — the pre-M7 behaviour).

  Doing δ here (rather than eagerly in `eval`) keeps `eval` signature-free; the
  effect is identical — certified globals reduce wherever conversion compares
  them. η is handled here too, type-free (the §4.5 λ-vs-neutral trick).
  """

  alias Cure.Core.{Env, Eval}

  @doc "True iff `term1` and `term2` are definitionally equal under `env`."
  @spec conv?(Cure.Core.Term.t(), Cure.Core.Term.t(), [Cure.Core.Value.t()], non_neg_integer(), Env.t() | nil) ::
          boolean()
  def conv?(term1, term2, env, depth, sig \\ nil) do
    conv_val?(Eval.eval(term1, env), Eval.eval(term2, env), depth, sig)
  end

  @doc "Value-level definitional equality — the core of `conv?`, for callers holding values."
  @spec conv_values?(Cure.Core.Value.t(), Cure.Core.Value.t(), non_neg_integer(), Env.t() | nil) ::
          boolean()
  def conv_values?(v1, v2, depth, sig \\ nil), do: conv_val?(v1, v2, depth, sig)

  # δ-whnf both sides (unfold certified-global heads), then compare structurally.
  defp conv_val?(v1, v2, depth, sig) do
    conv_struct?(whnf_delta(v1, sig), whnf_delta(v2, sig), depth, sig)
  end

  # η first: a λ on either side, compared by applying both to a fresh neutral.
  defp conv_struct?({:vlam, _, _} = l, r, depth, sig), do: eta_eq?(l, r, depth, sig)
  defp conv_struct?(l, {:vlam, _, _} = r, depth, sig), do: eta_eq?(r, l, depth, sig)

  defp conv_struct?({:vtype, l1}, {:vtype, l2}, _depth, _sig), do: l1 == l2

  defp conv_struct?({:vint_type}, {:vint_type}, _depth, _sig), do: true
  defp conv_struct?({:vint, a}, {:vint, b}, _depth, _sig), do: a == b
  defp conv_struct?({:vbool_type}, {:vbool_type}, _depth, _sig), do: true
  defp conv_struct?({:vbool, a}, {:vbool, b}, _depth, _sig), do: a == b

  defp conv_struct?({:vneutral, n1}, {:vneutral, n2}, depth, sig),
    do: conv_neutral?(n1, n2, depth, sig)

  defp conv_struct?({:vpair, a1, b1}, {:vpair, a2, b2}, depth, sig),
    do: conv_val?(a1, a2, depth, sig) and conv_val?(b1, b2, depth, sig)

  defp conv_struct?({:vpi, d1, c1}, {:vpi, d2, c2}, depth, sig),
    do: conv_val?(d1, d2, depth, sig) and conv_closure?(c1, c2, depth, sig)

  defp conv_struct?({:vsigma, d1, c1}, {:vsigma, d2, c2}, depth, sig),
    do: conv_val?(d1, d2, depth, sig) and conv_closure?(c1, c2, depth, sig)

  defp conv_struct?({:vdata, n1, vs1}, {:vdata, n2, vs2}, depth, sig),
    do: n1 == n2 and conv_spine?(vs1, vs2, depth, sig)

  defp conv_struct?({:vctor, n1, vs1}, {:vctor, n2, vs2}, depth, sig),
    do: n1 == n2 and conv_spine?(vs1, vs2, depth, sig)

  defp conv_struct?({:veq, t1, a1, b1}, {:veq, t2, a2, b2}, depth, sig),
    do:
      conv_val?(t1, t2, depth, sig) and conv_val?(a1, a2, depth, sig) and
        conv_val?(b1, b2, depth, sig)

  defp conv_struct?({:vrefl, a1}, {:vrefl, a2}, depth, sig), do: conv_val?(a1, a2, depth, sig)
  defp conv_struct?(_, _, _, _), do: false

  # -- δ : unfold a certified-global head to weak-head normal form -------------

  defp whnf_delta(value, nil), do: value

  defp whnf_delta({:vneutral, neutral} = v, sig) do
    case unfold_head(neutral, sig) do
      {:ok, reduced} -> whnf_delta(reduced, sig)
      :stuck -> v
    end
  end

  defp whnf_delta(value, _sig), do: value

  defp unfold_head(neutral, sig) do
    {head, args} = spine(neutral, [])

    case head do
      {:nglobal, name} ->
        if Env.certified?(sig, name) do
          %{body: body} = Env.get_def(sig, name)
          {:ok, Enum.reduce(args, Eval.eval(body, []), fn a, acc -> Eval.apply(acc, a) end)}
        else
          :stuck
        end

      _ ->
        :stuck
    end
  end

  defp spine({:napp, n, arg}, acc), do: spine(n, [arg | acc])
  defp spine(head, acc), do: {head, acc}

  # -- η / β-under-binder -----------------------------------------------------

  defp eta_eq?(lam, {:vlam, _, _} = other, depth, sig), do: apply_eq?(lam, other, depth, sig)
  defp eta_eq?(lam, {:vneutral, _} = other, depth, sig), do: apply_eq?(lam, other, depth, sig)
  defp eta_eq?(_lam, _other, _depth, _sig), do: false

  defp apply_eq?(v1, v2, depth, sig) do
    fresh = {:vneutral, {:nvar, depth}}
    conv_val?(Eval.apply(v1, fresh), Eval.apply(v2, fresh), depth + 1, sig)
  end

  defp conv_closure?({:closure, env1, t1}, {:closure, env2, t2}, depth, sig) do
    fresh = {:vneutral, {:nvar, depth}}
    conv_val?(Eval.eval(t1, [fresh | env1]), Eval.eval(t2, [fresh | env2]), depth + 1, sig)
  end

  defp conv_spine?(vs1, vs2, depth, sig) do
    length(vs1) == length(vs2) and
      Enum.zip(vs1, vs2) |> Enum.all?(fn {a, b} -> conv_val?(a, b, depth, sig) end)
  end

  # -- neutral conversion -----------------------------------------------------

  defp conv_neutral?({:nvar, l1}, {:nvar, l2}, _depth, _sig), do: l1 == l2
  # Uncertified globals are opaque, equal iff the same name (δ already tried in whnf).
  defp conv_neutral?({:nglobal, a}, {:nglobal, b}, _depth, _sig), do: a == b

  defp conv_neutral?({:napp, n1, v1}, {:napp, n2, v2}, depth, sig),
    do: conv_neutral?(n1, n2, depth, sig) and conv_val?(v1, v2, depth, sig)

  defp conv_neutral?({:nfst, n1}, {:nfst, n2}, depth, sig), do: conv_neutral?(n1, n2, depth, sig)
  defp conv_neutral?({:nsnd, n1}, {:nsnd, n2}, depth, sig), do: conv_neutral?(n1, n2, depth, sig)

  defp conv_neutral?({:nprim, op1, a1}, {:nprim, op2, a2}, depth, sig),
    do: op1 == op2 and conv_spine?(a1, a2, depth, sig)

  defp conv_neutral?({:ncase, n1, m1, brs1}, {:ncase, n2, m2, brs2}, depth, sig) do
    conv_neutral?(n1, n2, depth, sig) and conv_closure?(m1, m2, depth, sig) and
      conv_branches?(brs1, brs2, depth, sig)
  end

  defp conv_neutral?(_, _, _, _), do: false

  defp conv_branches?(brs1, brs2, depth, sig) do
    length(brs1) == length(brs2) and
      Enum.zip(brs1, brs2)
      |> Enum.all?(fn {{c1, a1, cl1}, {c2, a2, cl2}} ->
        c1 == c2 and a1 == a2 and conv_branch_bodies?(a1, cl1, cl2, depth, sig)
      end)
  end

  defp conv_branch_bodies?(arity, {:closure, env1, body1}, {:closure, env2, body2}, depth, sig) do
    fresh = for i <- 0..(arity - 1)//1, do: {:vneutral, {:nvar, depth + i}}
    ext = Enum.reverse(fresh)
    conv_val?(Eval.eval(body1, ext ++ env1), Eval.eval(body2, ext ++ env2), depth + arity, sig)
  end
end
