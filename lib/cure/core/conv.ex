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

  alias Cure.Core.{Env, Eval, Normalise}

  @doc """
  Like `conv?/5`, but bounds the total number of δ-unfolds to `fuel`. Returns
  `{:ok, boolean}` if conversion decides within budget, or `:fuel_exhausted` if the
  δ-unfold count is hit first (a suspected non-normalization — the reflexivity
  assay's oracle, spec §4.3/§8). The verdict is a fixed step count, so it is
  machine-independent and replayable.
  """
  @spec conv_within?(
          Cure.Core.Term.t(),
          Cure.Core.Term.t(),
          [Cure.Core.Value.t()],
          non_neg_integer(),
          Env.t() | nil,
          pos_integer()
        ) ::
          {:ok, boolean()} | :fuel_exhausted
  def conv_within?(term1, term2, env, depth, sig, fuel) when is_integer(fuel) and fuel > 0 do
    Normalise.with_fuel(fuel, fn ->
      {:ok, conv?(term1, term2, env, depth, sig)}
    end)
  end

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
  defp conv_val?({:vneutral, n1} = v1, {:vneutral, n2} = v2, depth, sig) do
    same_neutral_no_delta?(n1, n2, depth) or
      conv_struct?(Normalise.whnf_value(v1, sig), Normalise.whnf_value(v2, sig), depth, sig)
  end

  defp conv_val?(v1, v2, depth, sig) do
    conv_struct?(Normalise.whnf_value(v1, sig), Normalise.whnf_value(v2, sig), depth, sig)
  end

  # η first: a λ on either side, compared by applying both to a fresh neutral.
  defp conv_struct?({:vlam, _, _} = l, r, depth, sig), do: eta_eq?(l, r, depth, sig)
  defp conv_struct?(l, {:vlam, _, _} = r, depth, sig), do: eta_eq?(r, l, depth, sig)

  defp conv_struct?({:vtype, l1}, {:vtype, l2}, _depth, _sig), do: l1 == l2

  defp conv_struct?({:vint_type}, {:vint_type}, _depth, _sig), do: true
  defp conv_struct?({:vint, a}, {:vint, b}, _depth, _sig), do: a == b
  defp conv_struct?({:vfloat_type}, {:vfloat_type}, _depth, _sig), do: true
  defp conv_struct?({:vfloat, a}, {:vfloat, b}, _depth, _sig), do: a == b

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

  defp conv_struct?(_, _, _, _), do: false

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

  # The scrutinee compares up to conversion (lifted to a value, so whnf can
  # force a redex scrutinee that δι-reduces past the stuck case) — a stuck
  # case's scrutinee is an argument position like any other, per Lean
  # `is_def_eq_app` (each arg via full `is_def_eq`) and Agda `compareElims`.
  defp conv_neutral?({:ncase, n1, m1, brs1}, {:ncase, n2, m2, brs2}, depth, sig) do
    conv_val?({:vneutral, n1}, {:vneutral, n2}, depth, sig) and conv_closure?(m1, m2, depth, sig) and
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

  # Syntactic equality for neutral values before δ. This prevents certified
  # recursive globals from unfolding forever when conversion reaches the same
  # stuck recursive call on both sides (`plus(k, n)` vs `plus(k, n)`), while still
  # allowing δ when the two heads are not already identical.
  defp same_neutral_no_delta?({:nvar, l1}, {:nvar, l2}, _depth), do: l1 == l2
  defp same_neutral_no_delta?({:nglobal, a}, {:nglobal, b}, _depth), do: a == b

  defp same_neutral_no_delta?({:napp, f1, a1}, {:napp, f2, a2}, depth),
    do: same_neutral_no_delta?(f1, f2, depth) and same_value_no_delta?(a1, a2, depth)

  defp same_neutral_no_delta?({:nfst, n1}, {:nfst, n2}, depth), do: same_neutral_no_delta?(n1, n2, depth)
  defp same_neutral_no_delta?({:nsnd, n1}, {:nsnd, n2}, depth), do: same_neutral_no_delta?(n1, n2, depth)

  defp same_neutral_no_delta?({:nprim, op1, args1}, {:nprim, op2, args2}, depth),
    do: op1 == op2 and same_spine_no_delta?(args1, args2, depth)

  defp same_neutral_no_delta?(_, _, _depth), do: false

  defp same_value_no_delta?({:vneutral, n1}, {:vneutral, n2}, depth),
    do: same_neutral_no_delta?(n1, n2, depth)

  defp same_value_no_delta?({:vtype, l1}, {:vtype, l2}, _depth), do: l1 == l2
  defp same_value_no_delta?({:vint_type}, {:vint_type}, _depth), do: true
  defp same_value_no_delta?({:vint, a}, {:vint, b}, _depth), do: a == b
  defp same_value_no_delta?({:vfloat_type}, {:vfloat_type}, _depth), do: true
  defp same_value_no_delta?({:vfloat, a}, {:vfloat, b}, _depth), do: a == b

  defp same_value_no_delta?({:vdata, n1, args1}, {:vdata, n2, args2}, depth),
    do: n1 == n2 and same_spine_no_delta?(args1, args2, depth)

  defp same_value_no_delta?({:vctor, n1, args1}, {:vctor, n2, args2}, depth),
    do: n1 == n2 and same_spine_no_delta?(args1, args2, depth)

  defp same_value_no_delta?(_a, _b, _depth), do: false

  defp same_spine_no_delta?(args1, args2, depth) do
    length(args1) == length(args2) and
      Enum.zip(args1, args2) |> Enum.all?(fn {a, b} -> same_value_no_delta?(a, b, depth) end)
  end
end
