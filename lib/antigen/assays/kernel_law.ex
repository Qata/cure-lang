defmodule Antigen.Assays.KernelLaw do
  @moduledoc """
  Relational kernel-law assays (spec §3), all via the public `Cure.Core.*` API
  (no TCB edits): de Bruijn σ-algebra (`kernel/shift_subst`), weakening under an
  unused binder (`kernel/weakening`), and reduction order-independence
  (`kernel/confluence`). Each is a `:typed_term` challenge dispatched by assay-id.
  """
  alias Antigen.Challenge
  alias Antigen.Generators.SigMenu
  alias Antigen.Assays.Term, as: TermAssay
  alias Cure.Core.{Term, Context, Eval, Normalise, Kernel}

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}
  @sz {:ctor, :S, [{:ctor, :Z, []}]}

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{assay: "kernel/shift_subst", payload: p}), do: shift_subst(p.term)
  def run(%Challenge{assay: "kernel/weakening", payload: p}), do: weakening(p)
  def run(%Challenge{assay: "kernel/confluence", payload: p}), do: confluence(p)

  defp ctx_of(p), do: SigMenu.rebuild_context(SigMenu.env_of(p.sig), p.ctx)

  # ── 3a. de Bruijn σ-algebra (pure; no ctx needed) ──────────────────────────
  defp shift_subst(t) do
    with :ok <- law1(t), :ok <- law2(t), :ok <- law3(t), :ok <- law4(t), do: :ok
  end

  defp law1(t) do
    lhs = Term.shift(t, 0, 0)
    if lhs == t, do: :ok, else: {:violation, {:shift_subst_law, 1, lhs, t}}
  end

  defp law2(t) do
    case Enum.find_value([{1, 1, 0}, {2, 1, 0}, {1, 2, 1}, {2, 2, 1}], fn {a, b, c} ->
           lhs = Term.shift(Term.shift(t, a, c), b, c)
           rhs = Term.shift(t, a + b, c)
           if lhs != rhs, do: {a, b, c, lhs, rhs}, else: nil
         end) do
      nil -> :ok
      f -> {:violation, {:shift_subst_law, 2, f}}
    end
  end

  # commutation, for c ≤ j: shift(subst(t,j,r),a,c) == subst(shift(t,a,c), j+a, shift(r,a,c))
  defp law3(t) do
    combos = for j <- [0, 1], c <- [0, 1], a <- [1, 2], r <- [@z, @sz], c <= j, do: {j, c, a, r}
    case Enum.find_value(combos, fn {j, c, a, r} ->
           lhs = Term.shift(Term.subst(t, j, r), a, c)
           rhs = Term.subst(Term.shift(t, a, c), j + a, Term.shift(r, a, c))
           if lhs != rhs, do: {j, c, a, r, lhs, rhs}, else: nil
         end) do
      nil -> :ok
      f -> {:violation, {:shift_subst_law, 3, f}}
    end
  end

  # subst-of-fresh-index no-op: subst(shift(t,1,c),c,r) == shift(t,1,c)
  defp law4(t) do
    case Enum.find_value(for(c <- [0, 1], r <- [@z, @sz], do: {c, r}), fn {c, r} ->
           shifted = Term.shift(t, 1, c)
           lhs = Term.subst(shifted, c, r)
           if lhs != shifted, do: {c, r, lhs, shifted}, else: nil
         end) do
      nil -> :ok
      f -> {:violation, {:shift_subst_law, 4, f}}
    end
  end

  # ── 3b. weakening under an unused binder ───────────────────────────────────
  defp weakening(p) do
    ctx = ctx_of(p)
    t = p.term

    case Kernel.infer(ctx, t) do
      {:error, _} ->
        :ok

      {:ok, v} ->
        a_value = Eval.eval(@nat, Context.env(ctx))
        ctx2 = Context.extend(ctx, a_value)
        t2 = Term.shift(t, 1, 0)

        case Kernel.infer(ctx2, t2) do
          {:error, err} ->
            {:violation, {:weakening_broke_typing, err}}

          {:ok, v2} ->
            q = Normalise.quote(v, Context.length(ctx))
            q2 = Normalise.quote(v2, Context.length(ctx2))
            if q2 == Term.shift(q, 1, 0), do: :ok, else: {:violation, {:weakening_type_mismatch, q, q2}}
        end
    end
  end

  # ── 3c. reduction order-independence ───────────────────────────────────────
  defp confluence(p) do
    ctx = ctx_of(p)
    t = p.term
    fuel = TermAssay.assay_fuel()
    full = Normalise.nf(ctx, t, fuel: fuel)

    staged =
      case Normalise.whnf(ctx, t, fuel: fuel) do
        :fuel_exhausted -> :skip
        w -> Normalise.nf(ctx, w, fuel: fuel)
      end

    cond do
      full == :fuel_exhausted -> :ok
      staged in [:skip, :fuel_exhausted] -> :ok
      full == staged -> :ok
      true -> {:violation, {:confluence_mismatch, full, staged}}
    end
  end
end
