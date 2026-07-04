defmodule Antigen.Assays.KernelLaw do
  @moduledoc """
  Relational kernel-law assays (spec §3), via the public `Cure.Core.*` API (no
  TCB edits): de Bruijn σ-algebra (`kernel/shift_subst`), weakening under an
  unused binder (`kernel/weakening`), reduction order-independence
  (`kernel/confluence`), and capture-avoiding β (`kernel/beta_subst`). Each is a
  `:typed_term` challenge dispatched by assay-id.

  `kernel/beta_subst` additionally calls `Cure.Elab.Subst.instantiate/2` — the
  *elaborator's* (untrusted, non-TCB) substitution — as the property's right-hand
  side: it is precisely the machinery whose capture-safety this law cross-checks
  against the trusted kernel's β-reduction (ledger #4/#26). `elab/shift_agrees`
  is the shift-half of that cross-check: the elaborator's `Subst.shift` must equal
  the kernel's `Term.shift` on every meta-free term.
  """
  alias Antigen.Challenge
  alias Antigen.Generators.SigMenu
  alias Antigen.Assays.Term, as: TermAssay
  alias Cure.Core.{Term, Context, Eval, Normalise, Kernel}
  alias Cure.Elab.Subst

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}
  @sz {:ctor, :S, [{:ctor, :Z, []}]}

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{assay: "kernel/shift_subst", payload: p}), do: shift_subst(p.term)
  def run(%Challenge{assay: "kernel/weakening", payload: p}), do: weakening(p)
  def run(%Challenge{assay: "kernel/confluence", payload: p}), do: confluence(p)
  def run(%Challenge{assay: "kernel/beta_subst", payload: p}), do: beta_subst(p)
  def run(%Challenge{assay: "elab/shift_agrees", payload: p}), do: shift_agrees(p.term)

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

  # ── 3e. elaborator/kernel shift agreement ──────────────────────────────────
  # The untrusted elaborator carries its OWN de Bruijn shift (Cure.Elab.Subst.shift)
  # because it must also shift meta-bearing terms the trusted Core.Term.shift refuses
  # (subst.ex moduledoc). On the meta-FREE terms this generator emits the two MUST
  # coincide: if they ever diverge, the elaborator would relocate free variables
  # differently from the kernel — a capture bug at the TCB boundary that the
  # bind-once β-redex fix (which shifts `expected` via Subst.shift) would inherit.
  defp shift_agrees(t) do
    combos = for a <- [1, 2, 3], c <- [0, 1, 2], do: {a, c}

    case Enum.find_value(combos, fn {a, c} ->
           lhs = Subst.shift(t, a, c)
           rhs = Term.shift(t, a, c)
           if lhs != rhs, do: {a, c, lhs, rhs}, else: nil
         end) do
      nil -> :ok
      f -> {:violation, {:elab_shift_disagrees, f}}
    end
  end

  # ── 3d. capture-avoiding β: β-reduction agrees with substitution ───────────
  # For a redex (λx:T. body) e the law has TWO obligations, both of which must hold:
  #
  #   (a) reduction — the kernel's β lands on the same normal form as substituting
  #       e for x via the elaborator's capture-avoiding `instantiate`;
  #   (b) typing (the substitution lemma) — the redex and its substituted body are
  #       both well-typed and at the SAME type.
  #
  # `instantiate(body, [e])` replaces x (de Bruijn 0) with e, shifting e under every
  # binder body crosses. A shift/capture bug shows up in (a) as a normal-form
  # disagreement AND in (b) as a mis-scoped `subst_term` that infers to no type or a
  # different one — the typing-level teeth the nf comparison alone cannot see.
  defp beta_subst(%{term: {:app, {:lam, _t, body}, e}} = p) do
    ctx = ctx_of(p)
    redex = p.term
    subst_term = Subst.instantiate(body, [e])

    with :ok <- beta_nf_agrees(ctx, redex, subst_term),
         :ok <- beta_type_agrees(ctx, redex, subst_term) do
      :ok
    end
  end

  # The generator only ever emits redexes; a non-redex term is a wiring bug, not a
  # kernel finding — surface it distinctly.
  defp beta_subst(%{term: other}), do: {:violation, {:beta_subst_not_a_redex, other}}

  # (a) β-reduction ≡ substitution. Normalized under the same fuel so a divergent
  # (fuel-exhausting) case abstains rather than false-positives.
  defp beta_nf_agrees(ctx, redex, subst_term) do
    fuel = TermAssay.assay_fuel()
    lhs = Normalise.nf(ctx, redex, fuel: fuel)
    rhs = Normalise.nf(ctx, subst_term, fuel: fuel)

    cond do
      lhs == :fuel_exhausted or rhs == :fuel_exhausted -> :ok
      lhs == rhs -> :ok
      true ->
        {:violation,
         {:beta_subst_mismatch, %{redex: redex, subst: subst_term, beta_nf: lhs, subst_nf: rhs}}}
    end
  end

  # (b) the substitution lemma: Γ,x:A ⊢ body:B and Γ ⊢ e:A ⟹ Γ ⊢ body[e]:B[e].
  # Both the redex and its substituted body must infer, to the same type (compared
  # by their quoted normal forms, as `weakening` does). A `subst_term` that fails to
  # infer, or infers a different type, is a capture/shift bug in `instantiate`.
  defp beta_type_agrees(ctx, redex, subst_term) do
    depth = Context.length(ctx)

    case {Kernel.infer(ctx, redex), Kernel.infer(ctx, subst_term)} do
      {{:ok, vr}, {:ok, vs}} ->
        qr = Normalise.quote(vr, depth)
        qs = Normalise.quote(vs, depth)
        if qr == qs, do: :ok, else: {:violation, {:beta_subst_type_mismatch, %{redex_type: qr, subst_type: qs}}}

      {{:error, er}, _} ->
        {:violation, {:beta_subst_redex_ill_typed, er}}

      {{:ok, _}, {:error, es}} ->
        {:violation, {:beta_subst_result_ill_typed, es}}
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
