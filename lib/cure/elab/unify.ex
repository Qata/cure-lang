defmodule Cure.Elab.MetaCtx do
  @moduledoc """
  The elaborator's metavariable context (design spec §5.3): fresh unknowns
  created during elaboration (e.g. a constructor's erased index arguments) and
  their solutions once unification determines them.

  Metavariables live only in the untrusted elaborator. A term reaching the
  trusted kernel must be fully solved (`Unify.zonk/2` substitutes every solution
  away); an unsolved metavariable at that point is an elaboration error.
  """

  defstruct next: 0, solutions: %{}

  @type id :: non_neg_integer()
  @type t :: %__MODULE__{next: non_neg_integer(), solutions: %{id() => Cure.Core.Term.t()}}

  @doc "A fresh, empty metavariable context."
  @spec new() :: t()
  def new, do: %__MODULE__{}

  @doc "Allocate a fresh metavariable, returning `{ctx, id}`."
  @spec fresh(t()) :: {t(), id()}
  def fresh(%__MODULE__{next: n} = ctx), do: {%{ctx | next: n + 1}, n}

  @doc "The solution term for `id`, or nil if unsolved."
  @spec solution(t(), id()) :: Cure.Core.Term.t() | nil
  def solution(%__MODULE__{solutions: s}, id), do: Map.get(s, id)

  @doc "Is `id` solved?"
  @spec solved?(t(), id()) :: boolean()
  def solved?(%__MODULE__{solutions: s}, id), do: Map.has_key?(s, id)

  @doc false
  def put_solution(%__MODULE__{solutions: s} = ctx, id, term),
    do: %{ctx | solutions: Map.put(s, id, term)}
end

defmodule Cure.Elab.Unify do
  @moduledoc """
  First-order unification of Core terms with metavariables (design spec §5.3).

  Slice 1's index terms are first-order — constructor/data applications over
  `{:ctor, …}`, `{:data, …}`, and applied globals like `andd(d1, d2)` — so
  syntactic unification with occurs-checked metavariable solving is complete for
  them. (Higher-order Miller-pattern unification is a documented extension point
  for indices that apply a metavariable to bound variables.)

  A metavariable is the elaboration-only term `{:meta, id}`. `unify/3` follows
  existing solutions (`force`), solves unsolved metavariables against the other
  side, and otherwise recurses structurally. `zonk/2` finalises a term by
  substituting every solution away.
  """

  alias Cure.Elab.MetaCtx

  @type uterm :: Cure.Core.Term.t() | {:meta, MetaCtx.id()}

  @doc """
  Unify two (possibly metavariable-bearing) terms, refining the context.

  When `sig` (a `Cure.Core.Env` signature) is supplied, a syntactic failure on
  two CLOSED, metavariable-free terms falls back to the trusted δ-capable
  conversion (`Cure.Core.Conv`) — so a computed index like `dmeet(DDec, DDec)`
  unifies with its normal form `DDec` (Idris parity for composed computed
  indices). This is a COMPLETENESS improvement only: it uses the same conversion
  the kernel uses, and the kernel independently re-checks the assembled term, so
  no soundness rests on this fallback (a wrong accept here is caught downstream).
  Without `sig` the behaviour is exactly the prior purely-syntactic unification.
  """
  @spec unify(uterm(), uterm(), MetaCtx.t(), Cure.Core.Env.t() | nil) ::
          {:ok, MetaCtx.t()} | {:error, term()}
  def unify(t1, t2, ctx, sig \\ nil) do
    unify_d(t1, t2, ctx, sig, 0)
  end

  # Depth-tracked unification: `depth` counts the binders crossed so far (Π/λ/Σ
  # codomains). A metavariable is allocated in the *ambient* context (depth 0), so
  # its solution is stored in that frame. The two directions are duals:
  #   * on *solve* (`?m := t` under `depth` binders) the term is strengthened back
  #     to the ambient frame (`solve/4`), and
  #   * on *force* (reading `?m`'s solution under `depth` binders) the ambient
  #     solution is shifted *up* by `depth` into the current scope (`force_d/3`).
  # Together they keep `(a) -> b` vs `(?a) -> ?b` — and the endomorphism `(a) -> a`,
  # whose variable recurs on both sides of the binder — correctly levelled.
  defp unify_d(t1, t2, ctx, sig, depth) do
    do_unify(force_d(t1, ctx, depth), force_d(t2, ctx, depth), ctx, sig, depth)
  end

  # Resolve a metavariable's solution and lift it from the ambient frame into the
  # current binder `depth`. A non-metavariable head is already in the current
  # scope, so it is returned unshifted.
  defp force_d({:meta, id} = t, ctx, depth) do
    case MetaCtx.solution(ctx, id) do
      nil -> t
      sol -> force_d(Cure.Elab.Subst.shift(sol, depth, 0), ctx, depth)
    end
  end

  defp force_d(t, _ctx, _depth), do: t

  # Follow the chain of solutions until the head is not a solved metavariable
  # (depth-agnostic; used by `occurs?`/`zonk` where no binder lifting applies).
  defp force({:meta, id} = t, ctx) do
    case MetaCtx.solution(ctx, id) do
      nil -> t
      sol -> force(sol, ctx)
    end
  end

  defp force(t, _ctx), do: t

  defp do_unify({:meta, id}, {:meta, id}, ctx, _sig, _depth), do: {:ok, ctx}
  defp do_unify({:meta, id}, t, ctx, _sig, depth), do: solve(id, t, ctx, depth)
  defp do_unify(t, {:meta, id}, ctx, _sig, depth), do: solve(id, t, ctx, depth)

  defp do_unify({:type, l}, {:type, l}, ctx, _sig, _depth), do: {:ok, ctx}
  defp do_unify({:var, i}, {:var, i}, ctx, _sig, _depth), do: {:ok, ctx}
  defp do_unify({:global, g}, {:global, g}, ctx, _sig, _depth), do: {:ok, ctx}

  defp do_unify({:data, f, ps1, is1}, {:data, f, ps2, is2}, ctx, sig, depth),
    do: unify_lists(ps1 ++ is1, ps2 ++ is2, ctx, sig, depth)

  defp do_unify({:ctor, c, a1}, {:ctor, c, a2}, ctx, sig, depth),
    do: unify_lists(a1, a2, ctx, sig, depth)

  defp do_unify({:app, f1, x1}, {:app, f2, x2}, ctx, sig, depth) do
    with {:ok, ctx} <- unify_d(f1, f2, ctx, sig, depth), do: unify_d(x1, x2, ctx, sig, depth)
  end

  defp do_unify({:pi, d1, c1}, {:pi, d2, c2}, ctx, sig, depth) do
    with {:ok, ctx} <- unify_d(d1, d2, ctx, sig, depth),
         do: unify_d(c1, c2, ctx, sig, depth + 1)
  end

  defp do_unify({:lam, d1, b1}, {:lam, d2, b2}, ctx, sig, depth) do
    with {:ok, ctx} <- unify_d(d1, d2, ctx, sig, depth),
         do: unify_d(b1, b2, ctx, sig, depth + 1)
  end

  defp do_unify({:sigma, d1, c1}, {:sigma, d2, c2}, ctx, sig, depth) do
    with {:ok, ctx} <- unify_d(d1, d2, ctx, sig, depth),
         do: unify_d(c1, c2, ctx, sig, depth + 1)
  end

  # Structurally identical (literals, atoms, etc.).
  defp do_unify(t, t, ctx, _sig, _depth), do: {:ok, ctx}

  # Last resort: two terms that are not syntactically unifiable may still be
  # DEFINITIONALLY equal via δ (e.g. `DDec` vs the redex `dmeet(DDec, DDec)`).
  # Only attempt this when a signature is available and both sides are closed and
  # metavariable-free — then they carry no unification variables to solve, so a
  # convertibility check is exactly the right question, and `env=[] depth=0` is
  # sound (no free de Bruijn vars). Open neutral spines (e.g. `app(av, cv)`) unify
  # syntactically and never reach here.
  defp do_unify(t1, t2, ctx, sig, _depth) do
    if delta_convertible?(t1, t2, ctx, sig) do
      {:ok, ctx}
    else
      {:error, {:cannot_unify, t1, t2}}
    end
  end

  defp delta_convertible?(_t1, _t2, _ctx, nil), do: false

  defp delta_convertible?(t1, t2, ctx, sig) do
    z1 = zonk(t1, ctx)
    z2 = zonk(t2, ctx)

    meta_free?(z1) and meta_free?(z2) and
      Cure.Core.Term.closed?(z1) and Cure.Core.Term.closed?(z2) and
      Cure.Core.Conv.conv?(z1, z2, [], 0, sig)
  end

  defp meta_free?({:meta, _}), do: false
  defp meta_free?({:data, _f, ps, is}), do: Enum.all?(ps ++ is, &meta_free?/1)
  defp meta_free?({:ctor, _c, args}), do: Enum.all?(args, &meta_free?/1)
  defp meta_free?({:app, f, x}), do: meta_free?(f) and meta_free?(x)
  defp meta_free?({:pi, d, c}), do: meta_free?(d) and meta_free?(c)
  defp meta_free?({:lam, d, b}), do: meta_free?(d) and meta_free?(b)
  defp meta_free?(_), do: true

  defp unify_lists([], [], ctx, _sig, _depth), do: {:ok, ctx}

  defp unify_lists([x | xs], [y | ys], ctx, sig, depth) do
    with {:ok, ctx} <- unify_d(x, y, ctx, sig, depth), do: unify_lists(xs, ys, ctx, sig, depth)
  end

  defp unify_lists(l1, l2, _ctx, _sig, _depth),
    do: {:error, {:arity_mismatch, length(l1), length(l2)}}

  # Solve `?id := t`, first strengthening `t` from the current binder `depth` back
  # to the ambient frame the metavariable lives in. A free variable that points
  # *into* those `depth` local binders would escape its scope, so the solve fails
  # (not a first-order solution — a higher-order/Miller case we do not attempt).
  # At depth 0 this is the identity, so every existing (top-level) unification is
  # unchanged.
  defp solve(id, t, ctx, depth) do
    case strengthen(t, depth) do
      :escape -> {:error, {:escaping_variable, id}}
      {:ok, t2} -> solve_strengthened(id, t2, ctx)
    end
  end

  defp solve_strengthened(id, t, ctx) do
    if occurs?(id, t, ctx) do
      {:error, {:occurs_check, id, t}}
    else
      {:ok, MetaCtx.put_solution(ctx, id, t)}
    end
  end

  # Strengthen `t` by `depth`: subtract `depth` from every variable free in `t`
  # (accounting for `t`'s own binders), returning `:escape` if any free variable
  # points into the `depth` binders being removed. `depth == 0` is the identity.
  defp strengthen(t, 0), do: {:ok, t}

  defp strengthen(t, depth) do
    if escapes?(t, depth, 0), do: :escape, else: {:ok, Cure.Elab.Subst.shift(t, -depth, 0)}
  end

  # Does `t` reference (freely) any of the outermost `depth` binders? `local`
  # counts binders internal to `t`; a variable `i >= local` is free, at free index
  # `i - local`, and escapes iff that index is `< depth`.
  defp escapes?({:var, i}, depth, local), do: i >= local and i - local < depth
  defp escapes?({:meta, _}, _depth, _local), do: false
  defp escapes?({:pi, d, c}, depth, local), do: escapes?(d, depth, local) or escapes?(c, depth, local + 1)
  defp escapes?({:lam, d, b}, depth, local), do: escapes?(d, depth, local) or escapes?(b, depth, local + 1)

  defp escapes?({:sigma, d, c}, depth, local),
    do: escapes?(d, depth, local) or escapes?(c, depth, local + 1)

  defp escapes?({:app, f, x}, depth, local), do: escapes?(f, depth, local) or escapes?(x, depth, local)
  defp escapes?({:pair, a, b}, depth, local), do: escapes?(a, depth, local) or escapes?(b, depth, local)
  defp escapes?({:fst, p}, depth, local), do: escapes?(p, depth, local)
  defp escapes?({:snd, p}, depth, local), do: escapes?(p, depth, local)

  defp escapes?({:data, _f, ps, is}, depth, local),
    do: Enum.any?(ps ++ is, &escapes?(&1, depth, local))

  defp escapes?({:ctor, _c, args}, depth, local), do: Enum.any?(args, &escapes?(&1, depth, local))
  defp escapes?(_other, _depth, _local), do: false

  # Does metavariable `id` occur in `t` (following solutions)?
  defp occurs?(id, t, ctx) do
    case force(t, ctx) do
      {:meta, ^id} -> true
      {:meta, _other} -> false
      {:data, _f, ps, is} -> Enum.any?(ps ++ is, &occurs?(id, &1, ctx))
      {:ctor, _c, args} -> Enum.any?(args, &occurs?(id, &1, ctx))
      {:app, f, x} -> occurs?(id, f, ctx) or occurs?(id, x, ctx)
      {:pi, d, c} -> occurs?(id, d, ctx) or occurs?(id, c, ctx)
      {:lam, d, b} -> occurs?(id, d, ctx) or occurs?(id, b, ctx)
      _ -> false
    end
  end

  @doc "Finalise a term by substituting every metavariable solution away."
  @spec zonk(uterm(), MetaCtx.t()) :: uterm()
  def zonk(t, ctx) do
    case force(t, ctx) do
      {:meta, _id} = m -> m
      {:data, f, ps, is} -> {:data, f, Enum.map(ps, &zonk(&1, ctx)), Enum.map(is, &zonk(&1, ctx))}
      {:ctor, c, args} -> {:ctor, c, Enum.map(args, &zonk(&1, ctx))}
      {:app, f, x} -> {:app, zonk(f, ctx), zonk(x, ctx)}
      {:pi, d, c} -> {:pi, zonk(d, ctx), zonk(c, ctx)}
      {:lam, d, b} -> {:lam, zonk(d, ctx), zonk(b, ctx)}
      other -> other
    end
  end
end
