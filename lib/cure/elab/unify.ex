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

  @doc "Unify two (possibly metavariable-bearing) terms, refining the context."
  @spec unify(uterm(), uterm(), MetaCtx.t()) :: {:ok, MetaCtx.t()} | {:error, term()}
  def unify(t1, t2, ctx) do
    do_unify(force(t1, ctx), force(t2, ctx), ctx)
  end

  # Follow the chain of solutions until the head is not a solved metavariable.
  defp force({:meta, id} = t, ctx) do
    case MetaCtx.solution(ctx, id) do
      nil -> t
      sol -> force(sol, ctx)
    end
  end

  defp force(t, _ctx), do: t

  defp do_unify({:meta, id}, {:meta, id}, ctx), do: {:ok, ctx}
  defp do_unify({:meta, id}, t, ctx), do: solve(id, t, ctx)
  defp do_unify(t, {:meta, id}, ctx), do: solve(id, t, ctx)

  defp do_unify({:type, l}, {:type, l}, ctx), do: {:ok, ctx}
  defp do_unify({:var, i}, {:var, i}, ctx), do: {:ok, ctx}
  defp do_unify({:global, g}, {:global, g}, ctx), do: {:ok, ctx}

  defp do_unify({:data, f, ps1, is1}, {:data, f, ps2, is2}, ctx),
    do: unify_lists(ps1 ++ is1, ps2 ++ is2, ctx)

  defp do_unify({:ctor, c, a1}, {:ctor, c, a2}, ctx), do: unify_lists(a1, a2, ctx)

  defp do_unify({:app, f1, x1}, {:app, f2, x2}, ctx) do
    with {:ok, ctx} <- unify(f1, f2, ctx), do: unify(x1, x2, ctx)
  end

  defp do_unify({:pi, d1, c1}, {:pi, d2, c2}, ctx) do
    with {:ok, ctx} <- unify(d1, d2, ctx), do: unify(c1, c2, ctx)
  end

  defp do_unify({:lam, d1, b1}, {:lam, d2, b2}, ctx) do
    with {:ok, ctx} <- unify(d1, d2, ctx), do: unify(b1, b2, ctx)
  end

  # Structurally identical (literals, atoms, etc.).
  defp do_unify(t, t, ctx), do: {:ok, ctx}

  defp do_unify(t1, t2, _ctx), do: {:error, {:cannot_unify, t1, t2}}

  defp unify_lists([], [], ctx), do: {:ok, ctx}

  defp unify_lists([x | xs], [y | ys], ctx) do
    with {:ok, ctx} <- unify(x, y, ctx), do: unify_lists(xs, ys, ctx)
  end

  defp unify_lists(l1, l2, _ctx), do: {:error, {:arity_mismatch, length(l1), length(l2)}}

  defp solve(id, t, ctx) do
    if occurs?(id, t, ctx) do
      {:error, {:occurs_check, id, t}}
    else
      {:ok, MetaCtx.put_solution(ctx, id, t)}
    end
  end

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
