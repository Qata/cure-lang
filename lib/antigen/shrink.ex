defmodule Antigen.Shrink do
  @moduledoc """
  Value-level greedy post-shrink. Minimizes a reified `Challenge` artifact under a
  caller-supplied same-violation-shape predicate, via untyped structural rewrites.
  Purely deterministic (fixed enumeration, no RNG/clock); bounded by a step budget.
  """
  alias Antigen.{Challenge, Coverage}
  alias Cure.Core.Term

  @minimal_atoms [{:ctor, :Z, []}, {:ctor, :vnil, []}, {:ctor, :T, []}, {:type, 0}]

  @spec minimize(Challenge.t(), (Challenge.t() -> boolean()), non_neg_integer()) :: Challenge.t()
  def minimize(%Challenge{} = ch, pred, budget) do
    {out, _b} = sweep(ch, pred, budget)
    out
  end

  # greedy: first accepted candidate → restart sweep; else fixpoint. Budget = pred calls.
  defp sweep(ch, pred, budget) do
    case first_accepted(candidates(ch), pred, budget) do
      {:accepted, ch2, budget2} -> sweep(reseed(ch2), pred, budget2)
      {:none, budget2} -> {ch, budget2}
    end
  end

  defp first_accepted(_cands, _pred, 0), do: {:none, 0}
  defp first_accepted([], _pred, b), do: {:none, b}
  defp first_accepted([k | rest], pred, b) do
    if well_formed?(k) do
      if safe_pred(pred, k), do: {:accepted, k, b - 1}, else: first_accepted(rest, pred, b - 1)
    else
      first_accepted(rest, pred, b)   # shape-invalid: no pred call, no budget spent
    end
  end

  defp safe_pred(pred, k) do
    pred.(k)
  rescue
    _ -> false
  catch
    _, _ -> false
  end

  defp reseed(%Challenge{} = ch), do: %{ch | seed: :erlang.phash2({ch.kind, ch.payload})}

  # ── candidate enumeration (pinned order: ctx → type → term) ──────────────────
  # Task 1 covers type + term. Task 2 prepends ctx-drop candidates.
  defp candidates(%Challenge{payload: p} = ch) do
    field_cands(ch, :type, p.type) ++ field_cands(ch, :term, p.term)
  end

  defp field_cands(ch, field, t) do
    Enum.map(term_candidates(t), fn t2 ->
      %{ch | payload: Map.put(ch.payload, field, t2)}
    end)
  end

  # all single-edit variants of a term, pre-order (edits AT this node before children)
  defp term_candidates(t) do
    here = rule1(t) ++ rule2(t) ++ rule4(t)
    deeper =
      Enum.flat_map(child_slots(t), fn {rebuild, child} ->
        Enum.map(term_candidates(child), rebuild)
      end)
    here ++ deeper
  end

  # rule 1: subterm → minimal atom, only for compound (>1 node) positions
  defp rule1(t) do
    if node_count(t) > 1, do: @minimal_atoms, else: []
  end

  # rule 2: S^k Z → S^(k-1) Z
  defp rule2({:ctor, :S, [n]}), do: [n]
  defp rule2(_), do: []

  # rule 4: structural unwrap (Task 1: non-ctx rules incl. lam/case de Bruijn)
  defp rule4({:app, f, a}), do: [f, a]
  defp rule4({:ctor, _n, args}), do: args
  defp rule4({:fst, p}), do: [p]
  defp rule4({:snd, p}), do: [p]
  defp rule4({:pair, a, b}), do: [a, b]
  defp rule4({:case, scrut, _m, branches}) do
    [scrut | for({_c, 0, body} <- branches, do: body)]   # scrut + arity-0 branch bodies only
  end
  defp rule4({:lam, _dom, body}) do
    if occurs?(body, 0), do: [], else: [Term.shift(body, -1, 0)]
  end
  defp rule4(_), do: []

  # child slots: {rebuild_fn, child} for every immediate sub-term (all Core formers)
  defp child_slots({:app, f, a}), do: [{&{:app, &1, a}, f}, {&{:app, f, &1}, a}]
  defp child_slots({:lam, d, b}), do: [{&{:lam, &1, b}, d}, {&{:lam, d, &1}, b}]
  defp child_slots({:pi, d, c}), do: [{&{:pi, &1, c}, d}, {&{:pi, d, &1}, c}]
  defp child_slots({:sigma, a, b}), do: [{&{:sigma, &1, b}, a}, {&{:sigma, a, &1}, b}]
  defp child_slots({:pair, a, b}), do: [{&{:pair, &1, b}, a}, {&{:pair, a, &1}, b}]
  defp child_slots({:fst, p}), do: [{&{:fst, &1}, p}]
  defp child_slots({:snd, p}), do: [{&{:snd, &1}, p}]
  defp child_slots({:ctor, n, args}), do: slot_list(args, &{:ctor, n, &1})
  defp child_slots({:data, n, ps, is}) do
    slot_list(ps, &{:data, n, &1, is}) ++ slot_list(is, &{:data, n, ps, &1})
  end
  defp child_slots({:case, s, m, brs}) do
    [{&{:case, &1, m, brs}, s}, {&{:case, s, &1, brs}, m}] ++
      (Enum.with_index(brs)
       |> Enum.map(fn {{c, ar, body}, i} ->
         {fn nb -> {:case, s, m, List.replace_at(brs, i, {c, ar, nb})} end, body}
       end))
  end
  defp child_slots({:eq, ty, a, b}) do
    [{&{:eq, &1, a, b}, ty}, {&{:eq, ty, &1, b}, a}, {&{:eq, ty, a, &1}, b}]
  end
  defp child_slots({:refl, a}), do: [{&{:refl, &1}, a}]
  # :rewrite/:prim are real Core formers (Cure.Core.Term's node taxonomy) that
  # `Term.gen_term`/`Antigen.Generators.Mutation` never construct today, so
  # this clause is presently unreached — included anyway so term_candidates
  # doesn't silently stop descending if either ever appears (no binder in
  # either, matching Term.shift's own :rewrite/:prim clauses — no cutoff bump).
  defp child_slots({:rewrite, p, m, b}) do
    [{&{:rewrite, &1, m, b}, p}, {&{:rewrite, p, &1, b}, m}, {&{:rewrite, p, m, &1}, b}]
  end
  defp child_slots({:prim, op, args}), do: slot_list(args, &{:prim, op, &1})
  defp child_slots(_leaf), do: []

  defp slot_list(elems, rebuild_list) do
    elems
    |> Enum.with_index()
    |> Enum.map(fn {e, i} -> {fn ne -> rebuild_list.(List.replace_at(elems, i, ne)) end, e} end)
  end

  # ── measures / helpers ──────────────────────────────────────────────────────
  @spec size(Challenge.t()) :: non_neg_integer()
  def size(%Challenge{payload: p}),
    do: node_count(p.term) + length(p.ctx) + numeral_magnitude(p.term)

  defp node_count(t) when is_tuple(t),
    do: 1 + (t |> Tuple.to_list() |> tl() |> Enum.map(&node_count/1) |> Enum.sum())
  defp node_count(l) when is_list(l), do: l |> Enum.map(&node_count/1) |> Enum.sum()
  defp node_count(_), do: 0

  defp numeral_magnitude({:ctor, :S, [n]}), do: 1 + numeral_magnitude(n)
  defp numeral_magnitude(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> tl() |> Enum.map(&numeral_magnitude/1) |> Enum.sum()
  defp numeral_magnitude(l) when is_list(l), do: l |> Enum.map(&numeral_magnitude/1) |> Enum.sum()
  defp numeral_magnitude(_), do: 0

  # free-occurrence of de-Bruijn index k (crosses binders, incrementing) — mirrors Runner.occurs?/2
  def occurs?({:var, k}, k), do: true
  def occurs?({:var, _}, _k), do: false
  def occurs?({:lam, d, b}, k), do: occurs?(d, k) or occurs?(b, k + 1)
  def occurs?({:pi, d, c}, k), do: occurs?(d, k) or occurs?(c, k + 1)
  def occurs?({:sigma, a, b}, k), do: occurs?(a, k) or occurs?(b, k + 1)
  def occurs?({:case, s, m, brs}, k) do
    occurs?(s, k) or occurs?(m, k) or
      Enum.any?(brs, fn {_c, ar, body} -> occurs?(body, k + ar) end)
  end
  def occurs?(t, k) when is_tuple(t), do: t |> Tuple.to_list() |> tl() |> Enum.any?(&occurs?(&1, k))
  def occurs?(l, k) when is_list(l), do: Enum.any?(l, &occurs?(&1, k))
  def occurs?(_leaf, _k), do: false

  # shape-only well-formedness (reimplements Runner.well_formed?/1 to avoid a cycle)
  defp well_formed?(c) do
    c |> Coverage.terms_of() |> Enum.all?(&Term.term?/1)
  rescue
    _ -> false
  end
end
