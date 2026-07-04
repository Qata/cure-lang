defmodule Cure.Core.Certificate do
  @moduledoc """
  Totality decision procedures the kernel re-runs before certifying a global for
  δ-reduction (design spec §7).

  Operates directly on **Core terms** (not the surface AST), keeping the trusted
  kernel self-contained. Coverage is already enforced by the kernel's `case`
  typing (`check_def` re-runs it), so this module supplies the **termination**
  half.

  ## Termination: size-change (Lee–Jones–Ben-Amram)

  The check is *sound but conservative*. A definition certifies when EITHER it
  makes no self-call, OR the **size-change principle** holds for its self-calls
  (single-function self-recursion only; see below). This is a port of Idris
  `Core/Termination/SizeChange.idr`, scoped to a single function, and strictly
  generalises the older "one fixed decreasing position" guard.

  For every self-call `f(y₀ … y_{k-1})` we build a `k×k` **change matrix**
  `M[i][j] ∈ {:smaller | :equal | :unknown}` relating call-argument `yᵢ` to
  parameter `xⱼ`. We track, per parameter and across binders (shifted like de
  Bruijn indices):

    * `root`  — the parameter's current de Bruijn index (`:equal` when an
      argument IS this variable),
    * `smaller` — variables proven structural subterms of the parameter, grown
      when a `case` matches the parameter or an already-smaller variable
      (`:smaller`),
    * `recon` — the constructor form the parameter was matched against in the
      current branch. A call-argument **syntactically identical** to that form is
      `:equal` (**reconstruct-equal**: in the branch where `xⱼ` matched
      `C(f₀…fₘ)`, `xⱼ` is definitionally `C(f₀…fₘ)`). This is Idris's
      `sizeEq s t => Same`, and is what certifies Ackermann's inner call
      `ack(S m, n)`. A larger/non-matching form stays `:unknown`; we never derive
      `:smaller` from a reconstruction.

  The self-call matrices are closed under composition (a semiring: `:unknown`
  absorbs, `:equal` neutral, `:smaller` dominates) to a fixpoint, and the
  definition is certified total iff **every idempotent** matrix `M` in the
  closure (`M∘M == M`) has a strictly-decreasing diagonal (some `M[i][i] ==
  :smaller`) — the LJB non-termination criterion, negated.

  A conservative *rejection* is always sound — the kernel never certifies a
  function it cannot prove total, so δ never unfolds a non-terminating global.
  Every entry is `:smaller`/`:equal` only when justified by the tracking above
  (over-approximation); higher-order recursion, non-variable *strictly*-
  decreasing arguments, and mutual recursion fall outside the criterion and are
  (soundly) rejected.

  ## Mutual recursion

  The single-body structural check above sees only one definition, so it cannot
  witness a cycle that runs *through a sibling* global (`f` calls `g`, `g` calls
  `f`): each body is self-call-free, so a naive check would wrongly pass both.
  We close that gap with the signature: a definition is rejected when, following
  calls to *other* globals through `env`, some path returns to it — i.e. it sits
  on a mutual cycle. Well-founded mutual groups are conservatively rejected too
  (incompleteness, not unsoundness); they stay opaque to δ, never a soundness
  hole. A call to a global that does *not* lead back is a plain subroutine call
  and is unaffected, so non-cyclic helpers still certify regardless of the order
  in which the closure certifies them.
  """

  alias Cure.Core.Env

  @doc """
  True when the Core `body` of global `name` is provably terminating under the
  signature `env` (needed to see mutual cycles through sibling globals).
  """
  @spec terminating?(atom(), Cure.Core.Term.t(), Env.t()) :: boolean()
  def terminating?(name, body, env) do
    cond do
      # A cycle through a sibling global — mutual recursion — is rejected.
      mutually_recursive?(name, body, env) ->
        false

      not calls?(name, body) ->
        true

      true ->
        size_change_total?(name, body)
    end
  end

  # -- size-change termination (Lee–Jones–Ben-Amram) --------------------------
  #
  # Generalises the old "one fixed decreasing position" test to the full
  # size-change principle, scoped to single-function self-recursion. We build,
  # for every self-call in the body, a `k×k` **change matrix** relating each
  # call-argument to each parameter (`:smaller | :equal | :unknown`), close the
  # set under path composition to a fixpoint, and certify total iff every
  # *idempotent* matrix in the closure has a strictly-decreasing (`:smaller`)
  # diagonal entry. This is the LJB non-termination criterion negated.
  #
  # Over-approximation is the invariant: an entry is `:smaller`/`:equal` only
  # when justified by structural subterm tracking (a variable proven smaller, or
  # a term equal to a parameter — see `arg_relation/2`); otherwise `:unknown`.
  # Rejection is always sound. A single fixed decreasing position `p` yields an
  # idempotent loop with `M[p][p] = :smaller`, so everything the old check
  # certified still certifies (strict generalisation).
  defp size_change_total?(name, body) do
    {arity, inner} = peel_lams(body, 0)
    st = initial_state(arity)
    matrices = collect_matrices(name, arity, inner, st, []) |> Enum.uniq()
    closure = transitive_closure(matrices)

    Enum.all?(closure, fn m -> not idempotent?(m) or smaller_diagonal?(m) end)
  end

  # Per-parameter tracking, generalised from the old single `root`/`smaller`:
  #   roots[j]    — current de Bruijn index of parameter xⱼ
  #   smallers[j] — indices proven structurally < xⱼ
  #   recons[j]   — the constructor form xⱼ was matched against in this branch
  #                 (a Core ctor-of-vars term, or nil), for reconstruct-equal.
  # Param i (0-based, outermost first) starts at de Bruijn index arity-1-i.
  defp initial_state(arity) do
    %{
      roots: Enum.map(0..(arity - 1)//1, fn i -> arity - 1 - i end),
      smallers: List.duplicate(MapSet.new(), arity),
      recons: List.duplicate(nil, arity)
    }
  end

  # Traverse `term`, collecting a change matrix for every self-call to `name`.
  defp collect_matrices(name, k, term, st, acc) do
    case spine(term) do
      {{:global, ^name}, args} ->
        # A self-call: its own change matrix, then recurse into the arguments
        # (a nested self-call can sit inside an argument — e.g. Ackermann).
        acc = [build_matrix(k, args, st) | acc]
        Enum.reduce(args, acc, fn a, ac -> collect_matrices(name, k, a, st, ac) end)

      {head, args} when args != [] ->
        acc = collect_matrices(name, k, head, st, acc)
        Enum.reduce(args, acc, fn a, ac -> collect_matrices(name, k, a, st, ac) end)

      _ ->
        collect_node(name, k, term, st, acc)
    end
  end

  # `{:case,…}` is the only binder that refines the per-parameter tracking:
  # each branch shifts the frame by its arity, and matching a parameter (or a
  # known-smaller variable) exposes the branch's fields as smaller. Matching a
  # parameter *exactly* also records its reconstruction for reconstruct-equal.
  defp collect_node(name, k, {:case, scrut, motive, branches}, st, acc) do
    acc = collect_matrices(name, k, scrut, st, acc)
    acc = collect_matrices(name, k, motive, st, acc)

    Enum.reduce(branches, acc, fn {ctor, ar, body}, ac ->
      st2 = refine_branch(st, scrut, ctor, ar)
      collect_matrices(name, k, body, st2, ac)
    end)
  end

  defp collect_node(name, k, {:lam, d, b}, st, acc),
    do: collect_matrices(name, k, b, shift_state(st, 1), collect_matrices(name, k, d, st, acc))

  defp collect_node(name, k, {:pi, d, c}, st, acc),
    do: collect_matrices(name, k, c, shift_state(st, 1), collect_matrices(name, k, d, st, acc))

  defp collect_node(name, k, {:sigma, a, b}, st, acc),
    do: collect_matrices(name, k, b, shift_state(st, 1), collect_matrices(name, k, a, st, acc))

  defp collect_node(name, k, {:pair, a, b}, st, acc),
    do: collect_matrices(name, k, b, st, collect_matrices(name, k, a, st, acc))

  defp collect_node(name, k, {:fst, x}, st, acc), do: collect_matrices(name, k, x, st, acc)
  defp collect_node(name, k, {:snd, x}, st, acc), do: collect_matrices(name, k, x, st, acc)

  defp collect_node(name, k, {:data, _n, ps, is}, st, acc) do
    acc = Enum.reduce(ps, acc, fn t, ac -> collect_matrices(name, k, t, st, ac) end)
    Enum.reduce(is, acc, fn t, ac -> collect_matrices(name, k, t, st, ac) end)
  end

  defp collect_node(name, k, {:ctor, _n, args}, st, acc),
    do: Enum.reduce(args, acc, fn a, ac -> collect_matrices(name, k, a, st, ac) end)

  defp collect_node(name, k, {:eq, t, a, b}, st, acc) do
    acc = collect_matrices(name, k, t, st, acc)
    acc = collect_matrices(name, k, a, st, acc)
    collect_matrices(name, k, b, st, acc)
  end

  defp collect_node(name, k, {:refl, a}, st, acc), do: collect_matrices(name, k, a, st, acc)

  defp collect_node(name, k, {:rewrite, pr, m, b}, st, acc) do
    acc = collect_matrices(name, k, pr, st, acc)
    acc = collect_matrices(name, k, m, st, acc)
    collect_matrices(name, k, b, st, acc)
  end

  # Leaves (vars, literals, types, other globals): no self-call, no matrix.
  defp collect_node(_name, _k, _term, _st, acc), do: acc

  # Enter a case branch matching `scrut` with constructor `ctor`/arity `ar`:
  # shift the frame by `ar`, then for each parameter decide whether `scrut`
  # exposes new smaller fields and (for an exact parameter match) a reconstruction.
  defp refine_branch(st, scrut, ctor, ar) do
    shifted = shift_state(st, ar)
    recon = build_recon(ctor, ar)

    idx = scrut_index(scrut)

    smallers =
      Enum.zip_with([st.roots, st.smallers, shifted.smallers], fn [root, sm0, sm_sh] ->
        if idx != nil and (idx == root or MapSet.member?(sm0, idx)),
          do: add_fields(sm_sh, ar),
          else: sm_sh
      end)

    recons =
      Enum.zip_with([st.roots, shifted.recons], fn [root, rc_sh] ->
        # reconstruct-EQUAL only on an EXACT parameter match (`scrut` IS xⱼ):
        # then xⱼ is definitionally `ctor(fields)`. A merely-smaller scrutinee
        # never yields `:equal` (guardrail: never `:smaller`/over-claim from a
        # reconstruction), so its recon is left untouched.
        if idx != nil and idx == root, do: recon, else: rc_sh
      end)

    %{roots: shifted.roots, smallers: smallers, recons: recons}
  end

  defp scrut_index({:var, i}), do: i
  defp scrut_index(_), do: nil

  # The reconstruction of `ctor(f₀ … f_{ar-1})` in a freshly-entered branch. The
  # kernel binds ctor fields so the LAST field is de Bruijn 0 (see `eval`'s
  # `reverse(args) ++ env`), so field fᵢ is index `ar-1-i` — i.e. the field list
  # is `[var (ar-1), …, var 0]`. This must be byte-identical to the term the
  # elaborator emits for `ctor(f₀ … f_{ar-1})`, or reconstruct-equal soundly
  # fails to fire (→ `:unknown`).
  defp build_recon(ctor, 0), do: {:ctor, ctor, []}

  defp build_recon(ctor, ar),
    do: {:ctor, ctor, Enum.map((ar - 1)..0//-1, &{:var, &1})}

  # -- change matrix ----------------------------------------------------------

  # Build the `k×k` matrix for a self-call: M[i][j] = relation of call-arg yᵢ to
  # parameter xⱼ. Rows are call-arguments, columns are parameters.
  defp build_matrix(k, args, st) do
    Enum.map(0..(k - 1)//1, fn i ->
      arg = Enum.at(args, i)
      Enum.map(0..(k - 1)//1, fn j -> arg_relation(arg, param_view(st, j)) end)
    end)
  end

  defp param_view(st, j),
    do: %{root: Enum.at(st.roots, j), smaller: Enum.at(st.smallers, j), recon: Enum.at(st.recons, j)}

  # Relation of a single call-argument to a single parameter.
  #   :smaller — a variable proven structurally < xⱼ
  #   :equal   — the same de Bruijn var as xⱼ, OR a constructor application
  #              syntactically identical to xⱼ's reconstruction (reconstruct-equal)
  #   :unknown — anything else (never claim ≤ for a possibly-larger term)
  defp arg_relation(nil, _pv), do: :unknown

  defp arg_relation({:var, i}, %{root: root, smaller: smaller}) do
    cond do
      MapSet.member?(smaller, i) -> :smaller
      i == root -> :equal
      true -> :unknown
    end
  end

  defp arg_relation({:ctor, _c, _as} = arg, %{recon: recon}) do
    if recon != nil and arg == recon, do: :equal, else: :unknown
  end

  defp arg_relation(_arg, _pv), do: :unknown

  # -- SizeChange semiring ----------------------------------------------------

  # Path composition (∘): Unknown absorbs, Equal is neutral, Smaller dominates.
  defp pathmul(:unknown, _), do: :unknown
  defp pathmul(_, :unknown), do: :unknown
  defp pathmul(:smaller, _), do: :smaller
  defp pathmul(_, :smaller), do: :smaller
  defp pathmul(:equal, :equal), do: :equal

  # Parallel arcs / matrix-mult sum: keep the strongest (Smaller > Equal > Unknown).
  defp add_rel(:smaller, _), do: :smaller
  defp add_rel(_, :smaller), do: :smaller
  defp add_rel(:equal, _), do: :equal
  defp add_rel(_, :equal), do: :equal
  defp add_rel(:unknown, :unknown), do: :unknown

  # -- matrix operations ------------------------------------------------------

  # Diagrammatic composition of two `k×k` matrices: (A∘B)[i][j] = Σₖ A[i][k]·B[k][j].
  # We add both `compose(a,b)` and `compose(b,a)` during closure, so the set is
  # closed under composition regardless of this convention's orientation.
  defp compose(a, b) do
    k = length(a)
    if k == 0 do
      []
    else
      Enum.map(0..(k - 1)//1, fn i ->
        Enum.map(0..(k - 1)//1, fn j ->
          Enum.reduce(0..(k - 1)//1, :unknown, fn kk, acc ->
            add_rel(acc, pathmul(entry(a, i, kk), entry(b, kk, j)))
          end)
        end)
      end)
    end
  end

  defp entry(m, i, j), do: m |> Enum.at(i) |> Enum.at(j)

  # Close the initial self-call matrices under composition to a fixpoint. The
  # lattice is finite (`k×k` over 3 values), and dedup by matrix equality makes
  # the worklist strictly shrink, so this always terminates.
  defp transitive_closure(matrices) do
    set = MapSet.new(matrices)
    close(MapSet.to_list(set), set)
  end

  defp close([], set), do: MapSet.to_list(set)

  defp close([m | work], set) do
    {work, set} =
      Enum.reduce(MapSet.to_list(set), {work, set}, fn n, {wk, st} ->
        [compose(m, n), compose(n, m)]
        |> Enum.reduce({wk, st}, fn c, {wk2, st2} ->
          if MapSet.member?(st2, c),
            do: {wk2, st2},
            else: {[c | wk2], MapSet.put(st2, c)}
        end)
      end)

    close(work, set)
  end

  defp idempotent?(m), do: compose(m, m) == m

  defp smaller_diagonal?(m) do
    k = length(m)
    k > 0 and Enum.any?(0..(k - 1)//1, fn i -> entry(m, i, i) == :smaller end)
  end

  # -- mutual-recursion detection ---------------------------------------------

  # `name` sits on a mutual cycle iff, following calls to globals *other than*
  # `name` through the signature, some path returns to `name`. Direct
  # self-recursion (name→name) is excluded here — it is the structural guard's
  # job — so this only fires on cycles of length ≥ 2.
  defp mutually_recursive?(name, body, env) do
    callees = body |> called_globals() |> MapSet.delete(name) |> MapSet.to_list()
    reaches?(env, callees, name, MapSet.new())
  end

  defp reaches?(_env, [], _target, _visited), do: false

  defp reaches?(env, [g | rest], target, visited) do
    cond do
      g == target ->
        true

      MapSet.member?(visited, g) ->
        reaches?(env, rest, target, visited)

      true ->
        next =
          case Env.get_def(env, g) do
            %{body: b} -> b |> called_globals() |> MapSet.to_list()
            _ -> []
          end

        reaches?(env, next ++ rest, target, MapSet.put(visited, g))
    end
  end

  # Every global name referenced anywhere in a Core term.
  defp called_globals(term), do: gather_globals(term, MapSet.new())
  defp gather_globals({:global, n}, acc), do: MapSet.put(acc, n)
  defp gather_globals(t, acc) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.reduce(acc, &gather_globals/2)
  defp gather_globals(l, acc) when is_list(l), do: Enum.reduce(l, acc, &gather_globals/2)
  defp gather_globals(_, acc), do: acc

  # -- per-parameter frame maintenance ----------------------------------------

  # Shift every tracked de Bruijn index up by `by` on entering `by` binders.
  defp shift_state(st, by) do
    %{
      roots: Enum.map(st.roots, &(&1 + by)),
      smallers: Enum.map(st.smallers, &shift(&1, by)),
      recons: Enum.map(st.recons, fn nil -> nil; t -> shift_term(t, by) end)
    }
  end

  # A branch binds `ar` fresh fields at indices 0..ar-1 (outer indices already
  # shifted up by `ar`); those fields are the smaller subterms.
  defp add_fields(smaller, 0), do: smaller

  defp add_fields(smaller, ar),
    do: Enum.reduce(0..(ar - 1)//1, smaller, &MapSet.put(&2, &1))

  defp shift(set, by), do: MapSet.new(set, &(&1 + by))

  # Shift free de Bruijn vars in a reconstruction term. Reconstructions are only
  # ever built as constructor applications of variables (no inner binders), so a
  # blanket var-shift is exact.
  defp shift_term({:var, i}, by), do: {:var, i + by}
  defp shift_term({:ctor, c, args}, by), do: {:ctor, c, Enum.map(args, &shift_term(&1, by))}
  defp shift_term(other, _by), do: other

  # -- spine / lambda peeling -------------------------------------------------

  # Flatten a left-nested application `((h a) b) …` into `{h, [a, b, …]}`.
  defp spine(term), do: spine(term, [])
  defp spine({:app, f, a}, acc), do: spine(f, [a | acc])
  defp spine(head, acc), do: {head, acc}

  # Count leading lambdas and return the wrapped body.
  defp peel_lams({:lam, _d, b}, n), do: peel_lams(b, n + 1)
  defp peel_lams(term, n), do: {n, term}

  # -- self-call detection (fast path) ----------------------------------------

  defp calls?(name, {:global, n}), do: n == name
  defp calls?(name, {:pi, d, c}), do: calls?(name, d) or calls?(name, c)
  defp calls?(name, {:lam, d, b}), do: calls?(name, d) or calls?(name, b)
  defp calls?(name, {:sigma, a, b}), do: calls?(name, a) or calls?(name, b)
  defp calls?(name, {:app, f, a}), do: calls?(name, f) or calls?(name, a)
  defp calls?(name, {:pair, a, b}), do: calls?(name, a) or calls?(name, b)
  defp calls?(name, {:fst, p}), do: calls?(name, p)
  defp calls?(name, {:snd, p}), do: calls?(name, p)

  defp calls?(name, {:data, _n, ps, is}),
    do: Enum.any?(ps, &calls?(name, &1)) or Enum.any?(is, &calls?(name, &1))

  defp calls?(name, {:ctor, _n, args}), do: Enum.any?(args, &calls?(name, &1))

  defp calls?(name, {:case, s, m, brs}),
    do:
      calls?(name, s) or calls?(name, m) or
        Enum.any?(brs, fn {_c, _ar, b} -> calls?(name, b) end)

  defp calls?(name, {:eq, t, a, b}), do: calls?(name, t) or calls?(name, a) or calls?(name, b)
  defp calls?(name, {:refl, a}), do: calls?(name, a)

  defp calls?(name, {:rewrite, p, m, b}),
    do: calls?(name, p) or calls?(name, m) or calls?(name, b)

  defp calls?(_name, _term), do: false
end
