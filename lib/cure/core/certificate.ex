defmodule Cure.Core.Certificate do
  @moduledoc """
  Totality decision procedures the kernel re-runs before certifying a global for
  δ-reduction (design spec §7).

  Operates directly on **Core terms** (not the surface AST), keeping the trusted
  kernel self-contained. Coverage is already enforced by the kernel's `case`
  typing (`check_def` re-runs it), so this module supplies the **termination**
  half.

  ## Termination: structural recursion (guarded by destructors)

  The check is *sound but conservative*. A definition certifies when EITHER it
  makes no self-call, OR there is a fixed argument position `p` such that every
  self-call passes, at position `p`, a variable that is a **structural subterm**
  of the function's `p`-th parameter — i.e. a variable bound by pattern-matching
  (`case`) that parameter, transitively.

  This is the classic guarded-recursion criterion (cf. Coq's guard checker,
  Idris `Core/Termination/SizeChange.idr`). We track, in the current de Bruijn
  frame, the parameter variable itself (the *root*) and the set of variables
  known to be smaller than it; matching on the root or on a known-smaller
  variable makes the branch's freshly-bound fields smaller. A self-call whose
  `p`-th argument lands in that smaller-set is decreasing.

  A conservative *rejection* is always sound — the kernel never certifies a
  function it cannot prove total, so δ never unfolds a non-terminating global.
  Higher-order recursion, non-variable decreasing arguments, and mutual
  recursion fall outside this criterion and are (soundly) rejected.

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
        {params, inner} = peel_lams(body, 0)
        arity = params
        # Try each parameter position as the structurally-decreasing argument.
        # Param i (0-based, outermost first) sits at de Bruijn index arity-1-i.
        Enum.any?(0..(arity - 1)//1, fn p ->
          arity > 0 and guarded?(name, p, inner, arity - 1 - p, MapSet.new())
        end)
    end
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

  # -- structural-recursion guard ---------------------------------------------

  # `guarded?/5` is true when every self-call to `name` inside `term` passes, at
  # position `p`, a variable in `smaller` (structural subterms of the original
  # `p`-th argument). `root` is the current de Bruijn index of that argument;
  # `smaller` the indices proven smaller than it. Both are kept correct across
  # binders by shifting.
  defp guarded?(name, p, term, root, smaller) do
    case spine(term) do
      {{:global, ^name}, args} ->
        # A self-call: its p-th argument must be a known-smaller variable, and
        # each argument must itself be guarded.
        decreasing?(args, p, smaller) and
          Enum.all?(args, &guarded?(name, p, &1, root, smaller))

      {head, args} when args != [] ->
        # Some other application: recurse into head and arguments.
        guarded?(name, p, head, root, smaller) and
          Enum.all?(args, &guarded?(name, p, &1, root, smaller))

      _ ->
        guarded_node?(name, p, term, root, smaller)
    end
  end

  # A bare self-reference (no arguments) cannot be shown decreasing.
  defp guarded_node?(name, _p, {:global, n}, _root, _smaller), do: n != name

  defp guarded_node?(name, p, {:case, scrut, motive, branches}, root, smaller) do
    guarded?(name, p, scrut, root, smaller) and
      guarded?(name, p, motive, root, smaller) and
      Enum.all?(branches, fn {_c, ar, body} ->
        root2 = root + ar
        smaller2 = shift(smaller, ar)

        smaller3 =
          if subterm_scrutinee?(scrut, root, smaller),
            do: add_fields(smaller2, ar),
            else: smaller2

        guarded?(name, p, body, root2, smaller3)
      end)
  end

  defp guarded_node?(name, p, {:lam, d, b}, root, smaller),
    do: guarded?(name, p, d, root, smaller) and guarded?(name, p, b, root + 1, shift(smaller, 1))

  defp guarded_node?(name, p, {:pi, d, c}, root, smaller),
    do: guarded?(name, p, d, root, smaller) and guarded?(name, p, c, root + 1, shift(smaller, 1))

  defp guarded_node?(name, p, {:sigma, a, b}, root, smaller),
    do: guarded?(name, p, a, root, smaller) and guarded?(name, p, b, root + 1, shift(smaller, 1))

  defp guarded_node?(name, p, {:pair, a, b}, root, smaller),
    do: guarded?(name, p, a, root, smaller) and guarded?(name, p, b, root, smaller)

  defp guarded_node?(name, p, {:fst, x}, root, smaller), do: guarded?(name, p, x, root, smaller)
  defp guarded_node?(name, p, {:snd, x}, root, smaller), do: guarded?(name, p, x, root, smaller)

  defp guarded_node?(name, p, {:data, _n, ps, is}, root, smaller),
    do:
      Enum.all?(ps, &guarded?(name, p, &1, root, smaller)) and
        Enum.all?(is, &guarded?(name, p, &1, root, smaller))

  defp guarded_node?(name, p, {:ctor, _n, args}, root, smaller),
    do: Enum.all?(args, &guarded?(name, p, &1, root, smaller))

  defp guarded_node?(name, p, {:eq, t, a, b}, root, smaller),
    do:
      guarded?(name, p, t, root, smaller) and guarded?(name, p, a, root, smaller) and
        guarded?(name, p, b, root, smaller)

  defp guarded_node?(name, p, {:refl, a}, root, smaller), do: guarded?(name, p, a, root, smaller)

  defp guarded_node?(name, p, {:rewrite, pr, m, b}, root, smaller),
    do:
      guarded?(name, p, pr, root, smaller) and guarded?(name, p, m, root, smaller) and
        guarded?(name, p, b, root, smaller)

  # Leaves (vars, literals, types, primitives with no self-call): trivially fine.
  defp guarded_node?(_name, _p, _term, _root, _smaller), do: true

  # The p-th argument (0-based) is a variable known to be structurally smaller.
  defp decreasing?(args, p, smaller) do
    case Enum.at(args, p) do
      {:var, i} -> MapSet.member?(smaller, i)
      _ -> false
    end
  end

  # Matching on the root, or on an already-smaller variable, exposes strictly
  # smaller fields.
  defp subterm_scrutinee?({:var, i}, root, smaller),
    do: i == root or MapSet.member?(smaller, i)

  defp subterm_scrutinee?(_scrut, _root, _smaller), do: false

  # A branch binds `ar` fresh fields at indices 0..ar-1 (outer indices shift up
  # by `ar`, handled by the caller); those fields are the smaller subterms.
  defp add_fields(smaller, ar),
    do: Enum.reduce(0..(ar - 1)//1, smaller, &MapSet.put(&2, &1))

  defp shift(set, by), do: MapSet.new(set, &(&1 + by))

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
