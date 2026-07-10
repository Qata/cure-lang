defmodule Cure.Elab.Relevance do
  @moduledoc """
  The `{0,ω}` relevance check (M8.3) — the elaborator-side pass that makes
  erasure SOUND. It is the exact dual of `Cure.Elab.Erase`: erasure drops every
  `:erased` argument position, and this check guarantees no `:erased` binder is
  ever *used* in a position erasure would drop it from — so the runtime term
  `Erase.erase` produces never references a binding that no longer exists.

  This lives in the untrusted elaborator (E-layer), NOT the kernel — exactly like
  Idris, where `Core/LinearCheck.idr` runs outside the core conversion checker.
  The kernel stays quantity-blind; `declarations.ex` calls this after
  `Kernel.check` succeeds and before the def is registered/erased.

  ## Idris grounding (Core/LinearCheck.idr, 0/ω slice)

  `lcheck rig erase env term` threads a usage count; a `Rig0` (our `:erased`)
  binder must have usage 0 in every RELEVANT position. The multiplier is
  `checkRig = rigf |*| rig` (App case) with `erased |*| _ = erased`, so a binder
  counts only where the ambient `rig` is not erased:

    * RELEVANT (a `0` binder here is a violation):
      - returned as the value (`:returned`);
      - passed in a `:present` argument position of a call/constructor
        (`:present_arg`);
      - scrutinised as a `case` discriminant (`:scrutinee`);
      - applied as a function head (`:applied`).
    * EXEMPT (checked at `erased`, does not count): type/index positions
      (`{:pi}`/`{:data}` — Pi domains, the `case`
      motive), erased argument positions, and collapsible-family proof
      elimination (the J/subst transport's scrutinee).

  Only the 0/ω slice is ported (per the reference manifest caveat: read Idris
  core as ω-except-erased; the linear `1` multiplicity is out of scope).

  ## de Bruijn convention

  `check/4` receives the RAW body term (before `wrap_binders(:lam, …)`), so the
  `P = length(quantities)` parameters are its outermost free variables: parameter
  `p` (0-based, telescope order) occurs at de Bruijn index `P-1-p`. Walking with
  an initial `depth = P` makes `level = depth-1-i` recover the parameter index
  directly, and inner binders (`:lam` bodies, `case` branch patterns) simply
  increment `depth` — a free occurrence of parameter `p` at extra depth `d` is
  index `P-1-p+d`, still `level = p`. Levels `>= P` are inner binders, never
  parameters, so never flagged.
  """

  alias Cure.Core.{Env, Inductive}

  @type site :: :returned | :present_arg | :scrutinee | :applied

  @doc """
  Verify that no `:erased` parameter of `name` is used relevantly in `body`
  (the raw, pre-lambda-wrapped body term). `quantities` is the per-parameter
  `{0,ω}` list (`nil` = all runtime-relevant). Returns `:ok`, or the first
  violation as `{:error, {:erased_used_relevantly, %{def:, binder:, site:}}}`
  where `binder` is the 0-based parameter index.
  """
  @spec check(Env.t(), atom(), [atom()] | nil, Cure.Core.Term.t()) ::
          :ok | {:error, {:erased_used_relevantly, %{def: atom(), binder: non_neg_integer(), site: site()}}}
  def check(_env, _name, quantities, _body) when not is_list(quantities), do: :ok

  def check(env, name, quantities, body) do
    erased =
      quantities
      |> Enum.with_index()
      |> Enum.filter(fn {q, _idx} -> q == :erased end)
      |> Enum.map(fn {_q, idx} -> idx end)
      |> MapSet.new()

    # No early-out when `erased` is empty. Erasedness does not only originate at
    # the signature: matching a constructor with an erased FIELD introduces a fresh
    # erased binder (see the `:case` clause's `branch_erased` fold), so an ordinary
    # all-`:present` function can still return a value that `Erase.erase` deletes.
    # Idris's `lcheck` (Core/LinearCheck.idr) likewise always walks the body — there
    # is one notion of erased, not a checked and an unchecked one.
    walk(body, length(quantities), :returned, %{env: env, name: name, erased: erased})
  end

  # --- relevant positions: an erased-parameter occurrence here is a violation --

  defp walk({:var, i}, depth, site, st) do
    level = depth - 1 - i

    if level >= 0 and MapSet.member?(st.erased, level) do
      {:error, {:erased_used_relevantly, %{def: st.name, binder: level, site: site}}}
    else
      :ok
    end
  end

  # A closure value being returned: its domain is a type position (exempt); its
  # body is relevant. Descending binds one more variable.
  defp walk({:lam, _g, _dom, body}, depth, _site, st), do: walk(body, depth + 1, :returned, st)

  # `:let` — the ascription is a type position (exempt). The VALUE is always
  # evaluated at runtime (`X = Val` in the emitted BEAM), so it is a relevant
  # position regardless of whether the body uses the binder; that is the honest
  # dual of `Emit`'s unconditional bind. The body inherits the let's own site and
  # binds one more variable.
  defp walk({:let, _g, _ty, val, body}, depth, site, st) do
    with :ok <- walk(val, depth, :present_arg, st), do: walk(body, depth + 1, site, st)
  end

  # Application spine: the head is `:applied`; each argument is relevant iff the
  # callee's quantity for that position is `:present` (erased positions exempt —
  # the dual of `Erase.erase`'s `{:app, …}` filtering).
  defp walk({:app, _f, _x} = app, depth, _site, st) do
    {head, args} = spine(app, [])
    quantities = callee_quantities(head, length(args), st.env)

    with :ok <- walk(head, depth, :applied, st) do
      args
      |> Enum.zip(quantities)
      |> each(fn {arg, q} ->
        if q == :present, do: walk(arg, depth, :present_arg, st), else: :ok
      end)
    end
  end

  # Constructor: same present/erased split, via the family's ctor quantities.
  defp walk({:ctor, cname, args}, depth, _site, st) do
    quantities =
      (Inductive.ctor_quantities(st.env, cname) || List.duplicate(:present, length(args)))
      |> pad(length(args))

    args
    |> Enum.zip(quantities)
    |> each(fn {arg, q} ->
      if q == :present, do: walk(arg, depth, :present_arg, st), else: :ok
    end)
  end

  # `case`: the discriminant is scrutinised (relevant); the motive is a type
  # position (exempt); each branch body runs under `arity` fresh pattern binders.
  #
  # EXCEPTION — collapsible-family elimination (Phase B, spec "Phase-B encoding
  # amendment"): a case whose single branch names the sole constructor of its
  # family, all of whose fields are erased (e.g. `Equivalent`'s `reflexive`),
  # inspects nothing at runtime — the matched shape is forced. Such a scrutinee
  # is a PROOF position, exempt like the retired `{:rewrite}` node's proof
  # (Idris2 permits case on a 0-multiplicity value precisely when the match has
  # a single uninformative alternative; Brady/McBride/McKinna's collapsible
  # families). Sound only because `Erase.erase` drops the whole case for the
  # SAME class (its `collapsible_ctor?/3` must stay in lockstep with
  # `collapsible_case?/2` here), so the exempted scrutinee never survives into
  # the runtime term.
  #
  # Each branch additionally folds its constructor's own erased-field positions
  # into the tracked set — a named erased pattern binder (spec 2026-07-08 §2.3)
  # is policed exactly like an erased top-level parameter.
  defp walk({:case, scrut, _motive, branches}, depth, _site, st) do
    scrut_check =
      if collapsible_case?(st.env, branches),
        do: :ok,
        else: walk(scrut, depth, :scrutinee, st)

    with :ok <- scrut_check do
      each(branches, fn {cname, arity, body} ->
        ctor_qs =
          Inductive.ctor_quantities(st.env, cname) || List.duplicate(:present, arity)

        branch_erased =
          ctor_qs
          |> Enum.with_index()
          |> Enum.filter(fn {q, _p} -> q == :erased end)
          |> Enum.map(fn {_q, p} -> depth + p end)

        st2 = %{st | erased: Enum.into(branch_erased, st.erased)}
        walk(body, depth + arity, :returned, st2)
      end)
    end
  end

  # --- exempt positions: type formers and proof terms carry no runtime value ---
  defp walk({:pi, _g, _d, _c}, _depth, _site, _st), do: :ok
  defp walk({:data, _n, _ps, _is}, _depth, _site, _st), do: :ok

  # Leaves (`:global`, `:type`, `:hole`, literals) and any other form: no
  # erased-parameter occurrence to account for. Mirrors `Erase`'s leaf clause.
  defp walk(_leaf, _depth, _site, _st), do: :ok

  # Exactly one branch, naming its family's ONLY constructor, whose fields are
  # all erased (and nonempty — a nullary single-ctor family like Unit keeps
  # today's relevant-scrutinee treatment; this rule targets proof-like carriers).
  defp collapsible_case?(env, [{cname, arity, _body}]) do
    with dname when dname != nil <- Inductive.ctor_family(env, cname),
         [_only] <- Inductive.ctors_of(env, dname),
         qs when is_list(qs) <- Inductive.ctor_quantities(env, cname) do
      arity == length(qs) and qs != [] and Enum.all?(qs, &(&1 == :erased))
    else
      _ -> false
    end
  end

  defp collapsible_case?(_env, _branches), do: false

  defp spine({:app, f, x}, acc), do: spine(f, [x | acc])
  defp spine(head, acc), do: {head, acc}

  defp callee_quantities({:global, name}, arity, env) do
    case Env.get_def(env, name) do
      %{quantities: qs} when is_list(qs) -> pad(qs, arity)
      _ -> List.duplicate(:present, arity)
    end
  end

  defp callee_quantities({:ctor, cname, _args}, arity, env) do
    (Inductive.ctor_quantities(env, cname) || List.duplicate(:present, arity)) |> pad(arity)
  end

  defp callee_quantities(_other, arity, _env), do: List.duplicate(:present, arity)

  # Conservative padding: an argument position with no declared quantity is
  # treated as `:present` (relevant), never silently exempted.
  defp pad(qs, n) when length(qs) == n, do: qs

  # Over-application: the extra arguments apply to the callee's RESULT and are always present.
  defp pad(qs, n) when length(qs) < n, do: qs ++ List.duplicate(:present, n - length(qs))

  # Fewer arguments than declared quantities: by `Erase.erase/2`'s own convention, the term is
  # ALREADY ERASED — its erased arguments have been dropped, so the survivors occupy the
  # ORIGINAL trailing positions, not the leading ones. `Enum.take(qs, n)` realigned them onto
  # the leading labels, and a genuinely present survivor landing on an `:erased` label was
  # silently exempted from the relevance check. Erase guards this exact case ("re-zipping the
  # full quantity vector against the shrunk arg list would realign survivors onto leading
  # positions and DROP them"); Relevance, its documented dual, did not. Every surviving
  # argument of an already-erased term is relevant.
  defp pad(_qs, n), do: List.duplicate(:present, n)

  defp each(list, fun) do
    Enum.reduce_while(list, :ok, fn item, :ok ->
      case fun.(item) do
        :ok -> {:cont, :ok}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end
end
