defmodule Cure.Elab.Erase do
  @moduledoc """
  {0,ω} erasure of Core terms (design spec §8 / M9.1).

  Dependent indices exist only for type-checking; at runtime they carry no
  information, so erasure drops every `:erased` constructor argument (the
  quantities recorded by the elaborator, M8.3). What remains is a plain,
  non-dependent value the runtime can represent directly — e.g. `seq` erases from
  its seven-argument dependent form to the two stream functions it actually
  stores.

  `has_hole?/1` reports whether a term still contains an unfilled hole; a program
  with holes typechecks but must not be emitted (§6 negative #5).
  """

  alias Cure.Core.Inductive

  @doc "Erase a Core term to its runtime form (drop erased constructor arguments)."
  @spec erase(Cure.Core.Env.t(), Cure.Core.Term.t()) :: Cure.Core.Term.t()
  def erase(env, {:ctor, cname, args}) do
    quantities = Inductive.ctor_quantities(env, cname) || List.duplicate(:present, length(args))

    if length(args) == length(quantities) do
      kept =
        args
        |> Enum.zip(quantities)
        |> Enum.filter(fn {_arg, q} -> q == :present end)
        |> Enum.map(fn {arg, _q} -> erase(env, arg) end)

      {:ctor, cname, kept}
    else
      # Fewer (or more) args than the ctor's full arity means the term is already
      # erased — re-zipping the full quantity vector against the shrunk arg list
      # would realign survivors onto leading positions and drop them. Keep every
      # arg and only recurse, so erase(erase(t)) == erase(t).
      {:ctor, cname, Enum.map(args, &erase(env, &1))}
    end
  end

  def erase(env, {:lam, dom, body}), do: {:lam, erase(env, dom), erase(env, body)}

  def erase(env, {:app, _f, _x} = app) do
    {head, args} = spine(app, [])

    case head do
      {:global, name} ->
        quantities =
          case Cure.Core.Env.get_def(env, name) do
            %{quantities: qs} when is_list(qs) -> qs
            _ -> List.duplicate(:present, length(args))
          end

        if length(args) >= length(quantities) do
          # Full or over-application: filter the callee's own parameters by their
          # quantity, and keep every argument beyond them (those apply to the
          # *result* `mk()(z)` and are always present).
          padded = quantities ++ List.duplicate(:present, length(args) - length(quantities))

          args
          |> Enum.zip(padded)
          |> Enum.filter(fn {_arg, q} -> q == :present end)
          |> Enum.map(fn {arg, _q} -> erase(env, arg) end)
          |> Enum.reduce({:global, name}, fn arg, acc -> {:app, acc, arg} end)
        else
          # Fewer args than the callee's parameters means the erased ones were
          # already dropped by a prior pass; re-filtering would realign the full
          # quantity vector and drop a present arg. Keep all, recurse — idempotent.
          args
          |> Enum.map(&erase(env, &1))
          |> Enum.reduce({:global, name}, fn arg, acc -> {:app, acc, arg} end)
        end

      # A constructor heading a curried spine is the same term as the flat `{:ctor, name, args}`
      # node, and must erase to the same runtime shape. The bare fallback below kept every
      # argument, erased ones included — so an erased index literally survived into the runtime
      # term, and two Core encodings of one value erased differently. `Relevance`, the dual
      # pass, already anticipates this head shape in `callee_quantities/3`; `Erase` did not.
      {:ctor, cname, head_args} ->
        all = head_args ++ args
        quantities = Inductive.ctor_quantities(env, cname) || List.duplicate(:present, length(all))

        if length(all) >= length(quantities) do
          # Saturated (or over-applied, when a field is itself a function): the leading
          # `length(quantities)` arguments are the ctor's own fields and collapse into the flat
          # node; anything beyond applies to the result and is always present.
          {fields, extra} = Enum.split(all, length(quantities))

          kept =
            fields
            |> Enum.zip(quantities)
            |> Enum.filter(fn {_arg, q} -> q == :present end)
            |> Enum.map(fn {arg, _q} -> erase(env, arg) end)

          extra
          |> Enum.map(&erase(env, &1))
          |> Enum.reduce({:ctor, cname, kept}, fn arg, acc -> {:app, acc, arg} end)
        else
          # Partially applied, or already erased: filtering would realign the quantity vector
          # onto the wrong positions. Keep every argument and recurse, so erase(erase(t)) is
          # erase(t) — the same reasoning as the flat `{:ctor, …}` and `{:global, …}` clauses.
          args
          |> Enum.map(&erase(env, &1))
          |> Enum.reduce(erase(env, head), fn arg, acc -> {:app, acc, arg} end)
        end

      _ ->
        args
        |> Enum.map(&erase(env, &1))
        |> Enum.reduce(erase(env, head), fn arg, acc -> {:app, acc, arg} end)
    end
  end

  def erase(env, {:pi, d, c}), do: {:pi, erase(env, d), erase(env, c)}

  def erase(env, {:data, n, ps, is}),
    do: {:data, n, Enum.map(ps, &erase(env, &1)), Enum.map(is, &erase(env, &1))}

  # Collapsible-family elimination (Phase B, spec "Phase-B encoding amendment"):
  # a case whose single branch names the sole constructor of its family, all of
  # whose fields are erased (e.g. `Equivalent`'s `reflexive`), carries zero
  # runtime information — the matched shape is forced, so the case erases to its
  # branch body outright (Brady/McBride/McKinna collapsible families; this is
  # what lets the J/subst transport's proof scrutinee vanish at runtime exactly
  # as the retired `{:rewrite}` node's proof did). The branch's erased binders
  # are instantiated with an inert placeholder: they can only occur in positions
  # erasure drops anyway (all fields are `:erased`, and erased pattern binders
  # are surface-inaccessible), so the placeholder never survives into runtime-
  # relevant code. MUST stay in lockstep with `Relevance.collapsible_case?/2`,
  # which exempts the scrutinee from the relevance check on the same class —
  # keeping the case here would emit a scrutinee referencing dropped binders.
  def erase(env, {:case, s, m, [{cname, arity, body}] = branches}) do
    if collapsible_ctor?(env, cname, arity) do
      body
      |> Cure.Elab.Subst.instantiate(List.duplicate({:ctor, :cure_erased, []}, arity))
      |> then(&erase(env, &1))
    else
      {:case, erase(env, s), erase(env, m), Enum.map(branches, fn {c, ar, b} -> {c, ar, erase(env, b)} end)}
    end
  end

  def erase(env, {:case, s, m, branches}) do
    {:case, erase(env, s), erase(env, m), Enum.map(branches, fn {c, ar, b} -> {c, ar, erase(env, b)} end)}
  end

  def erase(_env, term), do: term

  defp spine({:app, f, x}, acc), do: spine(f, [x | acc])
  defp spine(head, acc), do: {head, acc}

  # The single branch's ctor is its family's ONLY constructor and every field is
  # erased (nonempty — nullary single-ctor families like Unit keep the ordinary
  # case; this rule targets proof-like carriers). Mirror of
  # `Relevance.collapsible_case?/2` — keep in lockstep.
  defp collapsible_ctor?(env, cname, arity) do
    with dname when dname != nil <- Inductive.ctor_family(env, cname),
         [_only] <- Inductive.ctors_of(env, dname),
         qs when is_list(qs) <- Inductive.ctor_quantities(env, cname) do
      arity == length(qs) and qs != [] and Enum.all?(qs, &(&1 == :erased))
    else
      _ -> false
    end
  end

  @doc "Does the term still contain an unfilled hole?"
  @spec has_hole?(Cure.Core.Term.t()) :: boolean()
  def has_hole?({:hole, _name}), do: true
  def has_hole?({:lam, d, b}), do: has_hole?(d) or has_hole?(b)
  def has_hole?({:pi, d, c}), do: has_hole?(d) or has_hole?(c)
  def has_hole?({:app, f, x}), do: has_hole?(f) or has_hole?(x)
  def has_hole?({:ctor, _n, args}), do: Enum.any?(args, &has_hole?/1)
  def has_hole?({:data, _n, ps, is}), do: Enum.any?(ps ++ is, &has_hole?/1)

  def has_hole?({:case, s, m, branches}),
    do: has_hole?(s) or has_hole?(m) or Enum.any?(branches, fn {_c, _ar, b} -> has_hole?(b) end)

  def has_hole?(_term), do: false
end
