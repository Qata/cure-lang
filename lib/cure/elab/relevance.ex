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

  ## Idris grounding (Core/LinearCheck.idr)

  Idris runs **two independent mechanisms**, and so does this module.

  ### 1. The position check — Idris `rigSafe` (`:166-170`)

  At a `Local` occurrence, `rigSafe l r = when (l < r) (throw (LinearMisuse …))`:
  a binder whose multiplicity sits strictly below the ambient rig is misused. The
  `{0, ω}` instance of that is "an `:erased` binder may not appear in a RELEVANT
  position", which is the check this module has always performed:

    * RELEVANT (a `0` binder here is a violation):
      - returned as the value (`:returned`);
      - passed in a runtime-**present** argument position of a call/constructor
        (`:present_arg`);
      - scrutinised as a `case` discriminant (`:scrutinee`);
      - applied as a function head (`:applied`).
    * EXEMPT (does not count): type/index positions (`{:pi}`/`{:data}` — Pi
      domains, the `case` motive), erased argument positions, and
      collapsible-family proof elimination (the J/subst transport's scrutinee).

  A present argument position is `Grade.present?/1`, **not** `q == :unrestricted`.
  Slice 4a's rename left the latter here, which exempted every `:linear` and
  `:affine` argument position from the walk — the same trap 4a fixed in `Erase`
  and `Emit`, dormant only until 4b made those grades reachable.

  ### 2. The usage check — Idris `checkUsageOK` (`:274-276`)

  At a `Bind`, `checkUsageOK used r = when (isLinear r && used /= 1) (throw …)`.
  Slice 4b generalises that over the full carrier, which is exactly where affinity
  enters: `:affine` admits `0` or `1`.

  Usage is carried **as a grade** — `:erased` = zero uses, `:linear` = one,
  `:unrestricted` = many — so composition is the semiring:

    * sequence (`:let` value then body, application head then args, `:case`
      scrutinee then branches) sums with `Grade.add/2`: `1 + 1 = ω`;
    * entering a subterm scales with `Grade.mul/2`. An argument position scales by
      the callee's declared grade, so passing a `:linear` variable to an `ω`
      parameter costs `ω`. **A λ's body scales by `ω`**, because a closure may be
      entered any number of times — this is how a linear binder captured by a
      returned closure is rejected without a bespoke rule. Idris achieves the same
      with `eraseLinear env` when checking a `Lam` at `top` (`:233-237`).

  The rule itself is `Grade.leq(used, declared)` — subusaging. Over this carrier
  that is *exhaustively equivalent* to `Grade.admits?(declared, n)` for the
  representative count `n`, and it keeps grades opaque: nothing here
  pattern-matches one. `grade_test.exs` pins the equivalence.

  ### Branches combine by agreement, not summation

  A `case` yields, per binder, the **set** of usages its branches produce, and
  every member must satisfy `leq`. A `:linear` binder used in one branch and
  dropped in another is rejected; an `:affine` one is accepted. Idris's
  `combineUsage` (`:528-540`) throws on any `Use0`/`Use1` mismatch regardless of
  the binder's grade — right for Idris, which has no affine, and wrong here.

  ### Division of labour

  The counting check runs for `:linear` and `:affine` binders. `:erased` stays
  with the position check above, which reports the more precise
  `{:erased_used_relevantly, …}` (naming the *site*) and carries the
  collapsible-family exemption. `:unrestricted` imposes no obligation.

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

  alias Cure.Core.{Env, Grade, Inductive}

  @type site :: :returned | :present_arg | :scrutinee | :applied
  @type kind :: :param | :lambda | :let | :field

  @typedoc """
  Per-binder usage. Keys are de Bruijn LEVELS; each value is the set of usages the
  term's branches admit for that level (a singleton outside a `case`). A level
  absent from the map was used zero times.
  """
  @type usage :: %{optional(non_neg_integer()) => MapSet.t(Grade.t())}

  @type error ::
          {:erased_used_relevantly, %{def: atom(), binder: non_neg_integer(), site: site()}}
          | {:usage_violation,
             %{def: atom(), binder: non_neg_integer(), kind: kind(), declared: Grade.t(), used: Grade.t()}}

  @doc """
  Check `body` (the raw, pre-lambda-wrapped body term) against `quantities`, the
  per-parameter grade vector (`nil` = all runtime-relevant, no check).

  Enforces both mechanisms described in the moduledoc: no `:erased` binder is used
  in a relevant position, and every `:linear` / `:affine` binder — parameter,
  lambda, `let`, or constructor field bound by a pattern — is used a number of
  times its grade admits. Returns `:ok` or the first violation.
  """
  @spec check(Env.t(), atom(), [Grade.t()] | nil, Cure.Core.Term.t()) :: :ok | {:error, error()}
  def check(_env, _name, quantities, _body) when not is_list(quantities), do: :ok

  def check(env, name, quantities, body) do
    erased =
      quantities
      |> Enum.with_index()
      |> Enum.filter(fn {q, _idx} -> Grade.erased?(q) end)
      |> Enum.map(fn {_q, idx} -> idx end)
      |> MapSet.new()

    # No early-out when `erased` is empty. Erasedness does not only originate at
    # the signature: matching a constructor with an erased FIELD introduces a fresh
    # erased binder (see the `:case` clause's `branch_erased` fold), so an ordinary
    # all-`:unrestricted` function can still return a value that `Erase.erase` deletes.
    # Idris's `lcheck` (Core/LinearCheck.idr) likewise always walks the body — there
    # is one notion of erased, not a checked and an unchecked one.
    st = %{env: env, name: name, erased: erased}

    # The parameters are the body's outermost free variables, so parameter `p` is
    # de Bruijn LEVEL `p` and its usage is read straight off the walk's result.
    with {:ok, usage} <- walk(body, length(quantities), :returned, st) do
      quantities
      |> Enum.with_index()
      |> each(fn {q, p} -> check_binder(st, p, q, usage, :param) end)
    end
  end

  # --- the usage rule --------------------------------------------------------

  # `Grade.leq(used, declared)` is subusaging, and over this carrier it is exactly
  # `Grade.admits?(declared, count(used))`. `:erased` binders are left to the
  # position check, which reports the site; `:unrestricted` imposes no obligation.
  defp check_binder(st, level, declared, usage, kind) do
    if Grade.restricted?(declared) and not Grade.erased?(declared) do
      usage
      |> Map.get(level, no_uses())
      |> Enum.find(fn used -> not Grade.leq(used, declared) end)
      |> case do
        nil ->
          :ok

        used ->
          {:error,
           {:usage_violation,
            %{def: st.name, binder: level, kind: kind, declared: declared, used: used}}}
      end
    else
      :ok
    end
  end

  # An `:erased` `:let` or `:lam` binder joins the POSITION check's tracked set, exactly
  # as an erased constructor FIELD does in `walk_branches/3`. Without this, `:erased`
  # is the one grade no mechanism polices on those binders: `check_binder/5` defers
  # erasure to the position check, and the position check only ever knew about
  # parameters and fields — so `let c :erased = e` and then returning `c` was accepted.
  # `Emit` binds every `:let` unconditionally, so the value does exist at runtime; the
  # lie was in the annotation, not in erasure.
  defp track_erased(st, g, level) do
    if Grade.erased?(g), do: %{st | erased: MapSet.put(st.erased, level)}, else: st
  end

  # --- usage algebra ---------------------------------------------------------

  # Zero uses. A level absent from a usage map has exactly this.
  defp no_uses, do: MapSet.new([Grade.zero()])

  defp one_use(level), do: %{level => MapSet.new([Grade.one()])}

  # Sequential composition: both subterms run, so usages SUM (`1 + 1 = ω`).
  defp seq(u1, u2) do
    Enum.reduce(u2, u1, fn {level, s2}, acc ->
      Map.update(acc, level, s2, fn s1 ->
        for a <- s1, b <- s2, into: MapSet.new(), do: Grade.add(a, b)
      end)
    end)
  end

  defp seq_all(usages), do: Enum.reduce(usages, %{}, &seq(&2, &1))

  # Alternative composition (`case` branches): exactly one branch runs, so the
  # usages are not summed — they are collected, and every one must satisfy `leq`.
  defp alt([]), do: %{}

  defp alt(usages) do
    usages
    |> Enum.flat_map(&Map.keys/1)
    |> Enum.uniq()
    |> Map.new(fn level ->
      {level, usages |> Enum.map(&Map.get(&1, level, no_uses())) |> Enum.reduce(&MapSet.union/2)}
    end)
  end

  # Scale a usage context by the grade of the position it sits in.
  defp scale(usage, g), do: Map.new(usage, fn {l, s} -> {l, MapSet.new(s, &Grade.mul(g, &1))} end)

  # --- relevant positions: an erased-parameter occurrence here is a violation --

  defp walk({:var, i}, depth, site, st) do
    level = depth - 1 - i

    cond do
      level >= 0 and MapSet.member?(st.erased, level) ->
        {:error, {:erased_used_relevantly, %{def: st.name, binder: level, site: site}}}

      level >= 0 ->
        {:ok, one_use(level)}

      true ->
        {:ok, %{}}
    end
  end

  # A closure value: its domain is a type position (exempt); its body is relevant.
  # Descending binds one more variable, at level `depth`.
  #
  # The body's usage of OUTER binders is scaled by `ω`: a λ may be entered any
  # number of times, so one syntactic occurrence inside it is not one use. This is
  # what rejects a linear binder captured by a returned closure, and it is the
  # `mul/2` consequence rather than a rule of its own (Idris: `eraseLinear env`
  # when a `Lam` is checked at `top`, LinearCheck.idr:233-237).
  defp walk({:lam, g, _dom, body}, depth, _site, st) do
    with {:ok, u} <- walk(body, depth + 1, :returned, track_erased(st, g, depth)),
         :ok <- check_binder(st, depth, g, u, :lambda) do
      {:ok, u |> Map.delete(depth) |> scale(Grade.unrestricted())}
    end
  end

  # `:let` — the ascription is a type position (exempt). The VALUE is always
  # evaluated at runtime (`X = Val` in the emitted BEAM), so it is a relevant
  # position regardless of whether the body uses the binder; that is the honest
  # dual of `Emit`'s unconditional bind. The body inherits the let's own site and
  # binds one more variable. Value and body both run, so their usages sum.
  #
  # JOIN POINT (slice 4c). When the value is a λ and the body is a `case` that
  # applies the binder AT MOST ONCE PER BRANCH and nowhere else — the shape
  # `wrap_join/2` produces — this `:let` is a shared branch continuation, not an
  # escaping closure. Idris never materialises such a shape: it usage-checks each
  # case alternative INDEPENDENTLY and combines by agreement (`LinearCheck.idr`
  # `getArgUsage`, `traverse getPUsage pats; combine us`). So the generic ω-scale of
  # a λ body (which assumes the closure may be entered any number of times) is wrong
  # here: the continuation runs at most once on any path, so its captured variables
  # are used at most once — the same count the un-joined per-branch form gives via
  # `alt`. `walk_joined_case/7` reproduces that: it walks the shared body's captures
  # ONCE, unscaled, and injects them as one more alternative into the branch `alt`.
  defp walk({:let, g, _ty, val, body}, depth, site, st) do
    case join_view(val, body, depth) do
      {:join, lg, jbody, scrut, branches} ->
        walk_joined_case(lg, jbody, scrut, branches, depth, site, st)

      :not_join ->
        with {:ok, uv} <- walk(val, depth, :present_arg, st),
             {:ok, ub} <- walk(body, depth + 1, site, track_erased(st, g, depth)),
             :ok <- check_binder(st, depth, g, ub, :let) do
          {:ok, seq(uv, Map.delete(ub, depth))}
        end
    end
  end


  # Application spine: the head is `:applied`; an argument is walked iff a runtime
  # value exists for it (`Grade.present?/1` — the dual of `Erase.erase`'s
  # `{:app, …}` filtering), and its usage is scaled by the callee's declared grade.
  # Passing a linear variable to an `ω` parameter therefore costs `ω`.
  defp walk({:app, _f, _x} = app, depth, _site, st) do
    {head, args} = spine(app, [])
    quantities = callee_quantities(head, length(args), st.env)

    with {:ok, uh} <- walk(head, depth, :applied, st),
         {:ok, ua} <- walk_args(args, quantities, depth, st) do
      {:ok, seq(uh, ua)}
    end
  end

  # Constructor: same present/erased split, via the family's ctor quantities.
  defp walk({:ctor, cname, args}, depth, _site, st) do
    quantities =
      (Inductive.ctor_quantities(st.env, cname) || List.duplicate(Grade.unrestricted(), length(args)))
      |> pad(length(args))

    walk_args(args, quantities, depth, st)
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
  #
  # Exactly one branch runs, so branch usages are collected by `alt/1` rather than
  # summed; the scrutinee runs before whichever branch is taken, so it sums.
  defp walk({:case, scrut, _motive, branches}, depth, _site, st) do
    scrut_usage =
      if collapsible_case?(st.env, branches),
        do: {:ok, %{}},
        else: walk(scrut, depth, :scrutinee, st)

    with {:ok, us} <- scrut_usage,
         {:ok, ubs} <- walk_branches(branches, depth, st) do
      {:ok, seq(us, alt(ubs))}
    end
  end

  # --- exempt positions: type formers and proof terms carry no runtime value ---
  defp walk({:pi, _g, _d, _c}, _depth, _site, _st), do: {:ok, %{}}
  defp walk({:data, _n, _ps, _is}, _depth, _site, _st), do: {:ok, %{}}

  # Leaves (`:global`, `:type`, `:hole`, literals) and any other form: no
  # occurrence to account for. Mirrors `Erase`'s leaf clause.
  defp walk(_leaf, _depth, _site, _st), do: {:ok, %{}}

  # Recognise the join idiom AND prove it is sound to un-join: the `:let` value is a
  # λ, the body is a `case`, and the let binder (de Bruijn level `depth`) occurs in
  # that case ONLY as an application head `{:app, {:var, →depth}, _}`, AT MOST ONCE in
  # any single branch, and NOWHERE in the scrutinee or motive. Under those conditions
  # the continuation is one-shot per execution path, so counting its captures once
  # (not ω) never under-counts. Any other shape → `:not_join`, keeping the sound,
  # conservative ω-scale of the generic `:let`/`:lam` path.
  defp join_view({:lam, lg, _dom, jbody}, {:case, scrut, motive, branches}, depth) do
    if join_binder_safe?(scrut, motive, branches, depth) do
      {:join, lg, jbody, scrut, branches}
    else
      :not_join
    end
  end

  defp join_view(_val, _body, _depth), do: :not_join

  # The join binder is at level `depth`. The `case` sits one binder deeper
  # (`case_depth`); inside a branch it is under `arity` more pattern binders. Safe to
  # un-join iff it does not occur in the scrutinee or motive, and EVERY branch is
  # either free of it entirely (a matched arm) OR is EXACTLY a bare tail application
  # `{:app, {:var, →depth}, s}` with the binder absent from `s` (a defaulted branch
  # that runs the shared continuation exactly once). This is precisely the shape
  # `wrap_join/2` emits, and precisely the shape `walk_join_branches/5` inlines — a
  # branch that applied the binder in ANY other position (`sink(j(x))`, `j(a)+j(b)`)
  # would be walked as a matched arm, dropping the binder and LOSING the shared
  # continuation's captures (an under-count). Anything else → `:not_join` → the sound
  # ω-scale of the generic `:lam`/`:let` path.
  defp join_binder_safe?(scrut, motive, branches, depth) do
    case_depth = depth + 1

    count_level(scrut, case_depth, depth) == 0 and
      count_level(motive, case_depth, depth) == 0 and
      Enum.all?(branches, fn {_c, arity, body} ->
        bd = case_depth + arity

        case body do
          {:app, {:var, idx}, s} when bd - 1 - idx == depth ->
            count_level(s, bd, depth) == 0

          _ ->
            count_level(body, bd, depth) == 0
        end
      end)
  end

  # Count free occurrences of de Bruijn LEVEL `target` in `term` (walked at `depth`).
  defp count_level({:var, i}, depth, target), do: if(depth - 1 - i == target, do: 1, else: 0)
  defp count_level({:lam, _g, d, b}, depth, t), do: count_level(d, depth, t) + count_level(b, depth + 1, t)
  defp count_level({:pi, _g, d, c}, depth, t), do: count_level(d, depth, t) + count_level(c, depth + 1, t)

  defp count_level({:let, _g, ty, v, b}, depth, t),
    do: count_level(ty, depth, t) + count_level(v, depth, t) + count_level(b, depth + 1, t)

  defp count_level({:app, f, x}, depth, t), do: count_level(f, depth, t) + count_level(x, depth, t)
  defp count_level({:ctor, _n, args}, depth, t), do: Enum.sum(Enum.map(args, &count_level(&1, depth, t)))

  defp count_level({:data, _n, ps, is}, depth, t),
    do: Enum.sum(Enum.map(ps ++ is, &count_level(&1, depth, t)))

  defp count_level({:case, s, m, brs}, depth, t) do
    count_level(s, depth, t) + count_level(m, depth, t) +
      Enum.sum(Enum.map(brs, fn {_c, ar, b} -> count_level(b, depth + ar, t) end))
  end

  defp count_level(_leaf, _depth, _t), do: 0


  # Un-join: check the shared continuation ONCE (unscaled), then combine it as one
  # alternative with the matched-arm usages. `alt` (agreement) then counts a captured
  # variable at most once across all branches — the Idris per-alternative result.
  defp walk_joined_case(lg, jbody, scrut, branches, depth, _site, st) do
    with {:ok, uj} <- walk(jbody, depth + 1, :returned, track_erased(st, lg, depth)),
         :ok <- check_binder(st, depth, lg, uj, :lambda) do
      jbody_captures = Map.delete(uj, depth)
      case_depth = depth + 1

      scrut_usage =
        if collapsible_case?(st.env, branches),
          do: {:ok, %{}},
          else: walk(scrut, case_depth, :scrutinee, st)

      with {:ok, us} <- scrut_usage,
           {:ok, ubs} <- walk_join_branches(branches, case_depth, depth, jbody_captures, st) do
        {:ok, seq(us, alt(ubs)) |> Map.delete(depth)}
      end
    end
  end

  # Like `walk_branches/3`, but a branch that IS a join application `{:app, {:var,
  # arity}, s}` contributes the shared continuation's captures (already computed,
  # unscaled) seq'd with the usage of its scrutinee argument — never counting the
  # join binder itself (it is inlined). Matched arms walk normally.
  defp walk_join_branches(branches, depth, join_level, jbody_captures, st) do
    branches
    |> Enum.reduce_while({:ok, []}, fn {cname, arity, body}, {:ok, acc} ->
      ctor_qs =
        Inductive.ctor_quantities(st.env, cname) || List.duplicate(Grade.unrestricted(), arity)

      branch_erased =
        ctor_qs
        |> Enum.with_index()
        |> Enum.filter(fn {q, _p} -> Grade.erased?(q) end)
        |> Enum.map(fn {_q, p} -> depth + p end)

      st2 = %{st | erased: Enum.into(branch_erased, st.erased)}
      drop_levels = for(p <- 0..(arity - 1)//1, do: depth + p)

      result =
        case body do
          {:app, {:var, idx}, s} when depth + arity - 1 - idx == join_level ->
            # Defaulted branch: it runs the shared continuation. Its usage is that
            # continuation's captures plus the usage of the scrutinee it is applied
            # to; the join binder is inlined, never counted.
            with {:ok, us} <- walk(s, depth + arity, :present_arg, st2) do
              {:ok, seq(us, jbody_captures) |> Map.drop(drop_levels)}
            end

          _ ->
            with {:ok, u} <- walk(body, depth + arity, :returned, st2),
                 :ok <- check_fields(st2, ctor_qs, depth, u) do
              {:ok, Map.drop(u, drop_levels)}
            end
        end

      case result do
        {:ok, bu} -> {:cont, {:ok, acc ++ [bu]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # Each branch binds its constructor's fields at levels `depth + p`. An erased
  # field joins the position check's tracked set (spec 2026-07-08 §2.3, a named
  # erased pattern binder is policed like an erased parameter); a restricted one is
  # usage-checked like any other binder, then dropped from the usage that escapes.
  defp walk_branches(branches, depth, st) do
    branches
    |> Enum.reduce_while({:ok, []}, fn {cname, arity, body}, {:ok, acc} ->
      ctor_qs =
        Inductive.ctor_quantities(st.env, cname) || List.duplicate(Grade.unrestricted(), arity)

      branch_erased =
        ctor_qs
        |> Enum.with_index()
        |> Enum.filter(fn {q, _p} -> Grade.erased?(q) end)
        |> Enum.map(fn {_q, p} -> depth + p end)

      st2 = %{st | erased: Enum.into(branch_erased, st.erased)}

      with {:ok, u} <- walk(body, depth + arity, :returned, st2),
           :ok <- check_fields(st2, ctor_qs, depth, u) do
        {:cont, {:ok, acc ++ [Map.drop(u, for(p <- 0..(arity - 1)//1, do: depth + p))]}}
      else
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp check_fields(st, ctor_qs, depth, usage) do
    ctor_qs
    |> Enum.with_index()
    |> each(fn {q, p} -> check_binder(st, depth + p, q, usage, :field) end)
  end

  # Walk each present argument and scale its usage by the position's grade; erased
  # positions are not walked at all (the position check's exemption).
  defp walk_args(args, quantities, depth, st) do
    args
    |> Enum.zip(quantities)
    |> Enum.reduce_while({:ok, []}, fn {arg, q}, {:ok, acc} ->
      if Grade.present?(q) do
        case walk(arg, depth, :present_arg, st) do
          {:ok, u} -> {:cont, {:ok, acc ++ [scale(u, q)]}}
          {:error, _} = err -> {:halt, err}
        end
      else
        {:cont, {:ok, acc}}
      end
    end)
    |> case do
      {:ok, usages} -> {:ok, seq_all(usages)}
      {:error, _} = err -> err
    end
  end

  # Exactly one branch, naming its family's ONLY constructor, whose fields are
  # all erased (and nonempty — a nullary single-ctor family like Unit keeps
  # today's relevant-scrutinee treatment; this rule targets proof-like carriers).
  defp collapsible_case?(env, [{cname, arity, _body}]) do
    with dname when dname != nil <- Inductive.ctor_family(env, cname),
         [_only] <- Inductive.ctors_of(env, dname),
         qs when is_list(qs) <- Inductive.ctor_quantities(env, cname) do
      arity == length(qs) and qs != [] and Enum.all?(qs, &Grade.erased?/1)
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
      _ -> List.duplicate(Grade.unrestricted(), arity)
    end
  end

  defp callee_quantities({:ctor, cname, _args}, arity, env) do
    (Inductive.ctor_quantities(env, cname) || List.duplicate(Grade.unrestricted(), arity)) |> pad(arity)
  end

  defp callee_quantities(_other, arity, _env), do: List.duplicate(Grade.unrestricted(), arity)

  # Conservative padding: an argument position with no declared quantity is
  # treated as `:unrestricted` (relevant), never silently exempted.
  defp pad(qs, n) when length(qs) == n, do: qs

  # Over-application: the extra arguments apply to the callee's RESULT and are always present.
  defp pad(qs, n) when length(qs) < n, do: qs ++ List.duplicate(Grade.unrestricted(), n - length(qs))

  # Fewer arguments than declared quantities: by `Erase.erase/2`'s own convention, the term is
  # ALREADY ERASED — its erased arguments have been dropped, so the survivors occupy the
  # ORIGINAL trailing positions, not the leading ones. `Enum.take(qs, n)` realigned them onto
  # the leading labels, and a genuinely present survivor landing on an `:erased` label was
  # silently exempted from the relevance check. Erase guards this exact case ("re-zipping the
  # full quantity vector against the shrunk arg list would realign survivors onto leading
  # positions and DROP them"); Relevance, its documented dual, did not. Every surviving
  # argument of an already-erased term is relevant.
  defp pad(_qs, n), do: List.duplicate(Grade.unrestricted(), n)

  defp each(list, fun) do
    Enum.reduce_while(list, :ok, fn item, :ok ->
      case fun.(item) do
        :ok -> {:cont, :ok}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end
end
