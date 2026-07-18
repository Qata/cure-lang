defmodule Cure.Elab.Elaborator do
  @moduledoc """
  Elaborate the surface expression fragment into explicit `Cure.Core` terms
  (design spec §5; mirrors Idris `TTImp/Elab/Check.idr`).

  Untrusted: it resolves names to de Bruijn indices and builds Core terms that
  the kernel then re-checks. This task covers the basic fragment — `Type`,
  function definitions (→ λ / Π), variables, and application. Implicit inference
  (M8.2), erasure marking (M8.3), and dependent pattern compilation (M8.4) build
  on it.

  A *scope* is the list of in-scope binder names, most-recently-bound first, so a
  name resolves to its de Bruijn index by position.
  """

  alias Cure.Core.{Context, Conv, Env, Eval, Grade, Inductive, Kernel, Normalise, Quote}
  alias Cure.Elab.{GuardLint, MetaCtx, Subst, Unify}

  # Placeholder body for a `:case` branch the join point will fill (see
  # `join_point?/5`, `elaborate_join/6`, `wrap_join/2`). Never reaches the kernel:
  # `wrap_join/2` replaces every marker before the term escapes `elaborate_match`.
  @join_marker :"$join_point"

  @doc """
  Elaborate a top-level function definition into `{:ok, core_lambda, type_value}`
  — the λ over the parameters and the Π type it inhabits.
  """
  @spec elaborate(tuple(), Env.t()) :: {:ok, Cure.Core.Term.t(), Cure.Core.Value.t()} | {:error, term()}
  def elaborate({:function_def, meta, body}, env) do
    params = Keyword.get(meta, :params, [])
    return_expr = Keyword.fetch!(meta, :return_type)

    with {:ok, param_tele} <- elaborate_params(params, [], env),
         scope = param_tele |> Enum.map(&elem(&1, 0)) |> Enum.reverse(),
         {:ok, body_core} <- elaborate_expr(single_body(body), scope, env),
         {:ok, return_core} <- elaborate_type(return_expr, scope, env) do
      lambda = wrap(:lam, param_tele, body_core)
      pi = wrap(:pi, param_tele, return_core)
      {:ok, lambda, Eval.eval(pi, [])}
    end
  end

  def elaborate(other, _env), do: {:error, {:unsupported_expression, other}}

  # Desugar record construction `Point{x: .., y: ..}` (a `record: true` call whose
  # arguments are `field: value` pairs) into the positional constructor application
  # `Point(.., ..)`, ordering the values by the record constructor's field telescope
  # (the constructor's argument names ARE the field names). Missing or extra fields
  # are rejected.
  defp desugar_record_construction(meta, field_pairs, env) do
    name = Keyword.fetch!(meta, :name)
    atom = String.to_atom(name)

    case Inductive.get_ctor(env, atom) do
      nil ->
        {:error, {:unknown_record, atom}}

      ctor ->
        order = Enum.map(ctor.args, fn {n, _t} -> n end)
        defaults = Map.get(ctor, :field_defaults, %{})
        provided = Map.new(field_pairs, fn {:pair, _m, [{:literal, _s, f}, val]} -> {f, val} end)

        cond do
          # A named field is not a field of this record.
          not Enum.all?(Map.keys(provided), &(&1 in order)) ->
            {:error, {:record_field_mismatch, atom}}

          # Every field must be supplied by the caller or carry a declared default
          # (`name: String = "Anonymous"`); an omitted field with no default is a
          # genuine mismatch.
          not Enum.all?(order, &(Map.has_key?(provided, &1) or Map.has_key?(defaults, &1))) ->
            {:error, {:record_field_mismatch, atom}}

          true ->
            values =
              Enum.map(order, fn f ->
                case Map.fetch(provided, f) do
                  {:ok, val} -> val
                  :error -> Map.fetch!(defaults, f)
                end
              end)

            {:ok, {:function_call, [name: name], values}}
        end
    end
  end

  # Desugar record update `Point{base | x: .., …}` into the positional constructor
  # `Point(.., ..)`: each overridden field takes its new value, every other field is
  # projected from the base (`base.field`), reusing construction and projection. An
  # override that names a non-field is rejected.
  defp desugar_record_update(meta, [base | field_pairs], env) do
    name = Keyword.fetch!(meta, :name)
    atom = String.to_atom(name)

    case Inductive.get_ctor(env, atom) do
      nil ->
        {:error, {:unknown_record, atom}}

      ctor ->
        order = Enum.map(ctor.args, fn {n, _t} -> n end)
        overrides = Map.new(field_pairs, fn {:pair, _m, [{:literal, _s, f}, val]} -> {f, val} end)

        if Enum.all?(Map.keys(overrides), &(&1 in order)) do
          values =
            Enum.map(order, fn f ->
              case Map.fetch(overrides, f) do
                {:ok, val} -> val
                :error -> {:attribute_access, [attribute: Atom.to_string(f)], [base]}
              end
            end)

          {:ok, {:function_call, [name: name], values}}
        else
          {:error, {:record_field_mismatch, atom}}
        end
    end
  end

  # Normalize a constructor atom to a registry key via the resolution layer:
  # a flattened dotted path (`:"Std.Nat.Z"`) via qualified resolution; a bare atom
  # that is absent from the registry but present under exactly one re-keyed
  # `:"Mod#Z"` variant (a shadowed-but-present import, spec §3.3) to that variant.
  # A bare atom still present under its bare key (local winner / unshadowed import)
  # is returned unchanged — so a redeclared ctor keeps winning (R1).
  defp resolve_ctor_key(env, cname) do
    s = Atom.to_string(cname)

    cond do
      String.contains?(s, ".") ->
        case Cure.Elab.Resolution.resolve_qualified(env, s, :value) do
          {:ok, key} -> key
          :error -> cname
        end

      Inductive.get_ctor(env, cname) != nil ->
        Env.resolve_key(env, env.ctors, cname)

      true ->
        case Cure.Elab.Resolution.resolve_bare(env, cname) do
          {:ok, key} -> key
          _ -> cname
        end
    end
  end

  # Rewrite a constructor pattern's surface `:name` to the resolved registry key
  # so downstream re-derivation (`constructor_pattern/1` in `elaborate_matched_branch`
  # / `elaborate_rematch_branch`) yields the resolved atom, not the stale dotted
  # one. Only ever called on a `constructor_pattern`-validated arm, which is always
  # a `{:function_call, …}` node (bare nullary ctors included, with empty args).
  defp rekey_pattern_name({:function_call, pmeta, pargs}, cname),
    do: {:function_call, Keyword.put(pmeta, :name, Atom.to_string(cname)), pargs}

  # A constructor pattern whose (resolved) ctor belongs to a different family than
  # the scrutinee. If the ORIGINAL bare name was shadowed off the registry (now
  # only reachable as a re-keyed `:"Mod#name"` variant, which uniform resolution
  # just bound `cname` to), report the targeted R5 `:shadowed_ctor` with a
  # qualified-escape-hatch hint; otherwise it is a genuine cross-family
  # `:foreign_ctor` (existing behavior, unchanged).
  defp shadowed_or_foreign_ctor(env, sig, cname0, cname, dname) do
    case Cure.Elab.Resolution.shadowed_origin(env, cname0) do
      {:ok, mod_id, _key} ->
        {:error,
         {:shadowed_ctor,
          [
            ctor: cname0,
            shadowed_module: mod_id,
            local_family: dname,
            local_ctors: Enum.map(Inductive.ctors_of(sig, dname), & &1.name),
            hint: mod_id <> "." <> Atom.to_string(cname0)
          ]}}

      :error ->
        {:error, {:foreign_ctor, cname}}
    end
  end

  defp elaborate_named_call(meta, args, names, ctx, env) do
    name = Keyword.fetch!(meta, :name)
    atom = String.to_atom(name)

    resolved =
      cond do
        String.contains?(name, ".") ->
          case Cure.Elab.Resolution.resolve_qualified(env, name, :value) do
            {:ok, key} -> key
            :error -> atom
          end

        Inductive.get_ctor(env, atom) != nil ->
          Env.resolve_key(env, env.ctors, atom)

        true ->
          case Cure.Elab.Resolution.resolve_bare(env, atom) do
            {:ok, key} -> key
            _ -> atom
          end
      end

    cond do
      # An interface-method call (`eqs(x, y)`) resolves to a concrete instance
      # from the head-positioned argument's type — inlined at a concrete head,
      # projected off the dictionary parameter at a rigid one. Checked before the
      # constructor/global paths so a method name never falls through to an
      # unresolved global.
      Cure.Elab.Resolve.method?(env, atom) ->
        Cure.Elab.Resolve.method_call(env, atom, args, names, ctx)

      # A call to a `where`-constrained global resolves and appends the dictionary
      # the callee expects before the ordinary application machinery runs, so the
      # dictionary parameter is supplied at every concrete call site.
      Cure.Elab.Resolve.constrained?(env, atom) ->
        Cure.Elab.Resolve.constrained_call(env, atom, args, names, ctx)

      name == "reflexive" and length(args) == 1 ->
        [arg] = args

        # Surface `reflexive(x)` supplies the (erased, forced) witness explicitly;
        # build the inductive ctor `reflexive : {w:a} -> Equivalent(a,w,w)` with `x`
        # in the erased slot (dropped at runtime by erasure). Matching is the
        # ordinary `reflexive()` ctor pattern. Retires the primitive `{:refl, x}`
        # (spec 2026-07-04).
        #
        # A bare data ctor has no inference rule (`:ctor_requires_checking_mode`),
        # so we synthesize reflexive's ONLY possible type — `Equivalent(a, x, x)`
        # over the witness's type/value — and have the kernel `check` the ctor
        # against it (validating that `x` inhabits `a` and the indices unify).
        with {:ok, arg_term, arg_type} <- elaborate_expr_typed(arg, names, ctx, env),
             reflexive = resolve_ctor_key(env, :reflexive),
             equivalent = Inductive.ctor_family(env, reflexive),
             term = {:ctor, reflexive, [arg_term]},
             arg_val = Eval.eval(arg_term, Context.env(ctx)),
             type = {:vdata, equivalent, [arg_type, arg_val, arg_val]},
             :ok <- Kernel.check(ctx, term, type) do
          {:ok, term, type}
        end

      Inductive.get_ctor(env, resolved) ->
        result =
          with {:ok, present} <- map_present_args(args, names, ctx, env) do
            elaborate_ctor_app(env, resolved, present, ctx)
          end

        # A nested underdetermined constructor in *inference* position —
        # `Cons(Z(), Nil())` as a bare argument, whose inner `Nil()` cannot be
        # inferred — fails up-front inference. Retry left-to-right: solve the
        # constructor's parameters from the arguments that do infer (`Z() : Nat`
        # fixes `a`), then *check* the rest (`Nil()` against `Lst(Nat)`). Additive:
        # reached only after inference already failed, original error surfaced
        # otherwise.
        case result do
          {:ok, _, _} = ok ->
            ok

          {:error, _} = orig ->
            case elaborate_ctor_app_infer_bidirectional(env, resolved, args, names, ctx) do
              {:ok, _, _} = ok -> ok
              {:error, _} -> orig
            end
        end

      # A QUALIFIED call to a plain (non-ctor) global def: `A.foo(x)`. The
      # qualified branch above mapped the dotted `name` to the def's registry key
      # (`resolved`, bare or re-keyed `Mod#foo`) via `resolve_qualified/3`; without
      # a clause acting on it the call falls through to the catch-all, which
      # re-elaborates from the raw dotted name and can never find a `.`-spelled
      # key. `elaborate_global_app/4` (as the `implicit_def?` clause uses it) reaches
      # both plain and implicit defs. Guarded on the dot so bare def calls keep
      # their existing paths.
      String.contains?(name, ".") and Map.has_key?(env.defs, resolved) ->
        if Enum.any?(args, &(match?({:lambda, _m, _b}, &1) or call_placeholder?(&1))) do
          # A lambda argument needs a checking-mode expected type, so the bidirectional
          # elaborator is the ONLY path here. It used to be run, and then — on failure —
          # run a second time with identical arguments, which can only reproduce the same
          # error. One attempt, one verdict.
          elaborate_implicit_app_bidirectional(env, resolved, args, names, ctx)
        else
          result =
            with {:ok, present} <- map_present_args(args, names, ctx, env) do
              elaborate_global_app(env, resolved, present, ctx)
            end

          case result do
            {:ok, _, _} = ok ->
              ok

            {:error, _} = orig ->
              # This retry IS load-bearing: the attempt above used a different algorithm
              # (direct application of already-elaborated args), so the bidirectional
              # elaborator can still succeed where it failed — e.g. when an implicit
              # argument only becomes solvable in checking mode.
              case elaborate_implicit_app_bidirectional(env, resolved, args, names, ctx) do
                {:ok, _, _} = ok -> ok
                {:error, _} -> orig
              end
          end
        end

      # An applied call to a bare overloaded name — a set of ≥2 members sharing
      # one bare spelling: same-module discriminated members, or cross-module
      # providers with no unique winner. `overload_candidates/2` already applies
      # local-then-direct precedence, so a name with a single local/direct winner
      # (a local `map` shadowing imports) collapses to one candidate and never
      # reaches here — only a genuine set of ≥2 does. Infer the argument types
      # once, prune by first-order convertibility, and dispatch the survivor.
      # Placed after the ctor/method/constrained/qualified special cases and
      # before the generic ambiguity/def paths; the `not String.contains?` guard
      # keeps it disjoint from the dotted-qualified clause.
      not String.contains?(name, ".") and
          length(Cure.Elab.Resolution.overload_candidates(env, atom)) >= 2 ->
        cands = Cure.Elab.Resolution.overload_candidates(env, atom)

        with {:ok, present} <- map_present_args(args, names, ctx, env),
             arg_types = Enum.map(present, fn {_term, ty} -> ty end),
             {:ok, winner} <- Cure.Elab.Overload.resolve(env, atom, arg_types, cands) do
          elaborate_global_app(env, winner, present, ctx)
        end

      # A bare name provided by ≥2 distinct re-keyed imports with no local/
      # unshadowed winner: unqualified use is ambiguous (R7). Checked before the
      # generic paths so an ambiguous name surfaces `:ambiguous_name`, not a
      # confusing downstream "not found". (`resolved == atom` here: an ambiguous
      # name has no dot and no unique variant.)
      length(Cure.Elab.Resolution.ambiguous_modules(env, atom)) >= 2 ->
        {:error, {:ambiguous_name, atom, Cure.Elab.Resolution.ambiguous_modules(env, atom)}}

      # `_` is meaningful only to the goal-directed application solver: the
      # ordinary scoped path necessarily interprets every variable-shaped AST as
      # a name and reports `:unknown_global` before a later dependent argument can
      # constrain it. Route placeholder-bearing calls directly through the same
      # Π-telescope solver used for implicit and lambda-bearing applications.
      # Local definitions retain the ordinary local-over-import precedence.
      Enum.any?(args, &call_placeholder?/1) and
          (Env.get_def(env, atom) != nil or Env.get_def(env, resolved) != nil) ->
        key = if Env.get_def(env, atom), do: Env.resolve_key(env, env.defs, atom), else: resolved
        elaborate_implicit_app_bidirectional(env, key, args, names, ctx)

      # A global whose telescope carries erased (implicit) parameters: insert
      # fresh metavariables for them and solve from the present arguments, the
      # same way constructor indices are inferred (§5.2). Without this, the
      # explicit args would be bound to the implicit positions.
      #
      # Key on the raw `atom` whenever it names a LOCAL def (which must shadow any
      # same-named import), otherwise on `resolved`. An IMPORTED implicit def is
      # registered under a re-keyed import key (`Std.List#map`), so
      # `implicit_def?(env, :map)` is false and the raw atom is not a def; without
      # resolving, a bare `map(xs, fn(x) -> ...)` skips implicit insertion, falls to
      # the lambda clause below, and mis-binds `xs : List(Int)` against the erased
      # `{t} : Type` slot (a `:conversion_failure`). Preferring `atom` when it is a
      # local def keeps a module's own `map`/`filter` bound to itself;
      # `resolve_bare` (which feeds `resolved`) resolves toward imports and
      # would otherwise redirect a recursive self-call to a same-named import.
      implicit_def?(env, if(Env.get_def(env, atom), do: atom, else: resolved)) ->
        key = if Env.get_def(env, atom), do: Env.resolve_key(env, env.defs, atom), else: resolved

        result =
          with {:ok, present} <- map_present_args(args, names, ctx, env) do
            elaborate_global_app(env, key, present, ctx)
          end

        # When up-front inference of the arguments fails — an argument that is
        # underdetermined until an implicit parameter is solved (`map(s, Cons(Z(),
        # Nil()))`) — retry with left-to-right bidirectional application. Additive:
        # reached only after the inference path errored, and its own failure
        # surfaces the original error, so a working call is untouched.
        case result do
          {:ok, _, _} = ok ->
            ok

          {:error, _} = orig ->
            case elaborate_implicit_app_bidirectional(env, key, args, names, ctx) do
              {:ok, _, _} = ok -> ok
              {:error, _} -> orig
            end
        end

      # A call carrying a lambda argument needs the callee's parameter types to
      # reach the (untyped-in-surface) lambda: elaborate bidirectionally, checking
      # each argument against its Π domain. Restricted to lambda-bearing calls so
      # every other application keeps its exact existing inference path.
      Enum.any?(args, &match?({:lambda, _m, _b}, &1)) ->
        elaborate_bidirectional_app(name, args, names, ctx, env)

      true ->
        # Non-constructor application: elaborate to a term, then let the kernel type it.
        result =
          with {:ok, term} <- elaborate_expr({:function_call, [name: name], args}, names, env),
               {:ok, type} <- Kernel.infer(ctx, term) do
            {:ok, term, type}
          end

        # The scoped path binds arguments positionally and does not insert
        # metavariables for a *nested* implicit call, so an argument like
        # `len(mklist())` / `map(s, xs)` — an implicit-parameter call — is
        # mis-bound (`Lst(Nat)` checked against the `{a} : Type` slot). When that
        # fails, retry checking each argument against the callee's Π domain, which
        # elaborates a nested implicit call in checking mode. Additive: reached only
        # after the scoped path errored, original error surfaced otherwise.
        case result do
          {:ok, _, _} = ok ->
            ok

          {:error, _} = orig ->
            case elaborate_bidirectional_app(name, args, names, ctx, env) do
              {:ok, _, _} = ok -> ok
              {:error, _} -> orig
            end
        end
    end
  end

  # Saturated application checked argument-by-argument against the callee's Π
  # telescope, so a lambda argument is elaborated in checking mode (its parameter
  # types come from the domain). The codomain is instantiated at each argument's
  # value, so a dependent parameter type is honoured too.
  defp elaborate_bidirectional_app(name, args, names, ctx, env) do
    with {:ok, head} <- elaborate_expr({:variable, [], name}, names, env),
         {:ok, head_type} <- Kernel.infer(ctx, head) do
      check_app_args(head, head_type, args, names, ctx, env)
    end
  end

  @doc """
  Apply an already-elaborated `term` of value-type `type` to surface `args`,
  checking each argument against the callee's Π domain (so a lambda argument
  elaborates in checking mode). Used by `Cure.Elab.Resolve` to apply a method
  projected off a dictionary at an abstract call site.
  """
  @spec apply_checked_args(term(), term(), [term()], [String.t()], Context.t(), Env.t()) ::
          {:ok, term(), term()} | {:error, term()}
  def apply_checked_args(term, type, args, names, ctx, env),
    do: check_app_args(term, type, args, names, ctx, env)

  defp check_app_args(term, type, [], _names, _ctx, _env), do: {:ok, term, type}

  defp check_app_args(term, type, [arg | rest], names, ctx, env) do
    case type do
      {:vpi, _g, dom_value, cod_closure} ->
        dom_term = Quote.reify(dom_value, Context.length(ctx))

        with {:ok, arg_term} <- elaborate_expr_checked(arg, dom_term, names, ctx, env) do
          arg_value = Eval.eval(arg_term, Context.env(ctx))
          next_type = Eval.apply_closure(cod_closure, arg_value)
          check_app_args({:app, term, arg_term}, next_type, rest, names, ctx, env)
        end

      _ ->
        {:error, :applied_non_function}
    end
  end

  @doc """
  Context-aware expression elaboration: elaborate `expr` to `{term, type_value}`
  in a kernel typing `ctx` (whose variables are named, most-recently-bound first,
  by `names`). Constructor applications route through `elaborate_ctor_app/3` so
  their erased indices are inferred; other forms reuse the untyped elaborator and
  the kernel's `infer/2` for their type.
  """
  @spec elaborate_expr_typed(term(), [String.t()], Context.t(), Env.t()) ::
          {:ok, term(), Cure.Core.Value.t()} | {:error, term()}
  def elaborate_expr_typed({:variable, _meta, "Type"}, _names, _ctx, _env),
    do: {:ok, {:type, 0}, {:vtype, 1}}

  def elaborate_expr_typed({:variable, _meta, name}, names, ctx, env) do
    case Enum.find_index(names, &(&1 == name)) do
      nil ->
        with {:ok, term} <- resolve_free(name, env),
             {:ok, type} <- Kernel.infer(ctx, term) do
          {:ok, term, type}
        end

      index ->
        term = {:var, index}

        with {:ok, type} <- Kernel.infer(ctx, term) do
          {:ok, term, type}
        end
    end
  end

  # A synthetic dictionary argument `{:dict_value, iface, head}`, inserted by
  # `Cure.Elab.Resolve` at a concrete call to a constrained function: build the
  # instance's dictionary record value (its type is `iface(head)`).
  def elaborate_expr_typed({:dict_value, iface, head}, _names, ctx, env),
    do: Cure.Elab.Resolve.dict_value(env, iface, head, ctx)

  # A forced (dot) pattern `{:forced_pattern, …}` is only meaningful in a
  # constructor-argument PATTERN position (handled by the pattern path in a later
  # task). Reaching ordinary expression elaboration means a dot was used outside
  # a pattern (a `let` RHS, a function argument/body, …) — reject it. Placed
  # before the catch-all so this precise error, not `{:unsupported_expression,…}`,
  # is reported.
  def elaborate_expr_typed({:forced_pattern, meta, _children}, _names, _ctx, _env),
    do: {:error, {:forced_pattern_not_in_pattern, meta}}

  # A named-implicit dot pattern `{ name = <expr> }` is only meaningful as a
  # constructor-argument PATTERN position (annotating an erased index by name).
  # Reaching ordinary expression elaboration means it was used outside a pattern
  # — reject it with a precise error (mirrors the forced-pattern guard above).
  def elaborate_expr_typed({:named_implicit_pat, meta, _children}, _names, _ctx, _env),
    do: {:error, {:named_implicit_not_in_pattern, meta}}

  def elaborate_expr_typed({:function_call, meta, args}, names, ctx, env) do
    cond do
      # `element(t, i)` — dependent n-ary telescope/tuple projection. ONE surface
      # for the i-th component, typed at the true `Ti` (not a numbered `tproj_i`),
      # with a COMPILE-TIME bounds check: an `i` beyond the arity is rejected at
      # elaboration, never a runtime crash. `t.i` is sugar for this (both share
      # `positional_projection`). `i` must be a static positive integer literal —
      # the bounds check is only meaningful for a statically-known index.
      Keyword.get(meta, :name) == "element" and element_projection?(args) ->
        [t_arg, {:literal, _, i}] = args
        positional_projection(i, t_arg, names, ctx, env)

      # Record construction `Point{x: .., y: ..}` desugars to the positional
      # constructor `Point(.., ..)` (fields ordered by the record's telescope).
      Keyword.get(meta, :record) ->
        with {:ok, positional} <- desugar_record_construction(meta, args, env) do
          elaborate_expr_typed(positional, names, ctx, env)
        end

      # `f(x)(y)` parses with the inner call preserved as `:callee` (and `name`
      # left "unknown"): elaborate the callee expression, then apply the outer
      # arguments to its (function-typed) result.
      callee = Keyword.get(meta, :callee) ->
        with {:ok, head, head_type} <- elaborate_expr_typed(callee, names, ctx, env) do
          check_app_args(head, head_type, args, names, ctx, env)
        end

      true ->
        elaborate_named_call(meta, args, names, ctx, env)
    end
  end

  def elaborate_expr_typed({:record_update, meta, children}, names, ctx, env) do
    with {:ok, positional} <- desugar_record_update(meta, children, env) do
      elaborate_expr_typed(positional, names, ctx, env)
    end
  end

  # Projection of a literal pair reduces by the Σ β-rule (`fst %[a,b] = a`,
  # `snd %[a,b] = b`), so we take the component directly — no `{:pair, …}` is built
  # and the kernel is never asked to infer a bare pair. This is what makes a
  # let-bound pair work: `let p = %[a, b]` is substitution-based, so `p.1`/`p.2`
  # become `%[a, b].1`/`.2` after inlining.
  def elaborate_expr_typed({:attribute_access, meta, [{:tuple, _tm, [a, b]}]} = expr, names, ctx, env) do
    case Keyword.fetch!(meta, :attribute) do
      "1" -> elaborate_expr_typed(a, names, ctx, env)
      "2" -> elaborate_expr_typed(b, names, ctx, env)
      _ -> {:error, {:unsupported_expression, expr}}
    end
  end

  def elaborate_expr_typed({:attribute_access, meta, [inner]}, names, ctx, env) do
    attr = Keyword.fetch!(meta, :attribute)

    case parse_positional_index(attr) do
      {:ok, i} -> positional_projection(i, inner, names, ctx, env)
      :error -> record_projection(inner, attr, names, ctx, env)
    end
  end

  def elaborate_expr_typed({:rewrite_expr, _meta, _children}, _names, _ctx, _env),
    do: {:error, :rewrite_requires_expected_type}

  # `assert_type expr : T` — a compile-time ascription. Lower `T`, then elaborate
  # `expr` in CHECKING mode against it (so the assertion can also steer inference).
  # The wrapper carries no runtime content: the result IS the checked term at type
  # `T`, so emit sees only `expr`. Mirrors the classic codegen, which strips it.
  def elaborate_expr_typed({:assert_type, _meta, [expr, type_ast]}, names, ctx, env) do
    with {:ok, expected_core} <- elaborate_type(type_ast, names, env),
         {:ok, term} <- elaborate_expr_checked(expr, expected_core, names, ctx, env) do
      {:ok, term, Eval.eval(expected_core, Context.env(ctx))}
    end
  end

  def elaborate_expr_typed({:literal, meta, value} = expr, names, ctx, env) do
    case Keyword.get(meta, :subtype) do
      :boolean when is_boolean(value) ->
        ctor = resolve_ctor_key(env, if(value, do: :True, else: :False))
        {:ok, {:ctor, ctor, []}, Kernel.bool_type_value(Context.signature(ctx))}

      :integer when is_integer(value) ->
        {:ok, {:int_lit, value}, {:vint_type}}

      :float when is_float(value) ->
        {:ok, {:float_lit, value}, {:vfloat_type}}

      :char when is_integer(value) and value >= 0 and value <= 0x10FFFF ->
        case char_type_value(Context.signature(ctx)) do
          {:ok, ty} -> {:ok, {:bounded_lit, value}, ty}
          :no_bounded -> {:error, {:char_literal_needs_bounded, value}}
        end

      :char when is_integer(value) ->
        {:error, {:char_literal_out_of_range, value}}

      # A string literal IS `List(Char)` — desugar to the char-literal list
      # `['c₀', …, 'cₙ']` (one element per Unicode codepoint) and elaborate that,
      # so `"abc"` and `['a','b','c']` produce the identical Cons spine.
      :string when is_binary(value) ->
        elaborate_expr_typed(desugar_string(value, meta), names, ctx, env)

      # A byte binary literal `<<1, 2, 3>>` desugars to `Std.Binary.of_bytes/1`.
      :bytes when is_list(value) ->
        with {:ok, surface} <- desugar_bytes(value, Keyword.get(meta, :line, 0)) do
          elaborate_expr_typed(surface, names, ctx, env)
        end

      # A symbol literal `:ok` is a value of the Int-tier primitive `Atom` base
      # type — a BEAM atom is its own canonical value (Core `{:atom_lit, a}`).
      :symbol when is_atom(value) ->
        {:ok, {:atom_lit, value}, {:vatom_type}}

      _ ->
        {:error, {:unsupported_expression, expr}}
    end
  end

  # `if c then t else e` — lowered to a `:case` on the inductive `Bool`. In
  # inference mode we infer the `then` branch's type T, check `else` against T,
  # and use the constant motive `λ_:Bool. T` (both branches share the type T).
  def elaborate_expr_typed({:conditional, _meta, [c, t, e]}, names, ctx, env) do
    with {:ok, c_core} <- elaborate_expr_checked(c, bool_type_term(Context.signature(ctx)), names, ctx, env),
         {:ok, t_core, t_type} <- elaborate_expr_typed(t, names, ctx, env),
         t_type_core = Quote.reify(t_type, Context.length(ctx)),
         {:ok, e_core} <- elaborate_expr_checked(e, t_type_core, names, ctx, env) do
      {:ok, bool_case(c_core, t_type_core, t_core, e_core, ctx), t_type}
    end
  end

  # A `let … ⏎ body` block in INFERENCE position — the counterpart to the
  # check-mode `{:block}` clause (`elaborate_let_block/5`). Enables annotation-free
  # function bodies (`fn f() = let a = 1 ⏎ a + 1`) and any inference-position block.
  # There is no `:let` desugaring to guess a type for: build the `:let` Core chain
  # by inferring each binding's rhs, then let the kernel infer the whole term's type
  # (which sidesteps hand-managing the de Bruijn depth of the body's type).
  def elaborate_expr_typed({:block, _meta, stmts}, names, ctx, env) do
    with {:ok, term} <- infer_block_term(stmts, names, ctx, env),
         {:ok, type} <- Kernel.infer(ctx, term) do
      {:ok, term, type}
    end
  end

  # A surface unary operator. `not` is retired as a kernel primitive: it lowers to
  # an application of the `Std.Bool` prelude def `not` (a `case`-eliminating
  # function over the inductive Bool). The kernel checks the operand against Bool
  # and infers the result. Any other unary operator is unsupported here.
  def elaborate_expr_typed({:unary_op, meta, [operand]} = expr, names, ctx, env) do
    case Keyword.fetch!(meta, :operator) do
      :not ->
        with {:ok, o_core, _ot} <- elaborate_expr_typed(operand, names, ctx, env),
             term = {:app, {:global, :not}, o_core},
             {:ok, type} <- Kernel.infer(ctx, term) do
          {:ok, term, type}
        end

      # Int-only bitwise complement. `int_bnot : Int -> Int`, so the kernel
      # infer both types the operand against Int and rejects a non-Int operand.
      :bnot ->
        with {:ok, o_core, _ot} <- elaborate_expr_typed(operand, names, ctx, env),
             term = {:app, {:global, builtin_op_global(:int_bnot)}, o_core},
             {:ok, type} <- Kernel.infer(ctx, term) do
          {:ok, term, type}
        end

      # Numeric negation. Type-directed exactly like binary arithmetic: infer the
      # operand's primitive kind, then lower to `int_neg`/`float_neg` (both return
      # their operand type). A non-numeric operand rejects as unsupported.
      :- ->
        with {:ok, o_core, o_type} <- elaborate_expr_typed(operand, names, ctx, env),
             {:ok, g} <- neg_global(o_type, ctx),
             term = {:app, {:global, builtin_op_global(g)}, o_core},
             {:ok, type} <- Kernel.infer(ctx, term) do
          {:ok, term, type}
        end

      _ ->
        {:error, {:unsupported_expression, expr}}
    end
  end

  # A surface binary operator (K2 phase 2 + Amendment A1). Arithmetic and
  # comparisons lower to registry-keyed builtin-op GLOBAL spines, type-directed
  # by the left operand: Int → int_*, Float → float_*. The Boolean CONNECTIVES
  # `and`/`or` lower to the `Std.Bool` prelude defs. `==`/`!=` dispatch 4-way:
  # Bool → `eq`/`ne` defs; Int/Float → `int_eq`/`float_eq` twins; any OTHER
  # operand type (ADT, neutral, type variable) → the polymorphic structural
  # `struct_eq`/`struct_ne` global applied to the READBACK of the operand type
  # (A1 §1-A — today's runtime-structural semantics, verbatim). We elaborate
  # both operands in inference mode, assemble the term, and let the kernel
  # infer the result type.
  # Concatenation is an operator overload resolved through the `Std.Semigroup`
  # interface, not a bespoke `build_binop` case: `x <> y` desugars to the
  # `combine` method, which coherence dispatches by the operand's type (the
  # `List` instance delegates to the reducing library `Std.List.append`). A
  # non-numeric `+` is the same overload (Swift-style) — numeric `+`/`-`/`<`/…
  # keep their primitive meaning and only route here when `build_binop` reports
  # the operand type has no primitive op.
  def elaborate_expr_typed({:binary_op, meta, [l, r]} = expr, names, ctx, env) do
    op = Keyword.fetch!(meta, :operator)

    if op == :<> do
      combine_call(l, r, names, ctx, env)
    else
      with {:ok, l_core, l_type} <- elaborate_expr_typed(l, names, ctx, env),
           {:ok, r_core, _rt} <- elaborate_expr_typed(r, names, ctx, env),
           {:ok, term} <- build_binop(op, l_core, r_core, l_type, ctx),
           {:ok, type} <- Kernel.infer(ctx, term) do
        {:ok, term, type}
      else
        {:error, {:unsupported_operand_type, :+}} ->
          combine_call(l, r, names, ctx, env)

        {:error, {:unsupported_operand_type, cmp}}
        when cmp in [:<, :>, :<=, :>=] ->
          compare_op_call(cmp, l, r, names, ctx, env)

        :unsupported_op ->
          {:error, {:unsupported_expression, expr}}

        other ->
          other
      end
    end
  end

  # A `match` in INFERENCE position (no expected type) — reached when a match
  # must have its type SYNTHESISED rather than checked: as the scrutinee of an
  # outer match, or (via `let`'s surface substitution, `elaborate_let_block`)
  # `let b = match n … ⏎ match b …`, which inlines the inner match into the outer
  # scrutinee slot. NON-DEPENDENT synthesis, faithful to Idris' case-function
  # lift: infer the scrutinee's data family, synthesise a candidate result type
  # `T` from the FIRST constructor arm's body (inferred in that arm's branch
  # context), verify `T` does NOT mention the arm's constructor-bound variables
  # (else the match is genuinely dependent and — exactly as in Idris — needs an
  # annotation, so we reject with `:cannot_infer_dependent_match`), strengthen it
  # out of the branch frame, then hand `T` to the CHECKED path (`elaborate_match`)
  # so every arm is checked against the one synthesised type. That reuses all the
  # coverage/motive/index machinery and, since `T` is non-scrutinee-dependent, the
  # motive it builds is effectively constant — correct for inference position.
  def elaborate_expr_typed({:pattern_match, meta, [scrut | arms]} = expr, names, ctx, env)
      when is_list(meta) do
    arms = arms |> desugar_list_patterns() |> desugar_typed_constructor_args()

    if special_match_arms?(arms) do
      with {:ok, desugared} <- desugar_special_match(scrut, arms, Keyword.get(meta, :line, 0)) do
        elaborate_expr_typed(desugared, names, ctx, env)
      end
    else
      with {:ok, _scrut_term, {:vdata, dname, combined_vals}} <-
             elaborate_expr_typed(scrut, names, ctx, env),
           {:ok, {cname, pattern_vars, body_expr}} <- first_constructor_arm(arms, env),
           %{args: telescope, quantities: quantities} <- Inductive.get_ctor(env, cname),
           arity = length(telescope),
           pc = Inductive.param_count(env, dname),
           {param_vals, _idx_vals} = Enum.split(combined_vals, pc),
           branch_names = branch_scope(telescope, quantities, pattern_vars) ++ names,
           branch_ctx = extend_context(ctx, telescope, param_vals),
           {:ok, _b_term, t_branch_val} <-
             elaborate_expr_typed(body_expr, branch_names, branch_ctx, env),
           t_branch = Quote.reify(t_branch_val, Context.length(branch_ctx)),
           {:ok, result_type_term} <- strengthen_inferred_type(t_branch, arity),
           {:ok, term} <- elaborate_match(scrut, arms, result_type_term, names, ctx, env),
           result_type_val = Eval.eval(result_type_term, Context.env(ctx)),
           :ok <- Kernel.check(ctx, term, result_type_val) do
        {:ok, term, result_type_val}
      else
        {:ok, _term, _non_data_type} -> {:error, {:cannot_infer_match_type, expr}}
        {:error, _} = err -> err
      end
    end
  end

  # `pickup` predicate dispatch (value-surface Wave 1). Pure syntactic
  # desugaring to a right-nested `:conditional` chain; reuses the conditional
  # path's Bool-guard and branch-join checks verbatim. No kernel change.
  # See docs/superpowers/specs/2026-07-09-wave1-pickup-design.md.
  def elaborate_expr_typed({:pickup, _meta, clauses}, names, ctx, env) do
    with {:ok, desugared} <- desugar_pickup(clauses) do
      elaborate_expr_typed(desugared, names, ctx, env)
    end
  end

  # Wave-2 List sugar: rewrite `[]`/`[h|t]`/`[a,b,c]` to Nil/Cons ctor-call form
  # and delegate, reusing all ctor inference (see desugar_list/1).
  # `()` — the unit value (Swift-style), the sole inhabitant of `Unit`. It is the
  # nullary `unit` constructor of the seeded `Unit` family; the same node emit
  # already understands as the empty-telescope terminator.
  def elaborate_expr_typed({:unit_value, _meta}, _names, _ctx, env) do
    {:ok, {:ctor, unit_ctor_name(env), []}, {:data, unit_family_name(env), [], []}}
  end

  def elaborate_expr_typed({:list, _, _} = node, names, ctx, env),
    do: elaborate_expr_typed(desugar_list(node), names, ctx, env)

  # `return e` — in tail position it IS the value of the enclosing function or
  # branch, so it elaborates as the identity on `e`. The classic throw/catch
  # unwind is dropped (a total language has no such escape); the STRUCTURED
  # tail-position meaning is all that survives.
  def elaborate_expr_typed({:early_return, _meta, [e]}, names, ctx, env),
    do: elaborate_expr_typed(e, names, ctx, env)

  # Integer range `a..b` (exclusive) / `a..=b` (inclusive). Desugars to a call to
  # the total structurally-recursive helper `Std.Nat.range_upto{,_incl}` (auto-
  # prelude, so no `use` is needed) — the honest analog of Idris's `enumFromTo`.
  # The list construction is genuine recursion; only the `Int -> Nat` count cast
  # (`Std.Nat.of_int`) is a trusted primitive boundary.
  def elaborate_expr_typed({:range, meta, [from_ast, to_ast]}, names, ctx, env) do
    fname = if Keyword.get(meta, :inclusive, false), do: "range_upto_incl", else: "range_upto"
    line = Keyword.get(meta, :line, 0)
    call = {:function_call, [name: fname, line: line], [from_ast, to_ast]}
    elaborate_expr_typed(call, names, ctx, env)
  end

  # List comprehension `[e for x <- xs, cond, y <- ys]`. Desugars (before Core) to
  # the textbook Wadler translation over already-supported constructs — nothing new
  # reaches the kernel:
  #   * no qualifiers left        -> `[e]`               (singleton list)
  #   * generator `x <- src`      -> `flat_map(src, fn(x) -> <rest>)`
  #   * filter `cond`             -> `if cond then <rest> else []`
  # The sole library dependency is `flat_map` (Std.List; `use`d or, at #18, the
  # dependent-compiled stdlib). Generator patterns must currently be a plain
  # variable — a destructuring generator is rejected rather than silently mistyped.
  def elaborate_expr_typed({:comprehension, meta, [body | quals]}, names, ctx, env) do
    case desugar_comprehension(quals, body, Keyword.get(meta, :line, 0)) do
      {:ok, desugared} -> elaborate_expr_typed(desugared, names, ctx, env)
      {:error, _} = err -> err
    end
  end

  # String interpolation `"a#{e}b"` desugars to a right fold of `str_concat` over
  # the segments (see `desugar_interpolation`). String-valued holes only; a
  # non-string hole fails as an ordinary type error against `str_concat`'s
  # `List(Char)` parameter.
  def elaborate_expr_typed({:string_interpolation, meta, segments}, names, ctx, env) do
    elaborate_expr_typed(
      desugar_interpolation(segments, Keyword.get(meta, :line, 0)),
      names,
      ctx,
      env
    )
  end

  # Map literal `%{k: v, …}`. Desugars (before Core) to nested `Std.Map.put`
  # calls over `Std.Map.new()` — the same shape a hand-written builder has, so
  # nothing new reaches the kernel. `Std.Map` is a thin `@extern` wrapper over
  # Erlang `:maps`, so this is seam-free (the runtime value is always a raw map);
  # the caller must have `use Std.Map` in scope for `put`/`new` to resolve.
  def elaborate_expr_typed({:map, meta, pairs}, names, ctx, env) do
    elaborate_expr_typed(desugar_map(pairs, Keyword.get(meta, :line, 0)), names, ctx, env)
  end

  # Pair introduction `%[a, b]` in typed-synthesis position (a ctor argument, a
  # `let` rhs, any sub-term the checked tuple clause at line ~1137 doesn't reach).
  # Synthesizes the non-dependent Σ `Sigma(A, λ_:A. B)` from the inferred component
  # types — the honest surface `Tuple(A, B)`. Mirrors the scope-based builder
  # (`elaborate_expr/3`, ~5129) and the checked clause; a *genuinely dependent* pair
  # still needs a checking position (its expected type supplies the codomain family).
  # The codomain `B` is closed w.r.t. the fresh Σ binder, so it is shifted +1 to keep
  # its free de Bruijn indices pointing at the same context entries under the `λ`.
  def elaborate_expr_typed({:tuple, _meta, [_, _ | _] = elems}, names, ctx, env) do
    with {:ok, parts} <- elaborate_tuple_parts(elems, names, ctx, env) do
      {value, type_term} = build_telescope_value(parts, ctx, env)
      {:ok, value, Eval.eval(type_term, Context.env(ctx))}
    end
  end

  # Quasiquotation (SP5.1) in checked position: lower `quote` to its builder
  # expression and check that against the expected type (`Syntax`).
  def elaborate_expr_typed({:quoted_syntax, _meta, [inner]}, names, ctx, env),
    do: elaborate_expr_typed(Cure.Compiler.MacroSyntax.lower_quote(inner), names, ctx, env)

  def elaborate_expr_typed({tag, meta, _}, _names, _ctx, _env) when tag in [:splice, :splice_group],
    do: {:error, {:splice_outside_quote, tag, meta}}

  def elaborate_expr_typed(other, _names, _ctx, _env), do: {:error, {:unsupported_expression, other}}

  # Synthesise each element of a tuple literal to `{core, type_term}` (the inferred
  # type reified to a Core term at the current depth).
  defp elaborate_tuple_parts(elems, names, ctx, env) do
    len = Context.length(ctx)

    Enum.reduce_while(elems, {:ok, []}, fn e, {:ok, acc} ->
      case elaborate_expr_typed(e, names, ctx, env) do
        {:ok, core, type} -> {:cont, {:ok, acc ++ [{core, Quote.reify(type, len)}]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # Build the unit-terminated telescope value + type from synthesised parts:
  # `%[e1, …, en]` (no expected type) is a flat `Tuple(T1, …, Tn)` —
  # `mk_pair(e1, … mk_pair(en, unit))` at type `Sigma(T1, λ. … Sigma(Tn, λ. Unit))`.
  # A genuinely DEPENDENT pair still needs a checking position (its expected type
  # supplies the codomain family); synthesis is the non-dependent product, which
  # is exactly a Tuple. Folds from the right so each accumulated type shifts +1
  # under the fresh Σ binder (non-dependent, so the binder is unused).
  defp build_telescope_value(parts, _ctx, env) do
    mk_pair = sigma_ctor_name(env)
    fam = Inductive.builtin(env, :sigma)
    unit_ctor = unit_ctor_name(env)
    unit_family = unit_family_name(env)

    Enum.reduce(Enum.reverse(parts), {{:ctor, unit_ctor, []}, {:data, unit_family, [], []}}, fn
      {core, type_term}, {val_acc, type_acc} ->
        value = {:ctor, mk_pair, [core, val_acc]}
        cod = {:lam, Cure.Core.Grade.unrestricted(), type_term, Cure.Core.Term.shift(type_acc, 1)}
        type = {:data, fam, [type_term, cod], []}
        {value, type}
    end)
  end

  # Desugar a concatenation operator to the `Std.Semigroup.combine` method call,
  # letting the interface-dispatch machinery pick the instance by operand type.
  defp combine_call(l, r, names, ctx, env),
    do: elaborate_expr_typed({:function_call, [name: "combine"], [l, r]}, names, ctx, env)

  # Desugar a comparison operator on a NON-primitive operand to the
  # `Std.Comparable.compare` method, tested against an `Ordering` constructor.
  # The comparison operators ARE the surface for `Comparable` (there are no
  # `lt`/`le`/`gt`/`ge` named helpers); each maps to a `compare` + `Ordering`
  # test:
  #
  #     a <  b  ~>  compare(a, b) == LessThan()
  #     a >  b  ~>  compare(a, b) == GreaterThan()
  #     a <= b  ~>  compare(a, b) != GreaterThan()
  #     a >= b  ~>  compare(a, b) != LessThan()
  #
  # `compare` dispatches by coherence to the operand's `Ord` instance; the
  # `==`/`!=` on the `Ordering` result rides the usual `struct_eq`/`struct_ne`
  # path. Reached only when `build_binop` reports the operand type has no
  # primitive `<`/`>`/`<=`/`>=` (Int/Float keep their primitive meaning).
  # Requires `use Std.Comparable` in scope so `compare` and the `Ordering`
  # constructors resolve (class-import model, like `combine`).
  defp compare_op_call(cmp, l, r, names, ctx, env) do
    {ctor, eq_op} =
      case cmp do
        :< -> {"LessThan", :==}
        :> -> {"GreaterThan", :==}
        :<= -> {"GreaterThan", :!=}
        :>= -> {"LessThan", :!=}
      end

    compare = {:function_call, [name: "compare"], [l, r]}
    ordering = {:function_call, [name: ctor], []}
    elaborate_expr_typed({:binary_op, [operator: eq_op], [compare, ordering]}, names, ctx, env)
  end

  # Fold a `pickup` clause list into a right-nested `:conditional` chain.
  # The LAST clause is the terminator (its body is the seed); every earlier
  # clause is a guard wrapper `{:conditional, [], [guard, body, acc]}`.
  # Three terminator shapes (matching codegen.ex's pickup lowering exactly):
  #   {:pickup_else, _, [e]}                         -> seed e
  #   {:pickup_clause, _, [{:literal, _, true}, e]}  -> seed e (guard discarded)
  #   anything else in last position                 -> defensive error
  # A single-clause pickup (only the terminator) collapses to the seed body
  # with no wrapping conditional (PICKUP §11: `pickup else -> e ≡ e`).
  # The empty/terminatorless shapes are impossible post-parse (the parser's
  # validate_pickup_clauses enforces them); the error arms are belt-and-suspenders.
  defp desugar_pickup([]), do: {:error, {:pickup_missing_else, []}}

  defp desugar_pickup(clauses) do
    {wrappers, [last]} = Enum.split(clauses, length(clauses) - 1)

    with {:ok, seed} <- pickup_seed(last) do
      fold_pickup_wrappers(wrappers, seed)
    end
  end

  defp fold_pickup_wrappers(wrappers, seed) do
    Enum.reduce_while(Enum.reverse(wrappers), {:ok, seed}, fn
      {:pickup_clause, _cm, [g, b]}, {:ok, acc} ->
        {:cont, {:ok, {:conditional, [], [g, b, acc]}}}

      other, {:ok, _acc} ->
        {:halt, {:error, {:pickup_missing_else, other}}}
    end)
  end

  defp pickup_seed({:pickup_else, _m, [e]}), do: {:ok, e}
  defp pickup_seed({:pickup_clause, _m, [{:literal, _, true}, e]}), do: {:ok, e}
  defp pickup_seed(other), do: {:error, {:pickup_missing_else, other}}

  # The first arm whose pattern is a constructor application, as
  # `{resolved_ctor, pattern_vars, body}` — the arm used to synthesise an
  # inference-position match's result type. Variable/wildcard (default) arms are
  # skipped; if no constructor arm exists the match cannot be synthesised here.
  defp first_constructor_arm(arms, env) do
    Enum.find_value(arms, {:error, {:cannot_infer_match_type, :no_constructor_arm}}, fn
      {:match_arm, arm_meta, body} ->
        case constructor_pattern(Keyword.fetch!(arm_meta, :pattern)) do
          {:ok, {cname0, pattern_vars}} ->
            cname = resolve_ctor_key(env, cname0)

            if Inductive.get_ctor(env, cname),
              do: {:ok, {cname, pattern_vars, single_body(body)}},
              else: false

          {:error, _} ->
            false
        end

      _other ->
        false
    end)
  end

  # Strengthen a branch-body type out of the constructor's `arity` bound vars (de
  # Bruijn 0..arity-1, most-recently bound). If any of those occur the type is
  # genuinely dependent — reject (needs an annotation); otherwise shift the free
  # outer variables down by `arity` (the inverse of `Subst.shift(_, arity, 0)`).
  defp strengthen_inferred_type(t_branch, 0), do: {:ok, t_branch}

  defp strengthen_inferred_type(t_branch, arity) do
    if occurs_below?(t_branch, arity, 0),
      do: {:error, {:cannot_infer_dependent_match, t_branch}},
      else: {:ok, Subst.shift(t_branch, -arity, 0)}
  end

  # Does any de Bruijn variable in the window `[depth, depth + arity)` occur in
  # `term`? Binder cutoffs are tracked EXACTLY as `Subst.shift` does (pi/lam/sigma
  # add one, each `:case` branch adds its own arity), so a positive answer means
  # strengthening by `-arity` at cutoff 0 would capture/underflow — i.e. the type
  # depends on the constructor-bound variables.
  defp occurs_below?({:var, k}, arity, depth), do: k >= depth and k < depth + arity

  defp occurs_below?({:pi, _g, d, c}, arity, depth),
    do: occurs_below?(d, arity, depth) or occurs_below?(c, arity, depth + 1)

  defp occurs_below?({:lam, _g, d, b}, arity, depth),
    do: occurs_below?(d, arity, depth) or occurs_below?(b, arity, depth + 1)

  defp occurs_below?({:case, s, m, brs}, arity, depth) do
    occurs_below?(s, arity, depth) or occurs_below?(m, arity, depth) or
      Enum.any?(brs, fn {_cn, ar, b} -> occurs_below?(b, arity, depth + ar) end)
  end

  defp occurs_below?(t, arity, depth) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.any?(&occurs_below?(&1, arity, depth))

  defp occurs_below?(l, arity, depth) when is_list(l),
    do: Enum.any?(l, &occurs_below?(&1, arity, depth))

  defp occurs_below?(_other, _arity, _depth), do: false

  # Surface operator symbols (from `Precedence.operator_symbol/1`) to the
  # builtin-op key the type-directed dispatch maps onto a monomorphic global
  # (K2). Only the ops with registered globals are mapped; `<>` (string
  # concat), `..`, and the like are left unsupported here.
  defp prim_op(:+), do: {:ok, :add}
  defp prim_op(:-), do: {:ok, :sub}
  defp prim_op(:*), do: {:ok, :mul}
  defp prim_op(:/), do: {:ok, :div}
  defp prim_op(:rem), do: {:ok, :rem}
  defp prim_op(:<), do: {:ok, :lt}
  defp prim_op(:>), do: {:ok, :gt}
  defp prim_op(:<=), do: {:ok, :le}
  defp prim_op(:>=), do: {:ok, :ge}
  # Int-only bitwise (no float twin — an @float_binop_globals miss rejects).
  defp prim_op(:band), do: {:ok, :band}
  defp prim_op(:bor), do: {:ok, :bor}
  defp prim_op(:bxor), do: {:ok, :bxor}
  defp prim_op(:bsl), do: {:ok, :bsl}
  defp prim_op(:bsr), do: {:ok, :bsr}
  defp prim_op(_), do: :error

  # Assemble the Core term for a surface binary operator (K2 phase 2 + A1).
  # The connectives and Bool-operand equality become applications of the
  # Std.Bool prelude defs; arithmetic/comparisons become type-directed
  # builtin-op global spines (int_*/float_*); non-primitive-typed `==`/`!=`
  # becomes the polymorphic structural `struct_eq`/`struct_ne` global applied
  # to the quoted operand type. Maps are explicit literals (no dynamic atom
  # construction). The float map has NO `rem` entry — `rem` on Float is
  # `{:error, {:unsupported_operand_type, :rem}}` (enumerated R5 churn; today
  # it dies as kernel `{:prim_type, :rem}`).
  @int_binop_globals %{
    add: :int_add,
    sub: :int_sub,
    mul: :int_mul,
    div: :int_div,
    rem: :int_rem,
    lt: :int_lt,
    le: :int_le,
    gt: :int_gt,
    ge: :int_ge,
    band: :int_band,
    bor: :int_bor,
    bxor: :int_bxor,
    bsl: :int_bsl,
    bsr: :int_bsr
  }
  @float_binop_globals %{
    add: :float_add,
    sub: :float_sub,
    mul: :float_mul,
    div: :float_div,
    lt: :float_lt,
    le: :float_le,
    gt: :float_gt,
    ge: :float_ge
  }

  defp build_binop(:and, l, r, _l_type, _ctx), do: {:ok, app2(:and, l, r)}
  defp build_binop(:or, l, r, _l_type, _ctx), do: {:ok, app2(:or, l, r)}

  defp build_binop(op_sym, l, r, l_type, ctx) when op_sym in [:==, :!=] do
    case primitive_scrut_kind(l_type, Context.signature(ctx)) do
      {:ok, :bool} ->
        {:ok, app2(if(op_sym == :==, do: :eq, else: :ne), l, r)}

      {:ok, :int} ->
        {:ok, app2(builtin_op_global(if(op_sym == :==, do: :int_eq, else: :int_ne)), l, r)}

      {:ok, :float} ->
        {:ok, app2(builtin_op_global(if(op_sym == :==, do: :float_eq, else: :float_ne)), l, r)}

      # An indexed family (Bounded — Char) erases to a native int but is not a
      # monomorphic twin, so it takes the same polymorphic struct_eq path.
      {:ok, :bounded} ->
        struct_eq_binop(op_sym, l, r, l_type, ctx)

      :error ->
        struct_eq_binop(op_sym, l, r, l_type, ctx)
    end
  end

  defp build_binop(op_sym, l, r, l_type, ctx) do
    case prim_op(op_sym) do
      {:ok, op} ->
        case primitive_scrut_kind(l_type, Context.signature(ctx)) do
          {:ok, :int} ->
            case Map.fetch(@int_binop_globals, op) do
              {:ok, g} -> {:ok, app2(builtin_op_global(g), l, r)}
              :error -> {:error, {:unsupported_operand_type, op_sym}}
            end

          {:ok, :float} ->
            case Map.fetch(@float_binop_globals, op) do
              {:ok, g} -> {:ok, app2(builtin_op_global(g), l, r)}
              :error -> {:error, {:unsupported_operand_type, op_sym}}
            end

          # No Bool arithmetic; non-numeric operand types reject here
          # (enumerated R5 churn — today these die as kernel {:prim_type, op}).
          _ ->
            {:error, {:unsupported_operand_type, op_sym}}
        end

      :error ->
        :unsupported_op
    end
  end

  # A1 §1-A: structural equality — struct_eq/struct_ne applied to the readback of
  # the operand type. The readback is signature-aware: an applied INDEXED family
  # (e.g. `Bounded(n)`, Char's underlying type) must keep its param/index split,
  # because this `ty` flows into `Kernel.infer` (the caller), which arity-checks
  # params and indices separately — a sig-less readback flattens the index into
  # the param slot and the kernel rejects it with `:arg_arity`. A meta-containing
  # readback must never reach the kernel (R8b): reject defensively (corpus
  # predicts none).
  defp struct_eq_binop(op_sym, l, r, l_type, ctx) do
    ty = Quote.reify(l_type, Context.length(ctx), Context.signature(ctx))

    if Unify.has_meta?(ty) do
      {:error, {:unsupported_operand_type, op_sym}}
    else
      g = builtin_op_global(if op_sym == :==, do: :struct_eq, else: :struct_ne)
      {:ok, {:app, app2(g, ty, l), r}}
    end
  end

  # Pick the type-directed negation builtin from the operand's primitive kind,
  # mirroring `build_binop`'s Int→int_*/Float→float_* dispatch for unary `-x`.
  defp neg_global(o_type, ctx) do
    case primitive_scrut_kind(o_type, Context.signature(ctx)) do
      {:ok, :int} -> {:ok, :int_neg}
      {:ok, :float} -> {:ok, :float_neg}
      _ -> {:error, {:unsupported_operand_type, :-}}
    end
  end

  # A saturated `f(a)(b)` application of a global by name, most-recently-applied
  # argument outermost — the shape the kernel + emit expect for a curried def.
  defp app2(name, l, r), do: {:app, {:app, {:global, name}, l}, r}

  # The canonical global identity of a kernel builtin op. `Builtins.seed/2`
  # registers these under `Std.Builtin#<op>` (see `builtin_op_name/1` there), so a
  # reference must name the same owner — otherwise it only resolves through
  # `Env.resolve_key`'s base-scan fallback and a raw `env.defs` walk (the trust
  # ledger's) sees the def as unresolved.
  defp builtin_op_global(op), do: Cure.Elab.Name.qualify("Std.Builtin", op)

  # `.1`/`.2` lower to an application of the Std.Sigma projection global
  # (`sigma_first`/`sigma_second`), with the erased implicits `{a}`/`{b}` solved
  # from `inner`'s inferred `Sigma(a, b)` type by the implicit-insertion machinery.
  # `inner` is the SURFACE AST (not the already-lowered term) so the wrapper infers
  # it in the caller's context. Same `{:ok, term, result_type}` contract as before.
  defp sigma_projection(which, inner, names, ctx, env) do
    gname = if which == :fst, do: :sigma_first, else: :sigma_second
    elaborate_implicit_global_app(env, gname, [inner], names, ctx)
  end

  # `element(t, i)` is the dependent n-ary projection form iff called with exactly
  # two arguments and a STATIC positive-integer literal index — the only shape for
  # which the compile-time bounds check is meaningful. Any other `element(…)` call
  # falls through to ordinary name resolution.
  defp element_projection?([_t_arg, {:literal, _meta, i}]) when is_integer(i) and i >= 1, do: true
  defp element_projection?(_), do: false

  # A `.N` attribute where `N` is a positive integer is a POSITIONAL projection
  # (`.1`, `.2`, …); anything else is a record field name.
  defp parse_positional_index(attr) do
    case Integer.parse(attr) do
      {i, ""} when i >= 1 -> {:ok, i}
      _ -> :error
    end
  end

  # Positional projection `base.i`. When `base` is a flat unit-terminated
  # telescope of arity `n` (a `Tuple(T1,…,Tn)` value, lowered to a flat BEAM
  # tuple), `.i` for `i ≥ 2` lowers to the `Std.Sigma` positional-projection
  # global `tproj_i` — typed at the true i-th component `Ti` and inlined to
  # `element(i, base)` (see sigma.cure). `.1` is `sigma_first` (correct for any
  # telescope). For a bare dependent pair (`Sigma(a, b)`, tail not `Unit`) or any
  # non-telescope, `.1`/`.2` keep their `sigma_first`/`sigma_second` meaning and
  # a higher index falls to the record path — exactly the pre-telescope behavior.
  # The classification is a heuristic over `base`'s inferred type; the kernel
  # re-checks the chosen `tproj_i` application against its real signature, so a
  # misclassification can only surface as a clean rejection, never unsoundness.
  defp positional_projection(i, inner, names, ctx, env) do
    case telescope_arity_of(inner, names, ctx, env) do
      {:telescope, n} when i <= n and i >= 2 ->
        elaborate_implicit_global_app(env, :"tproj#{i}", [inner], names, ctx)

      {:telescope, n} when i <= n ->
        sigma_projection(:fst, inner, names, ctx, env)

      # The arity is statically known and `i` is out of `[1, n]` — reject at
      # elaboration. A telescope carries its arity in its type, so an
      # out-of-bounds positional access (`t.9` / `element(t, 9)` on a 3-tuple)
      # is a compile-time error, never a runtime `element/2` crash.
      {:telescope, n} ->
        {:error, {:telescope_index_out_of_bounds, i, n}}

      _ ->
        case i do
          1 -> sigma_projection(:fst, inner, names, ctx, env)
          2 -> sigma_projection(:snd, inner, names, ctx, env)
          _ -> record_projection(inner, Integer.to_string(i), names, ctx, env)
        end
    end
  end

  # `{:telescope, n}` when `inner`'s inferred type is a unit-terminated Σ
  # telescope of arity `n` (`Sigma(T1, … Sigma(Tn, Unit))`), else `:not_telescope`.
  defp telescope_arity_of(inner, names, ctx, env) do
    case elaborate_expr_typed(inner, names, ctx, env) do
      {:ok, _term, type_value} ->
        case Inductive.builtin(env, :sigma) do
          nil ->
            :not_telescope

          sigma_fam ->
            # `type_value` is a semantic VALUE (as returned by elaboration); read it
            # back to a Core term (family param/index split recovered via the sig)
            # before walking the Σ spine.
            type_term = Quote.reify(type_value, Context.length(ctx), Context.signature(ctx))
            count_tele(type_term, ctx, sigma_fam, unit_family_name(env), unit_ctor_name(env), 0)
        end

      _ ->
        :not_telescope
    end
  end

  # Walk the Σ spine, instantiating each codomain (non-dependent for a telescope,
  # so the applied argument is discarded) until a `Unit` terminator is reached.
  defp count_tele(type, ctx, sigma_fam, unit_fam, unit_ctor, n) do
    case Kernel.normalize(ctx, type) do
      {:data, ^sigma_fam, [_dom, cod], []} ->
        tail = Kernel.normalize(ctx, {:app, cod, {:ctor, unit_ctor, []}})
        count_tele(tail, ctx, sigma_fam, unit_fam, unit_ctor, n + 1)

      {:data, ^unit_fam, [], []} when n >= 1 ->
        {:telescope, n}

      _ ->
        :not_telescope
    end
  end

  # Record field projection `obj.field`. The object's type identifies its record
  # family; the field name is looked up in the (single) constructor's telescope —
  # whose argument names ARE the field names — and the projection is elaborated as a
  # one-branch `match obj | Rec(f0, …, fn) -> f_i` in checking mode, the field's own
  # type as the goal. The field type lives in the constructor frame `params ++
  # fields`; its parameter references are instantiated with the record value's
  # actual arguments (so `val : a` in `Box(Nat)` becomes `Nat`). A field type that
  # references an EARLIER FIELD (filled with the sentinel index below) is rejected —
  # a genuinely dependent record field, which projection does not yet support. A
  # field type that merely mentions the record PARAMETER at an abstract argument
  # (`eqs : a -> a -> Bool` on a dictionary `Eqs(a)` over a rigid `a`) is fine: it
  # is a legitimate context-open type, and the kernel re-checks the built `:case`.
  @proj_field_sentinel 1_000_000

  @doc """
  Public entry to project field `field` from the record-typed surface expression
  `inner`. Used by `Cure.Elab.Resolve` to pull an interface method off the
  in-scope dictionary parameter at an abstract (rigid-head) call site.
  """
  @spec project_record_field(term(), String.t(), [String.t()], Context.t(), Env.t()) ::
          {:ok, term(), term()} | {:error, term()}
  def project_record_field(inner, field, names, ctx, env),
    do: record_projection(inner, field, names, ctx, env)

  defp record_projection(inner, field, names, ctx, env) do
    with {:ok, _obj_term, obj_type} <- elaborate_expr_typed(inner, names, ctx, env) do
      case Quote.reify(obj_type, Context.length(ctx)) do
        {:data, rec, params, _indices} ->
          ctor = Inductive.get_ctor(env, rec)

          cond do
            is_nil(ctor) or ctor.name != rec ->
              {:error, {:projection_not_a_record, rec}}

            true ->
              fields = ctor.args
              idx = Enum.find_index(fields, fn {n, _t} -> Atom.to_string(n) == field end)

              # Instantiate the field's type in `params ++ fields`: the parameters
              # get the record's actual arguments, earlier-field slots get a
              # sentinel var (so a field-dependent field type is caught below).
              ftype =
                idx &&
                  Subst.instantiate(
                    elem(Enum.at(fields, idx), 1),
                    params ++ List.duplicate({:var, @proj_field_sentinel}, idx)
                  )

              cond do
                is_nil(idx) ->
                  {:error, {:unknown_field, rec, field}}

                mentions_prior_field?(ftype) ->
                  {:error, {:dependent_record_projection, rec, field}}

                true ->
                  binders = for i <- 0..(length(fields) - 1), do: {:variable, [scope: :local], "$proj#{i}"}

                  arm =
                    {:match_arm, [pattern: {:function_call, [name: Atom.to_string(rec)], binders}],
                     [Enum.at(binders, idx)]}

                  with {:ok, term} <- elaborate_match(inner, [arm], ftype, names, ctx, env) do
                    {:ok, term, Eval.eval(ftype, Context.env(ctx))}
                  end
              end
          end

        _ ->
          {:error, {:projection_non_record, field}}
      end
    end
  end

  # Does the term reference the prior-field sentinel index (`@proj_field_sentinel`,
  # substituted into earlier-field slots)? A `{:var, k}` at binder depth `d` is the
  # sentinel iff `k - d >= @proj_field_sentinel` — the sentinel is lifted by one per
  # binder crossed, so its distance from the current frame stays constant, while a
  # genuine context/parameter reference stays far below the threshold.
  defp mentions_prior_field?(term), do: mentions_prior_field?(term, 0)
  defp mentions_prior_field?({:var, k}, depth), do: k - depth >= @proj_field_sentinel

  defp mentions_prior_field?({:lam, _g, d, b}, depth),
    do: mentions_prior_field?(d, depth) or mentions_prior_field?(b, depth + 1)

  defp mentions_prior_field?({:pi, _g, d, c}, depth),
    do: mentions_prior_field?(d, depth) or mentions_prior_field?(c, depth + 1)

  defp mentions_prior_field?(tuple, depth) when is_tuple(tuple),
    do: tuple |> Tuple.to_list() |> Enum.any?(&mentions_prior_field?(&1, depth))

  defp mentions_prior_field?(list, depth) when is_list(list), do: Enum.any?(list, &mentions_prior_field?(&1, depth))
  defp mentions_prior_field?(_other, _depth), do: false

  @doc """
  Checking-mode elaboration for proof forms whose Core term depends on the
  expected type. Ordinary expressions fall back to infer-then-check.
  """
  @spec elaborate_expr_checked(term(), term(), [String.t()], Context.t(), Env.t()) ::
          {:ok, term()} | {:error, term()}
  def elaborate_expr_checked({:record_update, meta, children}, expected_core, names, ctx, env) do
    with {:ok, positional} <- desugar_record_update(meta, children, env) do
      elaborate_expr_checked(positional, expected_core, names, ctx, env)
    end
  end

  def elaborate_expr_checked({:function_call, meta, args} = expr, expected_core, names, ctx, env) do
    name = Keyword.fetch!(meta, :name)
    atom = String.to_atom(name)
    # Resolve a qualified (`Std.Nat.S`) or bare-shadowed (`S` under a local `Nat`
    # shadow, present only as `:"Std.Nat#S"`) constructor to its registry key
    # (spec §3.3); a non-dotted, registry-present name maps to itself.
    cres = resolve_ctor_key(env, atom)

    cond do
      Keyword.get(meta, :record) ->
        with {:ok, positional} <- desugar_record_construction(meta, args, env) do
          elaborate_expr_checked(positional, expected_core, names, ctx, env)
        end

      name == "reflexive" and length(args) == 1 ->
        [arg] = args

        # Checking-mode `reflexive(x)` — see the infer-mode note above. Build the
        # inductive ctor and let the kernel check it against the expected type.
        with {:ok, arg_term, _type} <- elaborate_expr_typed(arg, names, ctx, env),
             reflexive = resolve_ctor_key(env, :reflexive),
             term = {:ctor, reflexive, [arg_term]},
             :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
          {:ok, term}
        end

      Inductive.get_ctor(env, cres) ->
        # Checking-mode constructor: pin erased indices from the expected type (a
        # reconstructed dependent-match branch body like `prim()`/`seq(l,r)` whose
        # indices no present argument determines), then let the kernel re-check the
        # assembled constructor against the goal.
        #
        # The normal path infers each present argument first (`map_present_args`),
        # which fails for an *underdetermined nested constructor* — `Cons(Z(),
        # Nil())` at `-> List(Nat)`, whose inner `Nil()` has no argument to fix its
        # type parameter. When inference fails, fall back to a bidirectional pass
        # (`elaborate_ctor_app_bidirectional`) that solves the parameters from the
        # expected type first, then *checks* each argument against its field type.
        # The fallback is reached only when the inference path already errored, so a
        # working constructor is untouched; either way the kernel re-checks below.
        result =
          with {:ok, present} <- map_present_args(args, names, ctx, env),
               {:ok, term, _type} <- elaborate_ctor_app(env, cres, present, ctx, expected_core) do
            {:ok, term}
          end

        result =
          case result do
            {:ok, _} = ok ->
              ok

            {:error, _} = orig ->
              # Try the bidirectional fallback, but only let it *win when it
              # succeeds*: if it also fails, surface the original inference error
              # (e.g. a GADT `seq`'s genuine `:index_mismatch`), so the fallback is
              # strictly additive and never masks a real diagnostic.
              case elaborate_ctor_app_bidirectional(env, cres, args, names, ctx, expected_core) do
                {:ok, _} = ok -> ok
                {:error, _} -> orig
              end
          end

        case result do
          {:ok, term} ->
            case Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
              :ok -> {:ok, term}
              {:error, _} = err -> ctor_refinement_fallback(expr, expected_core, names, ctx, env, err)
            end

          {:error, _} = err ->
            ctor_refinement_fallback(expr, expected_core, names, ctx, env, err)
        end

      true ->
        # Non-constructor call in checking mode. Try the ordinary path first (infer
        # then re-check against the goal). When that fails specifically because a
        # call's implicit stayed unsolved AND we have a concrete expected type,
        # retry the application threading the expected return type in, so an
        # implicit determined by NEITHER argument — only by the return type — gets
        # solved (`mk : {a} -> {b} -> a -> Const(a, b)` at `-> Const(Nat, Bool)`
        # solves `b` from the goal). Additive: reached only after the ordinary path
        # errored with `:unsolved_metavariables`, and the retry surfaces that
        # original error if it too fails, so inference-position behaviour (no
        # expected type) is byte-for-byte unchanged.
        #
        # ONE goal-first pre-pass. This was three (`implicit_first`, `lambda_first`,
        # `union_first`) with byte-identical bodies and different guards, tried in
        # sequence — so a call satisfying two guards ran the same elaboration twice and
        # discarded the first result. Three guesses in a row is not a solving strategy;
        # they are a single rule, and the guard is their disjunction: when the goal can
        # inform solving, thread it in FROM THE START instead of inferring and re-checking.
        #
        # Each disjunct earns its place:
        #   * a concrete goal + an implicit def — an implicit determined by NEITHER
        #     argument, only by the return type (`mk : {a} -> {b} -> a -> Const(a, b)`
        #     at `-> Const(Nat, Bool)` solves `b` from the goal);
        #   * a lambda argument, whose domain the goal may fix.
        #
        # The former anonymous-union disjunct is GONE, not merged: an implicit def at a
        # concrete goal already covers it (a union goal that reaches here is a container
        # implicit — `Std.Map.put`'s `v` — so the first disjunct fires). It mattered only
        # because inferring a union-goal call SUCCEEDS but wrongly (solving `v := Int`
        # from the value argument), and a wrong-but-solved implicit is not
        # `:unsolved_metavariables`, so the retry below never fired. Threading the goal
        # first is what fixes that — and that is now the rule, not an exception to it.
        # Union INJECTION is untouched: it is a check-position coercion, not an ordering.
        #
        # Additive: falls back to the ordinary infer-then-check path on any failure, so
        # inference-position behaviour (no expected type) is unchanged.
        resolved = resolve_def_key(env, name, atom)

        # Partial application of an implicit-carrying def against a function-type
        # goal: eta-expand the missing explicit parameters into lambda binders —
        # `konst(7)` at `(Int) -> Int` becomes `fn(x) -> konst(7, x)`. The residual
        # binder domains come from the expected Π, reducing an under-saturated call
        # (which the saturating implicit paths reject with `:too_few_arguments`, or
        # mis-align the first explicit arg onto the leading implicit slot) to the
        # ordinary saturated path. Idris elaborates an under-applied function
        # checked against a function type exactly this way; the kernel re-checks the
        # synthesized lambda, so only eta-equivalent well-typed terms are accepted.
        residual = residual_explicit_arity(env, resolved, length(args))

        if residual > 0 and match?({:pi, _, _, _}, Kernel.normalize(ctx, expected_core)) do
          elaborate_expr_checked(
            eta_expand_call(meta, args, residual),
            expected_core,
            names,
            ctx,
            env
          )
        else
          elaborate_checked_call_saturated(expr, resolved, expected_core, args, names, ctx, env)
        end
    end
  end

  # A synthetic dictionary argument in checking position (the constrained-call
  # applicator's dictionary slot): build the instance's dictionary record value
  # and let the kernel check it against the expected `iface(head)` type.
  def elaborate_expr_checked({:dict_value, iface, head}, expected_core, _names, ctx, env) do
    with {:ok, term, _type} <- Cure.Elab.Resolve.dict_value(env, iface, head, ctx),
         :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
      {:ok, term}
    end
  end

  def elaborate_expr_checked({:rewrite_expr, _meta, [proof_ast, body_ast]}, expected_core, names, ctx, env) do
    depth = Context.length(ctx)

    with {:ok, proof_term, proof_type} <- elaborate_expr_typed(proof_ast, names, ctx, env),
         {:ok, ty_value, a_value, b_value} <- eq_parts(proof_type, Context.signature(ctx)),
         ty = Kernel.normalize(ctx, Quote.reify(ty_value, depth)),
         a = Kernel.normalize(ctx, Quote.reify(a_value, depth)),
         b = Kernel.normalize(ctx, Quote.reify(b_value, depth)),
         normalized_expected = Kernel.normalize(ctx, expected_core),
         {:ok, build, body_expected} <- rewrite_plan(ctx, proof_term, ty, a, b, normalized_expected),
         {:ok, body_term} <- elaborate_expr_checked(body_ast, body_expected, names, ctx, env),
         term = build.(body_term),
         :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
      {:ok, term}
    end
  end

  # A `match` in nested expression position, in checking mode: the expected type
  # IS the result type its motive needs, so hand it straight to `elaborate_match`
  # (which builds the motive, refines indices per branch, and enforces coverage),
  # then let the kernel re-check the assembled `:case` — mirroring `:rewrite_expr`
  # above. Reached from `rewrite … in match …` (line ~151) and from nested arm
  # bodies (`elaborate_branch_body`). `let`-blocks are now handled in checking
  # mode (the `{:block, …}` clause below); inference-position inline match (no
  # expected type) stays unimplemented (a separate aux-function lift).
  def elaborate_expr_checked({:pattern_match, meta, [scrut | arms]}, expected_core, names, ctx, env)
      when is_list(meta) do
    if special_match_arms?(arms) do
      with {:ok, desugared} <- desugar_special_match(scrut, arms, Keyword.get(meta, :line, 0)) do
        elaborate_expr_checked(desugared, expected_core, names, ctx, env)
      end
    else
      case elaborate_match(scrut, arms, expected_core, names, ctx, env) do
        {:ok, term} ->
          with :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
            {:ok, term}
          end

        {:error, _reason} = error ->
          error
      end
    end
  end

  # A `with <expr>` in checking-mode expression position — a nested with-clause
  # appearing as another with/match arm body. Mirrors the top-level with-body
  # (`declarations.ex` `elaborate_body`): `expected_core` is this position's
  # (already-refined) goal, so each nested level refines on top of the enclosing
  # branch's goal and with-abstractions compose. No original params are threaded
  # (LHS re-match is a top-level-only form), so `original_params` is empty.
  def elaborate_expr_checked({:with_abs, meta, [scrut | arms]}, expected_core, names, ctx, env) do
    proof = Keyword.get(meta, :proof)
    elaborate_with(scrut, arms, proof, expected_core, names, ctx, env, [])
  end

  # A semantic macro failure is a typed `Std.Syntax.Failure` value. The
  # computed-macro expansion pass recognizes this constructor after
  # normalization and turns it into the author-facing Diagnosis error.
  def elaborate_expr_checked({:macro_fail, meta, args}, expected_core, names, ctx, env) do
    with {:ok, term} <- elaborate_macro_failure(meta, args, names, ctx, env),
         :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
      {:ok, term}
    end
  end

  # A `let x = e ⏎ body` block, in checking mode. There is no `:let` in Core, so
  # each binding is eliminated by *surface substitution* (`elaborate_let_block`):
  # every free `x` in the remaining statements is replaced by the rhs expression
  # `e`, then the substituted body is checked against the expected type. NOTE:
  # this INLINES `e` at each use (it does not build a `(λ x:T. body) e` redex), so
  # it does not bind-once — a caller wanting to avoid duplicating/re-evaluating a
  # complex `e` (e.g. a guarded match's scrutinee) cannot get that by routing
  # through here; it would need a real Core binder built directly. A rebinding of
  # `x` in a later statement is refused (would capture).
  def elaborate_expr_checked({:block, _meta, stmts}, expected_core, names, ctx, env) do
    elaborate_let_block(stmts, expected_core, names, ctx, env)
  end

  # `return e` in a checking position (e.g. an `if`/`match` branch tail): the
  # identity on `e`, checked against the expected type. See the inference clause.
  def elaborate_expr_checked({:early_return, _meta, [e]}, expected_core, names, ctx, env),
    do: elaborate_expr_checked(e, expected_core, names, ctx, env)

  # Dependent-pair introduction `%[a, b]` in checking mode. The expected type must
  # be the builtin inductive Sigma; elaborate `a` against its domain, then `b`
  # against the codomain APPLIED to `a` (the second Σ param `b_fn` is an arbitrary
  # term — lambda, global, or neutral — so the instantiated codomain is the
  # application `b_fn(a)` handed to the normalizer, NOT a binder-body substitution;
  # spec §2.2). Lowers to the ctor `mk_pair`; the kernel re-checks it. With no Sigma
  # family registered (a raw-`Env.empty()` elaboration), falls through to the
  # inference fallback, which builds the same `{:ctor, :mk_pair, …}`.
  # A tuple literal `%[e1, …, en]` (n ≥ 2) checked against a Σ-shaped goal. ONE
  # recursion (`check_tuple_against/5`) elaborates both the bare dependent pair
  # (`Sigma(x:T, U)` — the last element is the whole second component) AND the
  # unit-terminated telescope (`Tuple(T1,…,Tn)` = `Sigma(T1, … Sigma(Tn, Unit))` —
  # each element gets its own `mk_pair` cell, bottoming at `unit`). Which one is
  # produced is driven ENTIRELY by the goal's structure: whether a Σ layer's tail
  # bottoms at `Unit` (telescope) or at an ordinary type (bare). A non-Σ goal falls
  # through to the fallback exactly as the former arity-2 clause did.
  def elaborate_expr_checked({:tuple, _meta, elems} = expr, expected_core, names, ctx, env)
      when is_list(elems) and length(elems) >= 2 do
    sigma_fam = Inductive.builtin(env, :sigma)

    case Kernel.normalize(ctx, expected_core) do
      {:data, fam, [_dom, _b_fn], []} when fam == sigma_fam and not is_nil(sigma_fam) ->
        with {:ok, term} <- check_tuple_against(elems, expected_core, names, ctx, env),
             :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
          {:ok, term}
        end

      _ ->
        elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)
    end
  end

  # Lambda in checking mode: the expected type supplies the parameter types the
  # surface leaves untyped. `fn(a, b) -> body` against `Π a. Π b. C` curries to
  # `λa. λb. body` — each parameter is bound at the corresponding domain and the
  # body checked against the final codomain. A lambda needs a known Π (Idris
  # likewise only *checks*, never *infers*, an unannotated lambda); one in an
  # inference position (e.g. a bare higher-order argument) still needs the
  # expected type routed to it, which is a separate bidirectional-application step.
  def elaborate_expr_checked({:lambda, meta, [body_expr]}, expected_core, names, ctx, env) do
    with {:ok, term} <-
           elaborate_lambda(Keyword.fetch!(meta, :params), body_expr, expected_core, names, ctx, env),
         :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
      {:ok, term}
    end
  end

  # `if c then t else e` checked against the expected type: both branches are
  # checked at `expected_core` under a constant motive `λ_:Bool. expected_core`
  # (shifted past the fresh Bool binder). The kernel re-checks the assembled
  # `:case`, so nothing here is trusted.
  def elaborate_expr_checked({:conditional, _meta, [c, t, e]}, expected_core, names, ctx, env) do
    branch = fn expr ->
      if effect_goal?(expected_core, ctx),
        do: elaborate_effect_branch(expr, expected_core, names, ctx, env),
        else: elaborate_expr_checked(expr, expected_core, names, ctx, env)
    end

    with {:ok, c_core} <- elaborate_expr_checked(c, bool_type_term(Context.signature(ctx)), names, ctx, env),
         {:ok, t_core} <- branch.(t),
         {:ok, e_core} <- branch.(e) do
      {:ok, bool_case(c_core, expected_core, t_core, e_core, ctx)}
    end
  end

  # `pickup` in checked position: desugar to the nested conditional and check
  # it against the expected type (each branch body is checked at `expected_core`).
  def elaborate_expr_checked({:pickup, _meta, clauses}, expected_core, names, ctx, env) do
    with {:ok, desugared} <- desugar_pickup(clauses) do
      elaborate_expr_checked(desugared, expected_core, names, ctx, env)
    end
  end

  # Wave-2 List sugar in checked position: desugar to Nil/Cons and re-check
  # against the same expected type.
  def elaborate_expr_checked({:list, _, _} = node, expected_core, names, ctx, env),
    do: elaborate_expr_checked(desugar_list(node), expected_core, names, ctx, env)

  # Map literal in checked position: desugar to the `put`/`new` chain and re-check
  # against the expected type. This is what lets an empty `%{}` (a bare `new()`
  # with nothing to pin its key/value metavariables in synthesis) solve them from
  # an expected `Map(k, v)`.
  def elaborate_expr_checked({:map, meta, pairs}, expected_core, names, ctx, env),
    do:
      elaborate_expr_checked(
        desugar_map(pairs, Keyword.get(meta, :line, 0)),
        expected_core,
        names,
        ctx,
        env
      )

  def elaborate_expr_checked({:string_interpolation, meta, segments}, expected_core, names, ctx, env),
    do:
      elaborate_expr_checked(
        desugar_interpolation(segments, Keyword.get(meta, :line, 0)),
        expected_core,
        names,
        ctx,
        env
      )

  # Type-directed compact-Nat literal: a non-negative integer literal checked
  # against the `Nat` family lowers to a compact `{:nat_lit, n}` — the surface
  # payoff of the compact-Nat kernel path, so a numeric literal at `Nat` (and
  # hence a `Bounded`/`Char` index) is one machine integer, not an `S`-tower. A
  # bare literal still defaults to `Int` in inference mode; only a `Nat`-checked
  # one becomes compact. Every other case defers to the ordinary checked path.
  def elaborate_expr_checked({:literal, meta, value} = expr, expected_core, names, ctx, env) do
    int? = Keyword.get(meta, :subtype) == :integer and is_integer(value) and value >= 0
    string? = Keyword.get(meta, :subtype) == :string and is_binary(value)
    bytes? = Keyword.get(meta, :subtype) == :bytes and is_list(value)
    union_ctor = union_literal_ctor(meta, value, expected_core, ctx, env)

    cond do
      # A literal checked against a union that has that literal as a MEMBER is the
      # member's NULLARY constructor: the value is fully determined by the ctor, so
      # there is nothing to store.
      #
      # This must precede the `string?` branch — otherwise a `"north"` member would
      # be desugared to its List(Char) spine and never reach the injection.
      union_ctor != nil ->
        {:ok, {:ctor, union_ctor, []}}

      # A string literal checks as its `List(Char)` desugaring (see the typed
      # clause), so the expected `List(Char)`/`String` type drives each char.
      string? ->
        elaborate_expr_checked(desugar_string(value, meta), expected_core, names, ctx, env)

      # A byte binary literal checks as its `Std.Binary.of_bytes/1` desugaring.
      bytes? ->
        with {:ok, surface} <- desugar_bytes(value, Keyword.get(meta, :line, 0)) do
          elaborate_expr_checked(surface, expected_core, names, ctx, env)
        end

      int? and nat_expected?(expected_core, ctx) ->
        {:ok, {:nat_lit, value}}

      # Type-directed compact-Bounded literal: an integer literal checked against a
      # `Bounded(n)` type (e.g. `Char = Bounded(0x110000)`) is the value `k` itself,
      # a single compact node, iff `0 <= k < n`. This is the surface `let c: Char =
      # 97` — a codepoint is ONE integer, never a `Next(...First)` tower. The kernel
      # independently re-checks the bound (`check/3`), so this early check is only for
      # a clear error message.
      int? ->
        case bounded_expected(expected_core, ctx) do
          {:ok, n} when value < n -> {:ok, {:bounded_lit, value}}
          {:ok, n} -> {:error, {:bounded_lit_out_of_range, value, n}}
          :no -> elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)
        end

      true ->
        elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)
    end
  end

  # A proof-position hole: attempt auto-resolution. `expected_core` is the Core
  # goal at this slot. Soundness: ProofSearch only builds a term; the kernel
  # re-checks it. On `:none` (no candidate discharges the goal) the hole SURVIVES
  # as a first-class `{:hole, id}` — since holes are stuck neutrals (first-class
  # holes, Slice 1), the enclosing application evals to a stuck spine and
  # type-checks (the kernel accepts a hole at any goal), so the declined proof
  # becomes an inspectable hole that blocks codegen, exactly like a body-level
  # hole (declarations.ex hole clause), rather than a hard elaboration error.
  # The id is minted by the shared `Declarations.hole_id/2` scheme.
  def elaborate_expr_checked({:hole, meta, _}, expected_core, _names, ctx, env) do
    case Cure.Elab.ProofSearch.resolve(expected_core, ctx, env) do
      {:ok, term} -> {:ok, term}
      :none -> {:ok, {:hole, Cure.Elab.Declarations.hole_id(env, meta)}}
      {:error, _} = err -> err
    end
  end

  def elaborate_expr_checked(expr, expected_core, names, ctx, env),
    do: elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)

  # The saturated (or non-function-goal) checking-mode path for a non-constructor
  # call: try the goal-first pre-pass when the goal can inform implicit solving,
  # otherwise infer-then-recheck. Split out of the `true ->` branch of
  # `elaborate_expr_checked({:function_call,...})` so the eta-expansion path can
  # share `resolved` without duplicating this block. Defined here (after the
  # `elaborate_expr_checked/5` clause group) so those clauses stay grouped.
  defp elaborate_checked_call_saturated(expr, resolved, expected_core, args, names, ctx, env) do
    concrete_goal? = not Unify.has_meta?(expected_core)

    goal_first? =
      (concrete_goal? and implicit_def?(env, resolved)) or
        (concrete_goal? and Enum.any?(args, &call_placeholder?/1) and Map.has_key?(env.defs, resolved)) or
        (Enum.any?(args, &match?({:lambda, _m, _b}, &1)) and Map.has_key?(env.defs, resolved))

    goal_first =
      if goal_first? do
        case elaborate_global_app_expected(env, resolved, args, names, ctx, expected_core) do
          {:ok, term, _type} ->
            case Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
              :ok -> {:ok, term}
              {:error, _} -> nil
            end

          {:error, _} ->
            nil
        end
      end

    # No post-hoc retry. There used to be one here, firing on
    # `:unsolved_metavariables` under the guard `implicit_def?(resolved) and not
    # has_meta?(expected_core)` — which is EXACTLY the first disjunct of
    # `goal_first?` above. Whenever it fired, the identical
    # `elaborate_global_app_expected` had therefore already run and failed, so it
    # could only fail again. It was dead the moment the goal-first pre-pass was
    # introduced, and stayed in the file because each new attempt was bolted on in
    # front of the previous one instead of replacing it. Solving happens once, up
    # front, where the goal is known.
    goal_first || elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env)
  end

  # Recursively elaborate a run of surface tuple elements against a Σ-shaped goal,
  # peeling ONE Σ layer per element. Distinguishes two terminations:
  #
  #   * telescope terminator — the current Σ's tail bottoms at `Unit`
  #     (`telescope_terminator?/3`): the element inhabits the Σ's *domain* and a
  #     trailing `unit` closes the spine, so `%[…,e]` against `Sigma(D, λ_.Unit)`
  #     becomes `mk_pair(check(e,D), unit)`. This is how `Tuple(T1,…,Tn)` builds a
  #     flat, unit-terminated HList that emit later flattens to a BEAM tuple.
  #
  #   * bare dependent pair — the tail is an ordinary type: the LAST element is the
  #     whole second component, so `%[a,b]` against `Sigma(D, Cod)` checks `b` at
  #     `Cod[a]` directly (no `unit`). Preserves the landed `Sigma(x:T,U)` ABI.
  #
  # An empty run against `Unit` yields `unit` (the telescope terminator itself).
  defp check_tuple_against([], expected_core, _names, ctx, env) do
    unit_family = unit_family_name(env)

    case Kernel.normalize(ctx, expected_core) do
      {:data, ^unit_family, [], []} -> {:ok, {:ctor, unit_ctor_name(env), []}}
      other -> {:error, {:tuple_arity_mismatch, :expected_more, other}}
    end
  end

  defp check_tuple_against([e | rest], expected_core, names, ctx, env) do
    sigma_fam = Inductive.builtin(env, :sigma)

    case Kernel.normalize(ctx, expected_core) do
      {:data, fam, [dom, b_fn], []} when fam == sigma_fam and not is_nil(sigma_fam) ->
        if rest == [] and not telescope_terminator?(b_fn, ctx, env) do
          # Last element, tail is an ordinary type → e IS the whole second
          # component (a bare pair, possibly itself a nested tuple).
          elaborate_expr_checked(e, expected_core, names, ctx, env)
        else
          [%{name: mk_pair} | _] = Inductive.ctors_of(env, sigma_fam)

          with {:ok, e_term} <- elaborate_expr_checked(e, dom, names, ctx, env),
               cod_inst = Kernel.normalize(ctx, {:app, b_fn, e_term}),
               {:ok, rest_term} <- check_tuple_against(rest, cod_inst, names, ctx, env) do
            {:ok, {:ctor, mk_pair, [e_term, rest_term]}}
          end
        end

      other ->
        # Goal is not a Σ: only a single remaining element can inhabit it directly
        # (the bare final component of a 2-tuple). More than one is an arity error.
        if rest == [] do
          elaborate_expr_checked(e, expected_core, names, ctx, env)
        else
          {:error, {:tuple_arity_mismatch, :too_many, other}}
        end
    end
  end

  # Does this Σ's second parameter (a `λ`) bottom at `Unit`? Applying it to a
  # closed probe term and normalizing β-reduces a non-dependent tail to its body;
  # a dependent tail that mentions its argument won't reduce to `Unit` anyway. This
  # is the sole signal separating a telescope layer from a bare dependent pair.
  defp telescope_terminator?(b_fn, ctx, env) do
    unit_family = unit_family_name(env)

    case Kernel.normalize(ctx, {:app, b_fn, {:ctor, unit_ctor_name(env), []}}) do
      {:data, ^unit_family, [], []} -> true
      _ -> false
    end
  end

  # True iff the (meta-free) expected type evaluates to the canonical `Nat` family.
  defp nat_expected?(expected_core, ctx) do
    sig = Context.signature(ctx)
    nat_fid = Cure.Core.Inductive.builtin(sig, :nat)

    not is_nil(nat_fid) and not Unify.has_meta?(expected_core) and
      match?({:vdata, ^nat_fid, []}, Eval.eval(expected_core, Context.env(ctx)))
  end

  # `{:ok, n}` iff the expected type δ-unfolds to the `Bounded` family with a
  # concrete bound `n` (a full `Bounded(n)` with `n` a closed Nat) — `:no`
  # otherwise (metavariable, non-Bounded, or symbolic bound). Sees through a
  # `typealias` (e.g. `Char`) because `whnf_value` δ-unfolds the certified alias.
  defp bounded_expected(expected_core, ctx) do
    sig = Context.signature(ctx)
    bounded_fid = Inductive.builtin(sig, :bounded)

    if is_nil(bounded_fid) or Unify.has_meta?(expected_core) do
      :no
    else
      value = Normalise.whnf_value(Eval.eval(expected_core, Context.env(ctx)), sig)

      case value do
        {:vdata, ^bounded_fid, [bound_val]} ->
          case bound_to_int(Normalise.whnf_value(bound_val, sig)) do
            {:ok, n} -> {:ok, n}
            :error -> :no
          end

        _ ->
          :no
      end
    end
  end

  # Peel a concrete Nat bound value (compact `{:vnat, _}` or `Z`/`S` tower) to an
  # integer; `:error` for a symbolic/neutral bound.
  defp bound_to_int({:vnat, n}) when is_integer(n) and n >= 0, do: {:ok, n}
  defp bound_to_int({:vctor, :Z, []}), do: {:ok, 0}

  defp bound_to_int({:vctor, :S, [pred]}) do
    case bound_to_int(pred) do
      {:ok, n} -> {:ok, n + 1}
      :error -> :error
    end
  end

  defp bound_to_int(_other), do: :error

  # The type of every character literal: Char = Bounded(0x110000). A char literal
  # is a codepoint value; the bound 0x110000 (= 1_114_112) is intrinsic, not from
  # context. `:no_bounded` when the Bounded family is unregistered (needs
  # `use Std.Bounded`), so the caller reports a fix-naming error, not a crash.
  defp char_type_value(sig) do
    case Inductive.builtin(sig, :bounded) do
      nil -> :no_bounded
      fid -> {:ok, {:vdata, fid, [{:vnat, 0x110000}]}}
    end
  end

  defp elaborate_lambda([], body_expr, expected_core, names, ctx, env),
    do: elaborate_expr_checked(body_expr, expected_core, names, ctx, env)

  defp elaborate_lambda([{:param, _pm, pname} | rest], body_expr, expected_core, names, ctx, env) do
    case Kernel.normalize(ctx, expected_core) do
      {:pi, _g, dom_term, cod_term} ->
        dom_value = Eval.eval(dom_term, Context.env(ctx))
        ctx1 = Context.extend(ctx, dom_value)

        with {:ok, body_term} <-
               elaborate_lambda(rest, body_expr, cod_term, [pname | names], ctx1, env) do
          {:ok, {:lam, Cure.Core.Grade.unrestricted(), dom_term, body_term}}
        end

      _ ->
        {:error, {:lambda_expected_pi, expected_core}}
    end
  end

  defp elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env) do
    # An unsolved metavariable in the expected type (e.g. a higher-order implicit
    # `{P : Nat -> Type}` that first-order unification could not solve) must not be
    # handed to the trusted `Eval.eval` — it has no `{:meta, _}` clause and would
    # crash the kernel. Reject cleanly instead; higher-order pattern unification
    # (ledger #10) is what would let it be solved rather than rejected.
    if Unify.has_meta?(expected_core) do
      {:error, {:unsolved_metavariable_in_type, expected_core}}
    else
      case try_discharge_refinement(expr, expected_core, names, ctx, env) do
        {:ok, term} ->
          {:ok, term}

        :no ->
          with {:ok, term, type} <- elaborate_expr_typed(expr, names, ctx, env) do
            term = maybe_inject_union(term, type, expected_core, ctx, env)
            term = maybe_coerce_refined_to_base(term, type, expected_core, ctx, env)

            with :ok <- Kernel.check(ctx, term, Eval.eval(expected_core, Context.env(ctx))) do
              {:ok, term}
            end
          end
      end
    end
  end

  # A checking-mode constructor whose direct check against the expected type failed
  # may still inhabit the BASE of a refinement `{x: T | φ}` = `Sigma(T, λx. φ)` —
  # e.g. `S(k)` at `-> {n: Nat | IsPositive(n)}`, where `S` is a `Nat` (not `Sigma`)
  # constructor, so the direct check reports `:foreign_ctor`. When the expected type
  # is such a refinement, route to the refinement-discharge fallback, which checks
  # the constructor against the base domain `T` and searches for a proof of the
  # obligation `φ[x := S(k)]`. Additive: reached only after the direct constructor
  # check already failed, and the original error is surfaced when the expected type
  # is not a dischargeable refinement or no proof is found — so every
  # currently-accepted or -rejected constructor body is unchanged.
  defp ctor_refinement_fallback(expr, expected_core, names, ctx, env, orig_err) do
    if refinement_return?(expected_core, ctx, env) do
      case elaborate_expr_checked_fallback(expr, expected_core, names, ctx, env) do
        {:ok, _} = ok -> ok
        _ -> orig_err
      end
    else
      orig_err
    end
  end

  # Auto-discharge a CLOSED refinement obligation (§3a level 2). When a value is
  # checked against a refinement type `{x: T | φ}` — the dependent pair
  # `Sigma(T, λx. φ)` — and `φ[x := value]` reduces to an inhabited reflection
  # proposition (`IsTrue(True())`), fill the proof slot with that proposition's
  # nullary constructor (`Confirmed()`) and build the pair. The author writes just
  # the value; no `refine`, no explicit proof.
  #
  # Soundness: the elaborator only PROPOSES `mk_pair(value, proof)`; the proof it
  # supplies is itself kernel-checked against the obligation before use (by
  # `reflection_proof` via `Kernel.check`, or — for an open obligation — by every
  # candidate `ProofSearch.resolve` returns), and `value` is checked against the
  # base component at elaboration. The Σ-intro rule then makes the pair well-typed
  # by construction; the elaborator never trusts its own reduction. A CLOSED
  # obligation with no inhabiting nullary constructor (`IsTrue(False())`), or an
  # OPEN one with no derivable proof, yields `nil`, so this returns `:no` and the
  # value falls through to ordinary checking — the proof is required, never
  # invented.
  defp try_discharge_refinement(expr, expected_core, names, ctx, env) do
    sigma_fam = Inductive.builtin(env, :sigma)

    with false <- is_nil(sigma_fam),
         {:data, ^sigma_fam, [dom, cod], []} <- Kernel.normalize(ctx, expected_core),
         # Exclude a flat tuple / bare nested-pair Σ (`Tuple(T1,…,Tn)` lowers to a
         # unit-terminated Σ telescope that shares this shape). Its instantiated
         # second component is itself a Σ, which `ProofSearch` would happily "prove"
         # by fabricating a pair — silently accepting a program that has no
         # refinement obligation at all (and mis-elaborating its value). Only a
         # genuine refinement `{x: T | φ}`, whose predicate is a proposition, may
         # reach discharge.
         false <- tuple_telescope_type?(expected_core, sigma_fam, ctx, env),
         {:ok, value} <- elaborate_expr_checked(expr, dom, names, ctx, env),
         {:data, _fam_key, _p, _i} = obligation <- Kernel.normalize(ctx, {:app, cod, value}),
         proof when not is_nil(proof) <- discharge_obligation(obligation, ctx, env) do
      {:ok, {:ctor, sigma_ctor_name(env), [value, proof]}}
    else
      _ -> :no
    end
  end

  # Find a proof of a refinement obligation, or nil. A CLOSED obligation
  # (`IsTrue(True())`) is discharged by its family's nullary constructor via
  # `reflection_proof`. An OPEN obligation — one whose truth rests on a free
  # binder, e.g. `IsTrue(int_gt(x, 0))` for a parameter `x` — has no nullary
  # inhabitant, so it falls through to the auto-lemma proof search, which derives
  # the proof from in-scope hypotheses (a matching `evidence : IsTrue(x > 0)`
  # binder), `@lemma`-tagged theorems, or the sign-directed positivity procedure.
  # Every term `ProofSearch` returns is kernel-checked against this obligation
  # inside the search, so an open obligation is discharged only when a genuine
  # proof exists; an unprovable one returns `:none` here (→ nil → `:no` upstream)
  # and the value is rejected exactly as before.
  defp discharge_obligation(obligation, ctx, env) do
    case reflection_proof(obligation, ctx, env) do
      nil ->
        case Cure.Elab.ProofSearch.resolve(obligation, ctx, env) do
          {:ok, proof} -> proof
          _ -> nil
        end

      proof ->
        proof
    end
  end

  # The nullary constructor of the obligation's reflection family that the kernel
  # accepts as a proof of the (already-reduced) obligation, or nil if none does.
  # Trying each nullary constructor and letting `Kernel.check` decide keeps this
  # general over any `So`-style reflection type and never trusts the elaborator's
  # own view of inhabitation.
  defp reflection_proof({:data, fam_key, _p, _i} = obligation, ctx, env) do
    obligation_value = Eval.eval(obligation, Context.env(ctx))

    Inductive.ctors_of(env, fam_key)
    |> Enum.filter(fn ctor -> ctor.args == [] end)
    |> Enum.find_value(fn ctor ->
      candidate = {:ctor, ctor.name, []}

      case Kernel.check(ctx, candidate, obligation_value) do
        :ok -> candidate
        _ -> nil
      end
    end)
  end

  # If `term`'s inferred `type` WHNFs to the Sigma refinement family and the
  # expected base type is convertible to the Sigma's first-component type, coerce
  # by inserting the first projection (`sigma_first`, or `Std.Refine.refined_value`
  # when that idiomatic accessor is in scope) — the reverse of the base->refined
  # injection. This is the ONLY new behavior; if the shapes don't match, return
  # `term` unchanged so ordinary checking (and its error) stands.
  #
  # `type` is a semantic VALUE here (not a Core term — see the call site), so it is
  # inspected with `Normalise.whnf_value/2` (mirror `sigma_params/3` in
  # proof_search.ex), never `Kernel.normalize/2` (which expects a Core term and
  # matches `:data`, not `:vdata`). The inserted projection is independently
  # re-verified by the fallback's `Kernel.check`, so a wrong coercion is caught.
  defp maybe_coerce_refined_to_base(term, type, expected_core, ctx, env) do
    sigma_fam = Inductive.builtin(env, :sigma)
    depth = Context.length(ctx)
    sig = Context.signature(ctx)

    with false <- is_nil(sigma_fam),
         {:vdata, ^sigma_fam, [dom_value, predicate_value]} <- Normalise.whnf_value(type, sig),
         # Do not coerce when the expected type is itself that Sigma (no coercion
         # needed) — only when expected is the base component type.
         false <- sigma_typed?(expected_core, sigma_fam, ctx),
         dom_term <- Quote.reify(dom_value, depth, sig),
         true <- convertible?(dom_term, expected_core, ctx, env) do
      predicate_term = Quote.reify(predicate_value, depth, sig)
      build_app({:global, first_projection_head(env)}, [dom_term, predicate_term, term])
    else
      _ -> term
    end
  end

  # The global to head the first projection with: `Std.Refine.refined_value` when
  # the refinement API is in scope (the idiomatic accessor a human writes,
  # mirroring `refinement_proof`), else the kernel builtin `sigma_first`. Mirror
  # `second_projection_head/1` in `proof_search.ex`: nil-check via `Env.get_def`
  # FIRST, because `Env.resolve_key/3` falls back to the bare input atom (never
  # nil) and would otherwise hand back a nonexistent global.
  defp first_projection_head(env) do
    case Env.get_def(env, "refined_value") do
      nil -> :sigma_first
      _def -> Env.resolve_key(env, env.defs, "refined_value")
    end
  end

  # True when the expected Core type normalises to the Sigma family itself (so no
  # coercion is needed — the refined value is already at the expected type).
  defp sigma_typed?(expected_core, sigma_fam, ctx) do
    match?({:data, ^sigma_fam, _, []}, Kernel.normalize(ctx, expected_core))
  end

  # Up-to-conversion equality of two Core types, mirroring proof_search.ex:317.
  # `Conv.conv?/5` takes Core terms and evaluates them itself.
  defp convertible?(a_term, b_term, ctx, env) do
    Conv.conv?(a_term, b_term, Context.env(ctx), Context.length(ctx), env)
  end

  defp build_app(head, args), do: Enum.reduce(args, head, fn a, f -> {:app, f, a} end)

  # The nullary constructor for a LITERAL member of the expected union, or nil if the
  # expected type is not a union or the literal is not one of its members.
  #
  # The key comes from `Union.literal_key/2` — the same single source of truth the
  # canonicaliser uses when it builds the family. Duplicating the key format here
  # instead would let the two drift and silently produce a ctor name that does not
  # exist, turning the injection into a no-op conversion failure.
  defp union_literal_ctor(meta, value, expected_core, ctx, env) do
    with {:data, ukey, [], []} <- Kernel.normalize(ctx, expected_core),
         true <- Cure.Elab.Union.union_family?(ukey),
         {:ok, key} <- Cure.Elab.Union.literal_key(Keyword.get(meta, :subtype), value),
         cname <- Cure.Elab.Union.ctor_key(ukey, %{key: key}),
         true <- Inductive.get_ctor(env, cname) != nil do
      cname
    else
      _ -> nil
    end
  end

  @doc """
  Coerce an already-inferred term into an expected anonymous-union type.

  A STRICT no-op unless `expected_core` normalises to a generated union family, so it
  is safe to apply anywhere a term has been inferred but the expected type is known.
  `Declarations.elaborate_body/6`'s catch-all needs it: that clause elaborates in
  INFER mode and discards the declared return type, so a body like `fn f(n: Int) ->
  Int | Bool = n` never reaches check-position and would never be injected.
  """
  @spec coerce_union(term(), Cure.Core.Value.t(), term(), Context.t(), Env.t()) :: term()
  def coerce_union(term, type, expected_core, ctx, env),
    do: maybe_inject_union(term, type, expected_core, ctx, env)

  @doc """
  Coerce an already-inferred refinement value to its base type.

  A STRICT no-op unless the inferred `type` WHNFs to the Sigma refinement family and
  `expected_core` is convertible to the Sigma's first-component type, so it is safe to
  apply anywhere a term has been inferred but the expected base type is known.
  `Declarations.elaborate_body/6`'s catch-all needs it for the same reason it needs
  `coerce_union/5`: that clause elaborates in INFER mode, so a body like
  `fn underlying(p: PositiveNatural) -> Nat = p` never reaches the check-mode fallback.
  """
  @spec coerce_refined_to_base(term(), Cure.Core.Value.t(), term(), Context.t(), Env.t()) ::
          term()
  def coerce_refined_to_base(term, type, expected_core, ctx, env),
    do: maybe_coerce_refined_to_base(term, type, expected_core, ctx, env)

  @doc """
  True when the declared return type is the refinement / dependent-pair Sigma
  family.

  `Declarations.elaborate_body/6`'s catch-all uses it to route such returns
  through CHECK mode, so an OPEN refinement obligation (`{n: T | φ}` whose truth
  depends on a binder) reaches `try_discharge_refinement` and can be discharged by
  proof search — mirroring how `union_goal?/1` routes union returns through check
  mode. A metavariable-bearing return type is excluded (it must not be handed to
  the kernel's `Kernel.normalize`), matching `elaborate_expr_checked_fallback/5`'s
  own guard; such a body keeps the historical infer path.
  """
  @spec refinement_return?(term(), Context.t(), Env.t()) :: boolean()
  def refinement_return?(expected_core, ctx, env) do
    sigma_fam = Inductive.builtin(env, :sigma)

    not is_nil(sigma_fam) and not Unify.has_meta?(expected_core) and
      sigma_typed?(expected_core, sigma_fam, ctx) and
      not tuple_telescope_type?(expected_core, sigma_fam, ctx, env)
  end

  @doc """
  True when an *inferred* body already sits at the refinement / dependent-pair
  Sigma family — i.e. it is a complete refinement value (`refine(v, pf)`) rather
  than a bare base value that still owes a refinement obligation.

  `Declarations.elaborate_refinement_return_body/6` uses it to decide whether a
  body at a refinement return needs the goal threaded in (a base value like
  `multiply(a, b)` at `{n | IsPositive(n)}`, whose obligation must reach
  `try_discharge_refinement`) or is already complete and must be kept verbatim (so
  its projection accessors are not re-derived by a redundant checked pass).

  `type` is a semantic VALUE (the third element of `elaborate_expr_typed/4`, see
  `coerce_refined_to_base/5`), so it is inspected with `Normalise.whnf_value/2` —
  never `Kernel.normalize/2`, which expects a Core term and would crash on a value.
  """
  @spec inferred_refinement_value?(Cure.Core.Value.t(), Context.t(), Env.t()) :: boolean()
  def inferred_refinement_value?(type, ctx, env) do
    sigma_fam = Inductive.builtin(env, :sigma)
    sig = Context.signature(ctx)

    not is_nil(sigma_fam) and
      match?({:vdata, ^sigma_fam, [_dom, _pred]}, Normalise.whnf_value(type, sig))
  end

  # A refinement / bare dependent-pair Σ and a flat tuple Σ share ONE Core shape
  # (`{:data, Sigma, [dom, λ], []}`) — the unified-tuple encoding lowers
  # `Tuple(T1,…,Tn)` to the unit-terminated telescope
  # `Sigma(T1, λ_. … Sigma(Tn, λ_. Unit))`. Only the SPINE TERMINATOR separates
  # them: a tuple bottoms at `Unit`, a refinement's predicate is a proposition.
  # Routing a tuple return through the refinement check-first path changes how its
  # body elaborates (a still-well-typed but different Core term, e.g. an off-by-one
  # in a nested optic rebuild), so tuples MUST be excluded here.
  #
  # This is the transitive closure of `telescope_terminator?/3`'s probe technique:
  # apply each Σ's predicate to a closed `unit` probe, normalize (β-reducing a
  # non-dependent tail to its body), and recurse on the tail. A car list that ends
  # in `Unit` is a tuple; anything else (a proposition, or a bare pair whose tail is
  # an ordinary type) is not. Mirrors emit's value-level `telescope_cars/2`.
  defp tuple_telescope_type?(expected_core, sigma_fam, ctx, env) do
    unit_family = unit_family_name(env)

    case Kernel.normalize(ctx, expected_core) do
      {:data, ^unit_family, [], []} ->
        true

      {:data, ^sigma_fam, [_dom, b_fn], []} ->
        tail = {:app, b_fn, {:ctor, unit_ctor_name(env), []}}
        tuple_telescope_type?(tail, sigma_fam, ctx, env)

      _ ->
        false
    end
  end

  # Anonymous-union subsumption: a coercion inserted by the ELABORATOR in check mode
  # only — never a kernel rule. If the expected type is a generated union family and
  # the term's inferred type is one of its members, inject that member's constructor.
  #
  # Otherwise the term passes through untouched and the kernel rejects it with an
  # ordinary conversion failure. Note the injected `{:ctor, …}` is independently
  # re-verified by `Kernel.check/3`, so the elaborator stays untrusted: a wrong
  # injection is caught, not silently accepted.
  defp maybe_inject_union(term, type, expected_core, ctx, env) do
    with {:data, ukey, [], []} <- Kernel.normalize(ctx, expected_core),
         true <- Cure.Elab.Union.union_family?(ukey) do
      member_term = Quote.reify(type, Context.length(ctx), Context.signature(ctx))

      cond do
        # (a) The term's type is ITSELF a narrower union — widen it.
        match?({:data, _, [], []}, member_term) and
            Cure.Elab.Union.union_family?(elem(member_term, 1)) ->
          widen_union(term, elem(member_term, 1), ukey, expected_core, ctx, env)

        # (b) The term's type is a plain member — inject it.
        true ->
          cname =
            Cure.Elab.Union.ctor_key(ukey, %{key: Cure.Elab.Union.member_key(member_term)})

          if Inductive.get_ctor(env, cname), do: {:ctor, cname, [term]}, else: term
      end
    else
      _ -> term
    end
  end

  # Widen a narrower union into a wider one by remapping each of its constructors to
  # the counterpart with the same member key in the target family. This is a REAL
  # function — a Core `:case` — not a cast: the two families are genuinely distinct
  # types, so there is nothing to reinterpret.
  #
  # If any source member is absent from the target, the term is returned untouched
  # and the kernel rejects it with an ordinary conversion failure.
  defp widen_union(term, from_key, to_key, to_core, _ctx, env) do
    from_prefix = Atom.to_string(from_key) <> "$"

    branches =
      env
      |> Inductive.ctors_of(from_key)
      |> Enum.map(fn ctor ->
        suffix = ctor.name |> Atom.to_string() |> String.replace_prefix(from_prefix, "")
        target = String.to_atom(Atom.to_string(to_key) <> "$" <> suffix)

        cond do
          Inductive.get_ctor(env, target) == nil -> :missing
          ctor.args == [] -> {ctor.name, 0, {:ctor, target, []}}
          true -> {ctor.name, 1, {:ctor, target, [{:var, 0}]}}
        end
      end)

    if Enum.any?(branches, &(&1 == :missing)) do
      term
    else
      # The source family is parameterless and index-free, so its motive is a single
      # lambda over the scrutinee. `to_core` is a closed `{:data, key, [], []}`, so it
      # needs no weakening under that binder.
      motive =
        {:lam, Cure.Core.Grade.unrestricted(), {:data, from_key, [], []}, to_core}

      {:case, term, motive, branches}
    end
  end

  # Elaborate a saturated global call in checking mode, threading the expected
  # return type into the application so a return-type-only implicit can be solved.
  # Checking mode is goal-directed: solve hidden arguments from `expected` before
  # inferring explicit arguments, then retain eager inference as a compatibility
  # fallback. This ordering matters when eager inference can produce a complete but
  # wrong hidden family (for example the predicate of a refinement constructor).
  # The caller re-checks the assembled term against the goal in either path.
  defp elaborate_global_app_expected(env, atom, args, names, ctx, expected) do
    if Enum.any?(args, &call_placeholder?/1) do
      elaborate_implicit_app_bidirectional(env, atom, args, names, ctx, expected)
    else
      elaborate_global_app_expected_eager(env, atom, args, names, ctx, expected)
    end
  end

  defp elaborate_global_app_expected_eager(env, atom, args, names, ctx, expected) do
    case elaborate_implicit_app_bidirectional(env, atom, args, names, ctx, expected) do
      {:ok, _, _} = ok ->
        ok

      {:error, _} = goal_error ->
        case map_present_args(args, names, ctx, env) do
          {:ok, present} ->
            case elaborate_global_app(env, atom, present, ctx, expected) do
              {:ok, _, _} = ok -> ok
              {:error, _} -> goal_error
            end

          {:error, _} ->
            goal_error
        end
    end
  end

  defp call_placeholder?({:variable, _meta, "_"}), do: true
  defp call_placeholder?(_arg), do: false

  # A `rewrite` proof's type. The inductive identity type `Equivalent(a,x,y)` (spec
  # 2026-07-04) infers to `{:vdata, :Equivalent, [a, x, y]}` (1 param + 2 indices);
  # its `ty`/endpoints are that param and the two indices. The primitive `{:veq}`
  # form is still produced by the internal transport machinery (retired later), so
  # both are accepted.
  defp eq_parts({:vdata, family, [ty, a, b]}, sig) do
    if family == Inductive.builtin(sig, :eq), do: {:ok, ty, a, b}, else: {:error, :rewrite_proof_not_equality}
  end

  defp eq_parts(_other, _sig), do: {:error, :rewrite_proof_not_equality}

  # Build the inductive identity type `Equivalent(ty, a, b)` and its `reflexive(x)`
  # proof (spec 2026-07-04). The elaborator's transport/motive machinery constructs
  # these — not the retired primitive `{:eq}`/`{:refl}` — so that every
  # Equivalent/reflexive which can reach user code (a `with … proof pf` binder, a
  # returned equality) shares the single inductive representation user signatures
  # elaborate to. As of Phase B the `{:rewrite}` eliminator node has NO producers
  # left: every transport is the J/subst `transport_case` below (the kernel's
  # `{:rewrite}` rule and elab traversal clauses are stripped in Phase C).
  defp mk_eq(ty, a, b), do: {:data, :"Std.Equivalent#Equivalent", [ty], [a, b]}
  # Checking-position reflexive: fields-only spine; the expected type supplies the
  # parameter (M8.3 checking mode). (The inference-position params-on-spine form
  # `{:ctor, :reflexive, [ty, x]}` — K6 §E.1 — lost its last elaborator consumer
  # when bridge_step was deleted (B2); the kernel capability remains.)
  defp mk_refl(x), do: {:ctor, :"Std.Equivalent#reflexive", [x]}

  # Env-gated tracing for the rewrite-planning path (`CURE_REWRITE_LOG=1`). Off by
  # default so ordinary elaboration is untouched; used to diagnose non-termination
  # / mis-planning in the `rewrite_plan` occurrence matching.
  defp rwlog(fun) do
    if System.get_env("CURE_REWRITE_LOG"), do: IO.puts(:stderr, "[rw] " <> fun.())
    :ok
  end

  defp rw_ins(t), do: t |> inspect(limit: 14, printable_limit: 240) |> String.slice(0, 300)

  # Phase-B adopted encoding (spec "Phase-B encoding amendment", 2026-07-08): the
  # standard J/subst transport, exactly how Agda/Lean derive `subst`/`Eq.mpr`
  # from J. Given `proof : Equivalent(ty, l, r)` and a single-endpoint motive
  # `M = {:lam, Cure.Core.Grade.unrestricted(), ty, …}`, build
  #
  #     {:case, proof,
  #       λ(x:ty). λ(y:ty). λ(p : Equivalent(ty,x,y)). (M@x) -> (M@y),
  #       [reflexive(w) -> λ(h : M@l). h]}
  #
  # whose kernel-inferred type at the use site is `(M@l) -> (M@r)` (the kernel
  # applies the motive at the scrutinee's ACTUAL indices, kernel.ex
  # `infer {:case,…}`), while the reflexive branch is checked at the ctor's own
  # indices `[w,w]` with `w := l` bound by the index unifier, i.e. at
  # `(M@l) -> (M@l)` — which the identity inhabits. Applying the case to a body
  # elaborated OUTSIDE at `M@l` yields `M@r`: no de Bruijn body shift, and no
  # in-branch endpoint collapse (the in-branch re-elaboration route was
  # empirically disproven during B1 — `build_motive` abstracts BOTH endpoints,
  # demanding `l ≡ r` definitionally in-branch, false exactly when a rewrite is
  # needed).
  #
  # The identity branch's lam domain is annotated `M@l` (shifted into the
  # 1-binder branch frame), NOT `M@w`: `Kernel.check(lam, vpi)` converts the
  # annotation against the expected domain, and the branch's expected domain
  # after `specialize_branch_value` is `M@l`, not the fresh witness neutral.
  # Sound for every producer site here because each site's motive never
  # mentions the proof's second endpoint (it is abstracted away by
  # `motive_for`/`symmetry_proof`, or the motive is constant for the bridge),
  # so the branch substitution cannot touch anything the annotation's
  # evaluation sees.
  defp transport_case(proof, ty, motive, l) do
    # Motive binders outside-in: x (Equivalent's first index), y (second), then
    # the scrutinee p. Under x,y the scrutinee annotation's param shifts by 2;
    # under x,y,p the arrow domain sees x at de Bruijn 2; the (non-dependent)
    # codomain sits under one more binder, so y is also at de Bruijn 2 there.
    scrut_ty = {:data, :"Std.Equivalent#Equivalent", [Subst.shift(ty, 2, 0)], [{:var, 1}, {:var, 0}]}

    arrow =
      {:pi, Cure.Core.Grade.unrestricted(), {:app, Subst.shift(motive, 3, 0), {:var, 2}},
       {:app, Subst.shift(motive, 4, 0), {:var, 2}}}

    arrow_motive =
      {:lam, Cure.Core.Grade.unrestricted(), ty,
       {:lam, Cure.Core.Grade.unrestricted(), Subst.shift(ty, 1, 0),
        {:lam, Cure.Core.Grade.unrestricted(), scrut_ty, arrow}}}

    id_dom = {:app, Subst.shift(motive, 1, 0), Subst.shift(l, 1, 0)}

    {:case, proof, arrow_motive,
     [{:"Std.Equivalent#reflexive", 1, {:lam, Cure.Core.Grade.unrestricted(), id_dom, {:var, 0}}}]}
  end

  # Plan a `rewrite p in t` whose proof `p : Eq(ty, a, b)` transports along the
  # goal `expected`. Returns `{:ok, build, body_expected}`: `body_expected` is
  # the goal the surface body `t` must satisfy, and `build.(body_core)` assembles
  # the transport-`:case` application around the checked body. (A builder —
  # rather than a fixed `proof`/`motive` pair — lets the bridge case below nest
  # an outer transport around the original one.)
  #
  # The transport takes M[a] -> M[b]. Idris-style source `rewrite p in t`
  # checks `t` under the rewritten goal and returns the original goal, so when
  # the expected type contains the proof's left endpoint we synthesize symmetry.
  defp rewrite_plan(_ctx, proof, ty, a, b, expected) do
    rwlog(fn ->
      "plan a=#{rw_ins(a)} b=#{rw_ins(b)} | contains_a=#{contains_term?(expected, a)} " <>
        "contains_b=#{contains_term?(expected, b)} expected=#{rw_ins(expected)}"
    end)

    cond do
      contains_term?(expected, a) ->
        with {:ok, sym_proof} <- symmetry_proof(proof, ty, a, b),
             {:ok, motive} <- motive_for(expected, a, ty) do
          # sym_proof : Eq(ty, b, a), so the transport's left endpoint is `b`:
          # (M@b) -> (M@a) applied to the body checked at M@b = expected[a↦b].
          {:ok, fn body -> {:app, transport_case(sym_proof, ty, motive, b), body} end, replace_term(expected, a, b)}
        end

      # NOTE (B2): the former `find_bridge`/`bridge_step` cond arm — the
      # definitional-occurrence bridge built for rw07 (2ac4add) — was deleted as
      # dead code, not migrated. `expected` is always normalized before entry,
      # and since lazy δ-unfolding (ef3e958) + the nf idempotence fix, every
      # subterm of a normal form re-normalizes to itself, so the bridge's firing
      # condition (`normalize(s) != s` for a goal subterm `s`) is unsatisfiable.
      # Evidence (corpus trace + structural argument) recorded in
      # test/cure/elab/rewrite_as_case_test.exs, test (e).
      contains_term?(expected, b) ->
        {:ok, motive} = motive_for(expected, b, ty)
        # proof : Eq(ty, a, b): (M@a) -> (M@b) applied to the body checked at
        # M@a = expected[b↦a].
        {:ok, fn body -> {:app, transport_case(proof, ty, motive, a), body} end, replace_term(expected, b, a)}

      true ->
        {:error, {:rewrite_no_match, a, b, expected}}
    end
  end

  defp symmetry_proof(proof, ty, a, _b) do
    # M = λz. Eq(ty, z, a); proof : Eq(ty, a, b). The transport is
    # (M@a) -> (M@b) = Eq(ty,a,a) -> Eq(ty,b,a), applied to refl(a).
    motive_body = mk_eq(Subst.shift(ty, 1, 0), {:var, 0}, Subst.shift(a, 1, 0))
    motive = {:lam, Cure.Core.Grade.unrestricted(), ty, motive_body}
    {:ok, {:app, transport_case(proof, ty, motive, a), mk_refl(a)}}
  end

  defp motive_for(expected, target, ty),
    do: {:ok, {:lam, Cure.Core.Grade.unrestricted(), ty, abstract_term(expected, target, 0)}}

  defp contains_term?(term, target), do: term == target or Enum.any?(children(term), &contains_term?(&1, target))

  defp replace_term(term, target, replacement) when term == target, do: replacement

  defp replace_term(term, target, replacement) when is_list(term),
    do: Enum.map(term, &replace_term(&1, target, replacement))

  defp replace_term(term, target, replacement) do
    if term == target do
      replacement
    else
      rebuild(term, Enum.map(children(term), &replace_term(&1, target, replacement)))
    end
  end

  defp abstract_term(term, target, depth) when term == target, do: {:var, depth}
  defp abstract_term({:var, i}, _target, depth) when i >= depth, do: {:var, i + 1}
  defp abstract_term({:var, _} = var, _target, _depth), do: var

  defp abstract_term({:pi, _g, d, c}, target, depth),
    do: {:pi, Cure.Core.Grade.unrestricted(), abstract_term(d, target, depth), abstract_term(c, target, depth + 1)}

  defp abstract_term({:lam, _g, d, b}, target, depth),
    do: {:lam, Cure.Core.Grade.unrestricted(), abstract_term(d, target, depth), abstract_term(b, target, depth + 1)}

  # A `:case` branch `{ctor, arity, body}` binds `arity` de Bruijn variables in
  # `body` (see `Cure.Core.Term` shift/3's `:case` clause). Mirror that here:
  # abstract the scrutinee and motive at `depth`, but each branch body at
  # `depth + arity`, so branch-bound variables in `[depth, depth+arity)` are not
  # spuriously shifted by the `{:var, i} when i >= depth` clause. Without this,
  # the generic tuple clause below recurses into branch bodies at the wrong
  # depth and corrupts the motive (P0 Task 5, rewrite goals with a stuck `case`).
  defp abstract_term({:case, scrut, motive, branches}, target, depth) do
    {:case, abstract_term(scrut, target, depth), abstract_term(motive, target, depth),
     Enum.map(branches, fn {ctor, arity, body} ->
       {ctor, arity, abstract_term(body, target, depth + arity)}
     end)}
  end

  defp abstract_term(term, target, depth) when is_tuple(term),
    do: rebuild(term, Enum.map(children(term), &abstract_term(&1, target, depth)))

  defp abstract_term(term, target, depth) when is_list(term),
    do: Enum.map(term, &abstract_term(&1, target, depth))

  defp abstract_term(term, _target, _depth), do: term

  defp children(term) when is_tuple(term), do: term |> Tuple.to_list() |> tl()
  defp children(term) when is_list(term), do: term
  defp children(_term), do: []

  # Free de Bruijn indices in `term`, counted from `depth` binders in (binder-
  # aware for Π/λ/Σ/case, mirroring abstract_term). Used to check convoy sibling
  # independence.
  defp free_indices({:var, i}, depth) when i >= depth, do: MapSet.new([i - depth])
  defp free_indices({:var, _}, _depth), do: MapSet.new()

  defp free_indices({:pi, _g, d, c}, depth),
    do: MapSet.union(free_indices(d, depth), free_indices(c, depth + 1))

  defp free_indices({:lam, _g, d, b}, depth),
    do: MapSet.union(free_indices(d, depth), free_indices(b, depth + 1))

  defp free_indices({:case, s, m, brs}, depth) do
    base = MapSet.union(free_indices(s, depth), free_indices(m, depth))
    Enum.reduce(brs, base, fn {_c, ar, b}, acc -> MapSet.union(acc, free_indices(b, depth + ar)) end)
  end

  defp free_indices(term, depth) when is_tuple(term),
    do: term |> children() |> Enum.reduce(MapSet.new(), &MapSet.union(&2, free_indices(&1, depth)))

  defp free_indices(term, depth) when is_list(term),
    do: Enum.reduce(term, MapSet.new(), &MapSet.union(&2, free_indices(&1, depth)))

  defp free_indices(_term, _depth), do: MapSet.new()

  # Largest free de Bruijn index occurring anywhere in `terms` (−1 if none). Used
  # to pick sentinel variables for computed-index abstraction that are guaranteed
  # not to alias any existing variable.
  defp max_free_ref(terms) do
    terms
    |> Enum.reduce(MapSet.new(), fn t, acc -> MapSet.union(acc, free_indices(t, 0)) end)
    |> MapSet.to_list()
    |> Enum.max(fn -> -1 end)
  end

  # `Quote.reify` collapses a `{:vdata, name, params ++ indices}` value into
  # `{:data, name, all_args, []}` (the value rep does not track the param/index
  # split). Restore the split for every data application in `term` using the
  # family's declared param count, so the kernel's `:data` rule — which checks
  # params and indices against separate telescopes — accepts reified sibling and
  # transport types.
  defp resplit_data({:data, name, params, indices}, env) do
    combined = Enum.map(params ++ indices, &resplit_data(&1, env))
    {ps, is} = Enum.split(combined, Inductive.param_count(env, name))
    {:data, name, ps, is}
  end

  defp resplit_data(term, env) when is_tuple(term),
    do: rebuild(term, Enum.map(children(term), &resplit_data(&1, env)))

  defp resplit_data(term, env) when is_list(term),
    do: Enum.map(term, &resplit_data(&1, env))

  defp resplit_data(term, _env), do: term

  defp rebuild(term, children) when is_tuple(term) do
    [elem(term, 0) | children] |> List.to_tuple()
  end

  defp rebuild(term, _children), do: term

  defp implicit_def?(env, atom) do
    case Env.get_def(env, atom) do
      %{quantities: q} when is_list(q) -> :erased in q
      _ -> false
    end
  end

  # Residual explicit-parameter count for a partial application in checking mode:
  # the def's explicit (non-erased) arity minus the number of supplied arguments.
  # Positive means the call is under-saturated. Only defs with recorded
  # per-parameter quantities participate (every implicit-carrying def has them);
  # a def without quantities returns 0 so its existing partial-application
  # behaviour — non-implicit currying, which the kernel already types — is left
  # exactly as-is.
  defp residual_explicit_arity(env, key, supplied) do
    case Env.get_def(env, key) do
      %{quantities: q} when is_list(q) -> Enum.count(q, &(&1 != :erased)) - supplied
      _ -> 0
    end
  end

  # Eta-expand an under-saturated call by `k` explicit binders: `f(a1..an)`
  # becomes `fn($eta0 .. $eta{k-1}) -> f(a1..an, $eta0 .. $eta{k-1})`. The
  # `$`-prefixed binder names are synthetic and cannot collide with a source
  # identifier. Reuses the original call `meta` (carrying `:name`) for the now-
  # saturated inner application.
  defp eta_expand_call(meta, args, k) do
    vars = for i <- 0..(k - 1), do: {:variable, [], "$eta#{i}"}
    params = for i <- 0..(k - 1), do: {:param, [], "$eta#{i}"}
    {:lambda, [params: params], [{:function_call, meta, args ++ vars}]}
  end

  # Map a surface call name to its def-registry key: a qualified (`Std.Map.keys`)
  # name resolves through the value namespace, a bare name through bare-shadowing;
  # either falls back to the raw atom. Mirrors the `resolved` computation at the
  # top of `elaborate_named_call_scoped` so the checked-mode retry looks up the
  # same def the inference path does.
  defp resolve_def_key(env, name, atom) do
    if String.contains?(name, ".") do
      case Cure.Elab.Resolution.resolve_qualified(env, name, :value) do
        {:ok, key} -> key
        :error -> atom
      end
    else
      case Cure.Elab.Resolution.resolve_bare(env, atom) do
        {:ok, key} -> key
        _ -> atom
      end
    end
  end

  defp map_present_args(args, names, ctx, env) do
    depth = Context.length(ctx)

    Enum.reduce_while(args, {:ok, []}, fn arg, {:ok, acc} ->
      case elaborate_expr_typed(arg, names, ctx, env) do
        # Reify at the caller's depth AND with the inductive signature. Semantic
        # data values flatten parameters and indices; a signature-free readback
        # would turn `IsPositive(n)` (zero parameters, one index) into a bogus
        # one-parameter family before it is unified with a dependent call slot.
        {:ok, term, type} ->
          {:cont, {:ok, acc ++ [{term, Quote.reify(type, depth, env)}]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  @doc """
  Elaborate a surface `match scrut | C(pat…) -> body …` into a Core `:case`
  (design spec §5, M8.4). `result_type_term` is the expected result type (Core
  term in the current frame); the motive is built as a constant type family over
  the scrutinee family's indices and value (dependent motives — a result that
  varies with the matched indices — are a follow-up). Branch bodies are
  elaborated under the constructor's full telescope (erased indices + present
  args); surface pattern variables name the present positions. Coverage and
  per-branch index refinement are then enforced by the kernel.
  """
  @spec elaborate_match(term(), [tuple()], term(), [String.t()], Context.t(), Env.t()) ::
          {:ok, term()} | {:error, term()}
  def elaborate_match(scrut_expr, arms0, result_type_term, names, ctx, env) do
    # A tuple SCRUTINEE (`match %[xs, ys] | %[C(…), D(…)] -> …`) is lowered to a
    # nested single-scrutinee match (`match xs | C(…) -> match ys | D(…) -> …`),
    # so the existing dependent single-scrutinee machinery handles it — absurd
    # cross-constructor cases (a `Vector`'s shared index rules them out) fall out
    # of the inner index-refined match's coverage, exactly as the hand-written
    # nested form already does. Non-tuple scrutinees are returned unchanged.
    # Wave-2 List sugar in pattern position: rewrite each arm's `[]`/`[h|t]`
    # `:pattern` meta to Nil/Cons ctor-call form BEFORE any downstream pass, so
    # rekey/refine/constructor_pattern all see the uniform function_call shape and
    # no `:list` node survives. One-deep only; a nested list pattern desugars to a
    # nested ctor pattern that `constructor_pattern/1` rejects (:nested_constructor_arg).
    arms0 = arms0 |> desugar_list_patterns() |> desugar_typed_constructor_args()
    {scrut_expr, arms0} = desugar_tuple_scrutinee(scrut_expr, arms0)

    if hoist_named_default?(scrut_expr, arms0) do
      hoist_named_default_scrutinee(scrut_expr, arms0, result_type_term, names, ctx, env)
    else
      elaborate_match_dispatch(scrut_expr, arms0, result_type_term, names, ctx, env)
    end
  end

  # A *named* default (`… | other -> body`) binds the WHOLE scrutinee value, but
  # `desugar_with_default` can only do so when the scrutinee is already a
  # variable. A complex scrutinee (`match S(n) | S(Z()) -> … | other -> …`) has
  # nothing to bind `other` to and would otherwise reject as
  # `:catchall_with_nesting`. Hoist it into a fresh `let $s = scrut in match $s
  # | …` so the whole variable-scrutinee machinery applies and `$s` is evaluated
  # exactly once (Idris' `case … of other =>` binds once likewise). Engaged only
  # when nesting forces the default path AND the scrutinee is not already a
  # variable, so the common cases are untouched.
  defp hoist_named_default?(scrut_expr, arms) do
    not match?({:variable, _m, _n}, scrut_expr) and
      Enum.any?(arms, &named_default_arm?/1) and
      Enum.any?(arms, &arm_has_nested?/1)
  end

  defp named_default_arm?({:match_arm, meta, _body}) do
    case Keyword.fetch!(meta, :pattern) do
      {:variable, _m, name} -> name != "_"
      _ -> false
    end
  end

  defp hoist_named_default_scrutinee(scrut_expr, arms, result_type_term, names, ctx, env) do
    sname = "$scrut" <> fresh_tag()
    svar = {:variable, [], sname}
    assign = {:assignment, [let: true], [svar, scrut_expr]}
    inner_match = {:pattern_match, [], [svar | arms]}
    elaborate_let_block([assign, inner_match], result_type_term, names, ctx, env)
  end

  defp elaborate_match_dispatch(scrut_expr, arms0, result_type_term, names, ctx, env) do
    with {:ok, arms1} <- desugar_as_patterns(arms0),
         {:ok, arms1b} <- desugar_tuple_args(arms1),
         # A guard on a *nested* constructor pattern is threaded through the
         # pattern-matrix compiler here: rows carry their guard, and each matrix
         # leaf folds the reached rows into a `:case`-on-Bool `if`-chain whose tail is
         # the next row (the Wadler/Augustsson `match … default` continuation,
         # à la Idris' `CaseBuilder` errorCase — but over surface names, so no
         # de-Bruijn weakening is needed).
         {:ok, arms1c} <- desugar_nested_arms(arms1b, scrut_expr),
         # A guard on a *single-level* constructor pattern (which never reaches the
         # matrix) is folded into a guardless arm whose body is a `:case`-on-Bool
         # `if`-chain over the constructor group's rows (same-constructor
         # fall-through), so it flows through the ordinary `:vdata` path below. A
         # guard on a *variable/catch-all* pattern is left for `try_guard_match`.
         {:ok, arms} <- desugar_ctor_guards(arms1c, scrut_expr),
         # A `when` guard is orthogonal to the pattern's shape, so it is resolved
         # before the shape-dispatching paths (each of which would silently drop
         # the guard). Claims EVERY guarded match: handles the tractable subset,
         # errors on the rest — so no path below ever ignores a guard.
         :not_applicable <-
           try_guard_match(scrut_expr, arms, result_type_term, names, ctx, env),
         :not_applicable <- try_tuple_match(scrut_expr, arms, result_type_term, names, ctx, env),
         {:ok, scrut_term, scrut_type} <- elaborate_expr_typed(scrut_expr, names, ctx, env),
         :ok <- validate_typed_pattern_annotations(arms, scrut_type, names, ctx, env),
         :not_applicable <-
           try_trivial_match(scrut_expr, arms, result_type_term, names, ctx, env),
         :not_applicable <-
           try_literal_match(
             scrut_expr,
             arms,
             scrut_term,
             scrut_type,
             result_type_term,
             names,
             ctx,
             env
           ) do
      case scrut_type do
        {:vdata, dname, combined_vals} ->
          family = Inductive.get_family(env, dname)
          # The scrutinee's args are parameters ++ indices; split off the leading
          # parameters. Only the indices are abstracted by the motive and refined
          # per branch — parameters are uniform (never matched).
          pc = Inductive.param_count(env, dname)
          {param_vals, idx_vals} = Enum.split(combined_vals, pc)
          param_terms = Enum.map(param_vals, &Quote.reify(&1, Context.length(ctx)))
          idx_terms = Enum.map(idx_vals, &Quote.reify(&1, Context.length(ctx)))

          motive0 =
            build_motive(dname, family.indices, param_terms, idx_terms, scrut_term, result_type_term)

          # Step 3b: a *sibling* whose type mentions the scrutinee's stuck computed
          # index (`w : F(app(p,q))`) is not refined by 3a's motive (that only
          # generalizes the scrutinee's own goal). Carry `Eq(T, app(p,q), jₚₒₛ)`
          # into the motive and transport each such sibling in the branch body —
          # the same kernel-checked Eq-arrow + `rewrite` vehicle as capability B,
          # lifted from the scrutinee VALUE to its computed INDEX term.
          carried = detect_carried_index(family.indices, idx_terms, scrut_term, names, ctx, env)
          k = length(family.indices)
          motive = if carried, do: wrap_motive_carried_eq(motive0, k, carried), else: motive0

          # Anonymous-union elimination. Runs LATE — unlike the other desugarings,
          # which fire before the scrutinee is even elaborated — because it needs the
          # scrutinee's family key, which is only known here. Typed-pattern arms
          # (`n: Int`) become ordinary ctor-pattern arms, so coverage, exhaustiveness
          # and totality all come from the existing machinery below.
          with {:ok, arms} <- desugar_union_arms(arms, dname, names, env) do
            standard =
              with {:ok, branches, join} <-
                     elaborate_branches(
                       arms,
                       names,
                       ctx,
                       env,
                       dname,
                       idx_vals,
                       param_vals,
                       scrut_term,
                       result_type_term,
                       carried,
                       motive
                     ) do
                case_term = wrap_join({:case, scrut_term, motive, branches}, join)
                {:ok, if(carried, do: {:app, case_term, mk_refl(carried.idx_term)}, else: case_term)}
              end

            # Item C: the standard motive refines the RETURN per branch but not the
            # types of scrutinee-dependent SIBLINGS (`w : ReplyOf(r)`), so a plain
            # `match r` that reads such a sibling ill-types. Detect siblings only for a
            # non-indexed family matched on a VARIABLE (cheap gate). If present, retry
            # via motive-generalization (the machinery `with r` uses) when the standard
            # path FAILS during elaboration, OR when it succeeds but the assembled term
            # does not KERNEL-check — the sibling-read failure surfaces there, not in
            # `elaborate_branches` (`GetCount() -> w`, `:branch_type`). Sibling-free
            # matches keep the standard path untouched; the extra kernel-check runs only
            # for the rare match that has a scrutinee-dependent sibling.
            # Cheap gate first: a scrutinee-dependent sibling exists only if the
            # scrutinee VARIABLE occurs in some context binder's TYPE. Test that on the
            # stored VALUES (no reification) before the expensive `collect_with_siblings`
            # (which reifies every binder) + kernel-check — so an ordinary sibling-free
            # match pays only a value-level walk.
            siblings =
              with {:var, i} <- scrut_term,
                   true <- family.indices == [],
                   scrut_level = Context.length(ctx) - 1 - i,
                   true <- context_type_mentions_var?(ctx, scrut_level),
                   {:ok, s} <- collect_with_siblings(scrut_term, names, ctx, env) do
                s
              else
                _ -> []
              end

            retry = fn ->
              elaborate_motivegen_case(
                scrut_term,
                scrut_type,
                dname,
                combined_vals,
                siblings,
                arms,
                result_type_term,
                names,
                ctx,
                env
              )
            end

            cond do
              siblings == [] -> standard
              match?({:error, _}, standard) -> retry.()
              match_term_kernel_rejects?(elem(standard, 1), result_type_term, ctx) -> retry.()
              true -> standard
            end
          end

        _ ->
          {:error, :match_scrutinee_not_data}
      end
    end
  end

  # ── Anonymous-union elimination ────────────────────────────────────────────

  # Rewrite typed-pattern and literal arms into ordinary constructor-pattern arms
  # against the union family `dname`, so everything downstream — `partition_arms/4`,
  # coverage, exhaustiveness, totality — works unchanged.
  #
  # A no-op when the scrutinee is not a generated union, so an ordinary `match` over
  # a user ADT is untouched.
  defp desugar_union_arms(arms, dname, names, env) do
    if Cure.Elab.Union.union_family?(dname) do
      Enum.reduce_while(arms, {:ok, []}, fn arm, {:ok, acc} ->
        case expand_union_arm(arm, dname, names, env) do
          {:ok, expanded} -> {:cont, {:ok, acc ++ expanded}}
          {:error, _} = err -> {:halt, err}
        end
      end)
    else
      {:ok, arms}
    end
  end

  defp expand_union_arm({:match_arm, meta, body} = arm, dname, names, env) do
    case Keyword.get(meta, :pattern) do
      # `n: Int` — a type member, or `rest: Bool | Atom` — a SUB-UNION, which expands
      # into one arm per member of the sub-union.
      {:typed_pattern, pm, [name, type_ast]} ->
        with {:ok, members} <- Cure.Elab.Union.canonicalise([type_ast], names, env) do
          sub_union? = length(members) > 1

          Enum.reduce_while(members, {:ok, []}, fn m, {:ok, acc} ->
            cname = Cure.Elab.Union.ctor_key(dname, m)

            case expand_member_arm(meta, pm, name, type_ast, cname, m, sub_union?, body) do
              {:ok, arm} -> {:cont, {:ok, [arm | acc]}}
              {:error, _} = err -> {:halt, err}
            end
          end)
          |> case do
            {:ok, arms} -> {:ok, Enum.reverse(arms)}
            {:error, _} = err -> err
          end
        end

      # `:north` — a literal member, matched bare, binding nothing.
      {:literal, lm, value} ->
        case Cure.Elab.Union.literal_key(Keyword.get(lm, :subtype), value) do
          {:ok, key} ->
            cname = Cure.Elab.Union.ctor_key(dname, %{key: key})
            pattern = {:function_call, [name: Atom.to_string(cname)], []}
            {:ok, [{:match_arm, Keyword.put(meta, :pattern, pattern), body}]}

          :error ->
            {:ok, [arm]}
        end

      _ ->
        {:ok, [arm]}
    end
  end

  # A single member of a typed-pattern arm.
  #
  # For a plain member the bound name IS the payload, so the ctor pattern binds it
  # directly.
  #
  # For a SUB-UNION member (`rest: Bool | Atom`) the bound name must carry the
  # SUB-UNION's type, not this one member's payload type. So the ctor pattern binds a
  # FRESH name, and every occurrence of the surface name in the body is replaced by
  # `assert_type <fresh> : <sub-union>` — an ascription, which elaborates the fresh
  # payload in CHECK position against the sub-union and therefore re-injects it via
  # the ordinary union coercion. (A `let`-block cannot be used here: `:block` has no
  # infer-mode clause, and branch bodies are elaborated in infer mode.)
  #
  # `subst_surface_var/3` is a blind textual walk with no notion of scope, so it must
  # not run if `body` contains a NESTED binder that rebinds `name` — a nested `match`
  # arm whose own pattern is also `name`, or a lambda parameter named `name`. Left
  # unguarded, the inner (correctly narrower-typed) occurrence would be silently
  # overwritten by the outer sub-union ascription. `binds_any?/2` is the same
  # capture-avoidance guard `elaborate_let_block` and friends use for the identical
  # class of problem; when it fires here, refuse rather than attempt a smarter
  # rewrite, matching that established idiom.
  defp expand_member_arm(meta, pm, name, type_ast, cname, m, sub_union?, body) do
    cond do
      # A LITERAL member binds no payload — the value IS the constructor. But the arm still
      # gave it a NAME (`n: 3`, or the literal arm of `rest: Bool | 3`), and the body may
      # use it. Passing `body` through untouched leaves that name resolving to whatever it
      # means in the ENCLOSING scope — it typechecks, compiles, and returns the wrong
      # value. So substitute the name with the literal itself, ascribed to the arm's type,
      # exactly as the sub-union branch substitutes its fresh payload binder. And run the
      # SAME capture guard: this branch was skipping it entirely.
      m.payload == nil and binds_any?(body, [name]) ->
        {:error, {:unsupported_pattern, :shadowed_literal_member}}

      m.payload == nil ->
        pattern = {:function_call, [name: Atom.to_string(cname)], []}

        rebound =
          case Cure.Elab.Union.literal_surface(m.key) do
            {:ok, lit} ->
              ascription = {:assert_type, pm, [lit, type_ast]}
              Enum.map(body, &subst_surface_var(&1, name, ascription))

            :error ->
              body
          end

        {:ok, {:match_arm, Keyword.put(meta, :pattern, pattern), rebound}}

      sub_union? and binds_any?(body, [name]) ->
        {:error, {:unsupported_pattern, :shadowed_sub_union}}

      sub_union? ->
        fresh = "__u" <> Integer.to_string(:erlang.phash2({name, m.key}))
        pattern = {:function_call, [name: Atom.to_string(cname)], [{:variable, pm, fresh}]}

        ascription = {:assert_type, pm, [{:variable, pm, fresh}, type_ast]}
        rebound = Enum.map(body, &subst_surface_var(&1, name, ascription))

        {:ok, {:match_arm, Keyword.put(meta, :pattern, pattern), rebound}}

      true ->
        pattern = {:function_call, [name: Atom.to_string(cname)], [{:variable, pm, name}]}
        {:ok, {:match_arm, Keyword.put(meta, :pattern, pattern), body}}
    end
  end

  @doc """
  Elaborate a surface `with <scrut> [proof <name>] | C(pat…) -> body …` into a
  Core `:case`. Unlike `elaborate_match`, the motive is *value-abstracting*: the
  scrutinee EXPRESSION is abstracted out of the goal (`motive_for`-style), so
  each branch's expected type is the goal with the scrutinee replaced by that
  branch's constructor value — goal refinement that plain `match` cannot do (its
  `build_motive` only generalizes type INDICES).

  Capabilities A (goal refinement), B (`proof <name>`), and sibling/other-
  argument refinement share ONE Eq-arrow mechanism. Let `e : T`, goal `G`, and
  the SIBLINGS be the in-scope parameters `h_j : H_j` whose type mentions `e`.
  When either a proof clause or a sibling is present, the motive carries the
  scrutinee equation:

      motive = λ(w:T). Eq(T, e, w) -> G[e↦w]
      term   = (case e of … branches …) (refl e)   : G

  and each branch receives `prf : Eq(T, e, pat)` (the user's proof name, or an
  internal one). Siblings are refined **by transport in the branch body**, NOT
  by generalizing their type into the motive. (When this was written, a
  `Π(SNat(w))…` motive domain tripped `Quote.reify`'s `{:vdata}` param/index
  collapse. The no-proof sibling case now DOES generalize into the motive —
  `elaborate_motivegen_case` — and index-bearing families work there because
  `collect_with_siblings` applies `resplit_data`, recovering the split; see
  `linear_sibling_refinement_test.exs`. This proof-clause path keeps transport.)
  For each sibling:

      h_j' = rewrite prf (λx. H_j[e↦x]) h_j   : H_j[e↦pat]

  bound in the arm body via `(λ h_j'. body) h_j'`, so the ORIGINAL name resolves
  to the refined `h_j'`. The indexed-data type only ever appears as a `:rewrite`
  motive RESULT (which the kernel `Eval.apply`s, never reifies) — sound, no TCB.
  Capability A is the no-equation special case (bare value-abstracting motive).
  Restricted to a non-indexed scrutinee family; this slice generalizes only
  siblings that form an independent set (see `collect_with_siblings`).
  """
  @spec elaborate_with(term(), [tuple()], String.t() | nil, term(), [String.t()], Context.t(), Env.t(), [tuple()]) ::
          {:ok, term()} | {:error, term()}
  def elaborate_with(scrut_expr, arms, proof_name, result_type_term, names, ctx, env, original_params \\ []) do
    cond do
      Enum.any?(arms, &with_rematch_arm?/1) ->
        if Enum.all?(arms, &with_rematch_arm?/1) do
          elaborate_with_rematch(scrut_expr, arms, original_params, result_type_term, names, ctx, env)
        else
          {:error, :with_mixed_rematch_arms}
        end

      true ->
        elaborate_with_value(scrut_expr, arms, proof_name, result_type_term, names, ctx, env)
    end
  end

  defp with_rematch_arm?({:with_rematch_arm, _, _}), do: true
  defp with_rematch_arm?(_), do: false

  # Capability A/B (no LHS re-match): value-abstracting motive + eq-arrow sibling
  # transport, restricted to a NON-indexed scrutinee family. This is the original
  # `elaborate_with` body, unchanged.
  defp elaborate_with_value(scrut_expr, arms, proof_name, result_type_term, names, ctx, env) do
    with {:ok, scrut_term, scrut_type} <- elaborate_expr_typed(scrut_expr, names, ctx, env) do
      case scrut_type do
        {:vdata, dname, combined_vals} ->
          family = Inductive.get_family(env, dname)

          with {:ok, siblings} <- collect_with_siblings(scrut_term, names, ctx, env) do
            # An Eq-arrow is needed when the user asked for a proof OR when a
            # sibling must be transported (both consume `prf : Eq(T,e,pat)`).
            need_eq = proof_name != nil or siblings != []

            cond do
              # Capability A (bare value-abstraction) is SUBSUMED by the unified
              # match front-end: since Phase 2½ plain `match` value-refines the
              # goal per branch (the same refinement A's `{:lam, Cure.Core.Grade.unrestricted(), T, g_abs}` motive
              # provided), so `with <e>` with no proof and no sibling is exactly a
              # plain `match <e>`. (Task 3.2; the arms are already `{:match_arm}`.)
              # elaborate_match handles indexed AND non-indexed families, so the
              # no-eq path is index-agnostic — a bare `with` over an indexed-family
              # scrutinee (`with v` for `v : NVv(n)`) refines the same as `match v`.
              not need_eq ->
                elaborate_match(scrut_expr, arms, result_type_term, names, ctx, env)

              # Sibling refinement WITHOUT a user proof, single sibling: use
              # MOTIVE-GENERALIZATION rather than Eq-transport. The sibling becomes a
              # Π domain in the case motive and a real λ binder per branch, so a LINEAR
              # sibling STAYS linear — the Eq-transport `transport_case(prf) cap`
              # encoding is a collapsible case that erases to identity but which the
              # relevance checker ω-scaled pre-erasure (over-counting a dup, masking a
              # drop). Here `cap` is a direct convoy argument `(case e …) cap` whose
              # per-branch λ binder `check_binder` polices; the relevance convoy rule
              # counts it once. The branch-λ grade is ω — the sibling's REAL grade is
              # enforced at its own binding site (the def's `:linear cap`) via the
              # convoy. Restricted to ONE sibling; the proof form and multi-sibling keep
              # the Eq-arrow path below.
              family.indices == [] and proof_name == nil and siblings != [] ->
                elaborate_motivegen_case(
                  scrut_term,
                  scrut_type,
                  dname,
                  combined_vals,
                  siblings,
                  arms,
                  result_type_term,
                  names,
                  ctx,
                  env
                )

              # Capability B (proof / sibling transport) — the Eq-arrow motive.
              # This slice's eq-arrow motive is built for a NON-indexed scrutinee
              # family; an indexed scrutinee that also needs transport must use the
              # multi-column LHS-rematch form (`elaborate_with_rematch`) instead.
              family.indices == [] ->
                pc = Inductive.param_count(env, dname)
                {param_vals, _idx_vals} = Enum.split(combined_vals, pc)
                scrut_type_term = resplit_data(Quote.reify(scrut_type, Context.length(ctx)), env)
                g_abs = abstract_term(result_type_term, scrut_term, 0)
                motive = eq_arrow_motive(scrut_type_term, scrut_term, g_abs)

                cfg = %{
                  names: names,
                  ctx: ctx,
                  env: env,
                  dname: dname,
                  param_vals: param_vals,
                  motive: motive,
                  need_eq: true,
                  siblings: siblings,
                  prf_name: proof_name || "$with_prf",
                  scrut_term: scrut_term,
                  scrut_type_term: scrut_type_term
                }

                with {:ok, branches} <- elaborate_with_branches(arms, cfg) do
                  case_term = {:case, scrut_term, motive, branches}
                  {:ok, {:app, case_term, mk_refl(scrut_term)}}
                end

              true ->
                {:error, {:with_indexed_scrutinee_unsupported, dname}}
            end
          end

        _ ->
          {:error, :with_scrutinee_not_data}
      end
    end
  end

  # -- LHS re-match over an indexed view (Idris-parity indexed views) ----------
  #
  # A with-clause that restates the parent LHS (`{:with_rematch_arm}`) is
  # elaborated like an indexed `match` — NOT the value-abstracting capability-A
  # path. The scrutinee (e.g. `view n : NV n`) is genuinely indexed; the goal is
  # generalized over its index variables by `build_motive`, and each branch is
  # refined by the kernel's index inversion (`branch_unify` yields `n := S(m)`).
  # That SAME substitution refines the branch goal AND every index-mentioning
  # sibling (e.g. `w : SNat n` ↦ `SNat (S m)`) via `specialize_branch_context`.
  # The kernel independently re-checks the assembled `{:case,…}`, so the
  # refinement is sound with no TCB change (the index equation comes from the
  # case eliminator, not from an index-injectivity assumption). `match_parent_lhs`
  # validates each restated LHS is constructor-refined (rejecting forced/
  # arithmetic patterns — the deferred #5 case) before the arm is admitted.
  defp elaborate_with_rematch(scrut_expr, arms, original_params, result_type_term, names, ctx, env) do
    with {:ok, scrut_term, scrut_type} <- elaborate_expr_typed(scrut_expr, names, ctx, env) do
      case scrut_type do
        {:vdata, dname, combined_vals} ->
          family = Inductive.get_family(env, dname)
          pc = Inductive.param_count(env, dname)
          {param_vals, idx_vals} = Enum.split(combined_vals, pc)
          depth = Context.length(ctx)
          param_terms = Enum.map(param_vals, &Quote.reify(&1, depth))
          idx_terms = Enum.map(idx_vals, &Quote.reify(&1, depth))

          motive =
            build_motive(dname, family.indices, param_terms, idx_terms, scrut_term, result_type_term)

          with {:ok, arm_map} <- partition_rematch_arms(arms, original_params, ctx, env, dname),
               {:ok, branches} <-
                 elaborate_rematch_branches(
                   arm_map,
                   names,
                   ctx,
                   env,
                   dname,
                   idx_vals,
                   param_vals,
                   scrut_term,
                   result_type_term
                 ) do
            {:ok, {:case, scrut_term, motive, branches}}
          end

        _ ->
          {:error, :with_scrutinee_not_data}
      end
    end
  end

  # Build `cname => {:matched, with_pattern, body} | {:impossible_marked, ...}`,
  # validating (a) the with-pattern names one of dname's OWN constructors (reused
  # from `partition_arms` semantics), and (b) the restated parent patterns are a
  # legal LHS re-match of `original_params` (`match_parent_lhs`) — the point at
  # which a forced/arithmetic restated pattern (`k+k`) is rejected.
  defp partition_rematch_arms(arms, original_params, ctx, env, dname) do
    sig = Context.signature(ctx)

    Enum.reduce_while(arms, {:ok, %{}}, fn {:with_rematch_arm, arm_meta, body}, {:ok, acc} ->
      with_pattern = Keyword.fetch!(arm_meta, :pattern)
      parent_patterns = Keyword.fetch!(arm_meta, :parent_patterns)

      with {:ok, {cname0, _vars}} <- constructor_pattern(with_pattern),
           {:ok, _subst} <- match_parent_lhs(original_params, parent_patterns) do
        cname = resolve_ctor_key(env, cname0)
        with_pattern = rekey_pattern_name(with_pattern, cname)

        cond do
          Inductive.get_ctor(env, cname) == nil ->
            {:halt, {:error, {:unknown_pattern_constructor, cname}}}

          Inductive.ctor_family(sig, cname) != dname ->
            {:halt, shadowed_or_foreign_ctor(env, sig, cname0, cname, dname)}

          Map.has_key?(acc, cname) ->
            {:halt, {:error, {:duplicate_branch, cname}}}

          true ->
            {:cont, {:ok, Map.put(acc, cname, {:matched, with_pattern, single_body(body)})}}
        end
      else
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # One Core branch per declared constructor (coverage), mirroring
  # `elaborate_branches`: an omitted/impossible constructor is discharged with
  # `{:absurd}`; a matched constructor's body is elaborated under the kernel's
  # index-refinement substitution.
  defp elaborate_rematch_branches(arm_map, names, ctx, env, dname, idx_vals, param_vals, scrut_term, result_type_term) do
    sig = Context.signature(ctx)

    sig
    |> Inductive.ctors_of(dname)
    |> Enum.map(& &1.name)
    |> Enum.reduce_while({:ok, []}, fn cname, {:ok, acc} ->
      verdict = Kernel.branch_unify(ctx, dname, cname, idx_vals, param_vals)

      case Map.get(arm_map, cname) do
        {:matched, with_pattern, body_expr} ->
          case elaborate_rematch_branch(
                 verdict,
                 cname,
                 with_pattern,
                 body_expr,
                 names,
                 ctx,
                 env,
                 param_vals,
                 scrut_term,
                 result_type_term
               ) do
            :omit -> {:cont, {:ok, acc}}
            {:ok, branch} -> {:cont, {:ok, acc ++ [branch]}}
            {:error, _} = err -> {:halt, err}
          end

        nil ->
          if verdict == :impossible do
            # impossible constructor ⇒ OMIT it (K4 §H); the kernel's partial
            # coverage accepts the omission. No {:absurd} placeholder body.
            {:cont, {:ok, acc}}
          else
            {:halt, {:error, {:missing_branch, cname}}}
          end
      end
    end)
  end

  defp elaborate_rematch_branch(
         verdict,
         cname,
         with_pattern,
         body_expr,
         names,
         ctx,
         env,
         param_vals,
         scrut_term,
         result_type_term
       ) do
    {:ok, {^cname, pattern_vars}} = constructor_pattern(with_pattern)
    %{args: telescope, quantities: quantities} = Inductive.get_ctor(env, cname)
    arity = length(telescope)
    branch_names = branch_scope(telescope, quantities, pattern_vars) ++ names

    case verdict do
      :impossible ->
        # impossible ⇒ signal omission to the caller (K4 §H); no {:absurd} body.
        :omit

      _solved_or_trivial ->
        subst =
          case verdict do
            {:solved, s} -> s
            :trivial -> %{}
          end

        # The index inversion (`n := S(m)`) refines the branch goal AND every
        # index-mentioning sibling in the context.
        branch_ctx =
          ctx
          |> extend_context(telescope, param_vals)
          |> specialize_branch_context_subst(subst)

        # Compose (1b) value-refinement with (1a) index inversion via the shared
        # `refine_branch_goal` (Task 3.4) — the SAME refinement plain match uses.
        # The rematch path abstracts the computed scrutinee in the MOTIVE (shared
        # `build_motive`); this refines the branch goal to the constructor too.
        branch_expected =
          refine_branch_goal(result_type_term, scrut_term, cname, arity, subst, branch_ctx)

        body_expr = refine_scrutinee_in_body(body_expr, scrut_term, with_pattern, pattern_vars, names)

        with {:ok, body_term} <-
               elaborate_branch_body(body_expr, branch_expected, branch_names, branch_ctx, env) do
          {:ok, {cname, arity, body_term}}
        end
    end
  end

  # Refine every context type by a branch substitution (kernel-frame de Bruijn
  # keys), mirroring the kernel's `specialize_branch_context`: reify → replace →
  # re-eval (the reify/eval round-trip repairs the flat-`{:vdata}` split).
  defp specialize_branch_context_subst(ctx, subst) when map_size(subst) == 0, do: ctx

  defp specialize_branch_context_subst(ctx, subst) do
    depth = Context.length(ctx)
    env = Context.env(ctx)

    types =
      Enum.map(ctx.types, fn type_value ->
        type_value
        |> Quote.reify(depth)
        |> replace_branch_vars(subst)
        |> Eval.eval(env)
      end)

    refined_env =
      for i <- 0..(depth - 1)//1 do
        {:var, i}
        |> replace_branch_vars(subst)
        |> Eval.eval(env)
      end

    %{ctx | types: types, env: refined_env}
  end

  # Eq-arrow motive `λ(w:T). Eq(T, e, w) -> G[e↦w]`. Under the `w`-binder, `e`/`T`
  # shift by +1; `g_abs` (= `G[e↦w]`, already under one binder) shifts +1 more to
  # clear the extra Eq-arrow (proof) binder.
  defp eq_arrow_motive(scrut_type_term, scrut_term, g_abs) do
    eq_ty_w =
      mk_eq(Subst.shift(scrut_type_term, 1, 0), Subst.shift(scrut_term, 1, 0), {:var, 0})

    {:lam, Cure.Core.Grade.unrestricted(), scrut_type_term,
     {:pi, Cure.Core.Grade.unrestricted(), eq_ty_w, Subst.shift(g_abs, 1, 0)}}
  end

  # In-scope parameters whose (reified) type mentions the scrutinee term, in
  # scope order (outermost binder first). STOPs (rather than mis-building) when a
  # generalized sibling's type mentions another generalized sibling, or a kept
  # parameter depends on a generalized one — this slice handles only an
  # independent set.
  defp collect_with_siblings(scrut_term, names, ctx, env) do
    depth = Context.length(ctx)

    gen =
      names
      |> Enum.with_index()
      |> Enum.flat_map(fn {name, i} ->
        if is_binary(name) do
          type_term = resplit_data(Quote.reify(Context.lookup(ctx, i), depth), env)

          if contains_term?(type_term, scrut_term),
            do: [%{name: name, index: i, type_term: type_term}],
            else: []
        else
          []
        end
      end)
      |> Enum.sort_by(& &1.index, :desc)

    gen_set = gen |> Enum.map(& &1.index) |> MapSet.new()

    cond do
      Enum.any?(gen, fn %{type_term: t, index: idx} ->
        not MapSet.disjoint?(free_indices(t, 0), MapSet.delete(gen_set, idx))
      end) ->
        {:error, {:with_sibling_dependency_unsupported, :sibling_references_sibling}}

      Enum.any?(0..(depth - 1)//1, fn i ->
        not MapSet.member?(gen_set, i) and
            not MapSet.disjoint?(
              free_indices(resplit_data(Quote.reify(Context.lookup(ctx, i), depth), env), 0),
              gen_set
            )
      end) ->
        {:error, {:with_sibling_dependency_unsupported, :kept_references_sibling}}

      true ->
        {:ok, gen}
    end
  end

  # Emit one Core branch per surface arm. Reuses partition_arms (same validation
  # as match: own-family ctors, no duplicates). A `-> impossible` arm becomes an
  # `{:absurd}` branch; coverage is enforced by the kernel's check_coverage.
  defp elaborate_with_branches(arms, %{ctx: ctx, env: env, dname: dname} = cfg) do
    with {:ok, {arm_map, default}} <- partition_arms(arms, ctx, env, dname),
         :ok <- reject_with_default(default) do
      arm_map
      |> Enum.reduce_while({:ok, []}, fn
        {_cname, {:impossible_marked, _pattern}}, {:ok, acc} ->
          # explicit `-> impossible` ⇒ OMIT (K4 §H); kernel coverage re-verifies.
          {:cont, {:ok, acc}}

        {cname, {:matched, pattern, body_expr}}, {:ok, acc} ->
          case elaborate_with_branch(cname, pattern, body_expr, cfg) do
            {:ok, branch} -> {:cont, {:ok, acc ++ [branch]}}
            {:error, _} = err -> {:halt, err}
          end
      end)
    end
  end

  # A `with`/`with`-rematch clause refines by restating constructor patterns; a
  # bare variable/wildcard catch-all has no refinement to offer here.
  defp reject_with_default(nil), do: :ok
  defp reject_with_default({vname, _body}), do: {:error, {:unsupported_pattern, {:default_in_with, vname}}}

  defp elaborate_with_branch(cname, pattern, body_expr, cfg) do
    %{
      names: names,
      ctx: ctx,
      env: env,
      param_vals: param_vals,
      motive: motive,
      need_eq: need_eq
    } = cfg

    {:ok, {^cname, pattern_vars}} = constructor_pattern(pattern)
    %{args: telescope, quantities: quantities} = Inductive.get_ctor(env, cname)
    arity = length(telescope)
    branch_names0 = branch_scope(telescope, quantities, pattern_vars) ++ names
    branch_ctx0 = extend_context(ctx, telescope, param_vals)

    ctor_term = branch_constructor_term(cname, arity)
    motive_shifted = Subst.shift(motive, arity, 0)
    applied = Kernel.normalize(branch_ctx0, {:app, motive_shifted, ctor_term})

    if need_eq do
      elaborate_with_eq_branch(cname, arity, ctor_term, applied, branch_ctx0, branch_names0, body_expr, cfg)
    else
      with {:ok, body_term} <-
             elaborate_branch_body(body_expr, applied, branch_names0, branch_ctx0, env) do
        {:ok, {cname, arity, body_term}}
      end
    end
  end

  # The Eq-arrow branch: bind `prf : Eq(T,e,pat)`, transport each `e`-mentioning
  # sibling to its refined type, check the arm body under the refined names, and
  # wrap as `λprf. (λh_1. … (λh_m. body) t_m …) t_1`.
  defp elaborate_with_eq_branch(cname, arity, ctor_term, applied, branch_ctx0, branch_names0, body_expr, cfg) do
    %{env: env, siblings: siblings, prf_name: prf_name, scrut_term: scrut_term, scrut_type_term: scrut_type_term} = cfg

    # `applied` = Π(prf : Eq(T,e,pat)). G[e↦pat]. Bind prf → the branch_ctx1 frame.
    {:pi, _g, eq_dom_term, cod_b1} = applied
    eq_dom_value = Eval.eval(eq_dom_term, Context.env(branch_ctx0))
    branch_ctx1 = Context.extend(branch_ctx0, eq_dom_value)
    branch_names1 = [prf_name | branch_names0]

    # Constants in the branch_ctx1 frame (ctx + ctor telescope + prf).
    sc = arity + 1
    e_b1 = Subst.shift(scrut_term, sc, 0)
    t_b1 = Subst.shift(scrut_type_term, sc, 0)
    pat_b1 = Subst.shift(ctor_term, 1, 0)

    # Per-sibling transport (`prf = {:var,0}`; original `h_j` = {:var, idx+sc}).
    sib_data =
      Enum.map(siblings, fn %{index: idx, name: sname, type_term: h_ctx} ->
        h_b1 = Subst.shift(h_ctx, sc, 0)
        motive_j = {:lam, Cure.Core.Grade.unrestricted(), t_b1, abstract_term(h_b1, e_b1, 0)}
        # J/subst transport (Phase B): prf {:var,0} : Eq(T, e, pat); the case's
        # type is (M_j@e) -> (M_j@pat), applied to the original sibling h_j.
        # Annotation-safety (transport_case doc): M_j abstracts e out of an
        # OUTER-frame sibling type, so it mentions neither `pat` nor the ctor
        # telescope vars pair-2 of the reflexive unify could bind.
        transport =
          {:app, transport_case({:var, 0}, t_b1, motive_j, e_b1), {:var, idx + sc}}

        %{name: sname, dom: replace_term(h_b1, e_b1, pat_b1), transport: transport}
      end)

    m = length(sib_data)

    branch_ctx_full =
      Enum.reduce(sib_data, branch_ctx1, fn %{dom: d}, c ->
        Context.extend(c, Eval.eval(d, Context.env(branch_ctx1)))
      end)

    body_names = Enum.reduce(sib_data, branch_names1, fn %{name: s}, acc -> [s | acc] end)
    cod_expected = Kernel.normalize(branch_ctx_full, Subst.shift(cod_b1, m, 0))

    with {:ok, inner} <-
           elaborate_branch_body(body_expr, cod_expected, body_names, branch_ctx_full, env) do
      wrapped =
        sib_data
        |> Enum.with_index()
        |> Enum.reverse()
        |> Enum.reduce(inner, fn {%{dom: d, transport: t}, i}, acc ->
          {:app, {:lam, Cure.Core.Grade.unrestricted(), Subst.shift(d, i, 0), acc}, Subst.shift(t, i, 0)}
        end)

      {:ok, {cname, arity, {:lam, Cure.Core.Grade.unrestricted(), eq_dom_term, wrapped}}}
    end
  end

  # Cheap value-level check: does any binder type in `ctx` reference the neutral var
  # at `level`? Walks the stored type VALUES without reifying, so an ordinary
  # sibling-free match pays only this. Conservative — a scrutinee buried inside a
  # closure-valued binder type is not seen (that sibling just isn't refined, no worse
  # than before), but the applied-type siblings we care about (`ReplyOf(r)`, `Cap(r)`)
  # are `{:nvar, level}` reachable by structural walk.
  defp context_type_mentions_var?(ctx, level) do
    Enum.any?(ctx.types, &value_mentions_nvar?(&1, level))
  end

  defp value_mentions_nvar?({:nvar, k}, level), do: k == level

  defp value_mentions_nvar?(t, level) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.any?(&value_mentions_nvar?(&1, level))

  defp value_mentions_nvar?(l, level) when is_list(l),
    do: Enum.any?(l, &value_mentions_nvar?(&1, level))

  defp value_mentions_nvar?(_, _), do: false

  # Does the assembled `match` term fail the kernel against its expected type? Used
  # by the item-C fallback: a plain `match` whose body reads a scrutinee-dependent
  # sibling at its unrefined type builds a term `elaborate_branches` accepts but the
  # kernel later rejects (`:branch_type`). A crash in the check is treated as a
  # rejection (retry motive-gen). Only ever called when a sibling is in scope.
  defp match_term_kernel_rejects?(term, result_type_term, ctx) do
    expected = Eval.eval(result_type_term, Context.env(ctx))
    match?({:error, _}, Kernel.check(ctx, term, expected))
  rescue
    _ -> true
  catch
    _, _ -> true
  end

  # Motive-generalization elimination (shared by `with` and plain `match`): refine
  # `m` scrutinee-dependent siblings by generalizing them into the case motive and
  # binding a fresh refined λ per branch, then apply the case to the ORIGINAL
  # siblings. `motive = λw. Π(s₁: H₁[e↦w]) … Π(sₘ: Hₘ[e↦w]). G[e↦w]` (independent
  # siblings, so domain j shifts +(j-1) and G shifts +m). Non-indexed family, variable
  # scrutinee. A linear sibling stays linear (see the relevance convoy rule).
  defp elaborate_motivegen_case(
         scrut_term,
         scrut_type,
         dname,
         combined_vals,
         siblings,
         arms,
         result_type_term,
         names,
         ctx,
         env
       ) do
    scrut_type_term = resplit_data(Quote.reify(scrut_type, Context.length(ctx)), env)
    m = length(siblings)
    g_abs = abstract_term(result_type_term, scrut_term, 0)

    motive_body =
      siblings
      |> Enum.with_index(1)
      |> Enum.reverse()
      |> Enum.reduce(Subst.shift(g_abs, m, 0), fn {%{type_term: h_ctx}, j}, acc ->
        h_abs = abstract_term(h_ctx, scrut_term, 0)
        {:pi, Cure.Core.Grade.unrestricted(), Subst.shift(h_abs, j - 1, 0), acc}
      end)

    motive = {:lam, Cure.Core.Grade.unrestricted(), scrut_type_term, motive_body}
    pc = Inductive.param_count(env, dname)
    {param_vals, _idx_vals} = Enum.split(combined_vals, pc)

    cfg = %{
      names: names,
      ctx: ctx,
      env: env,
      dname: dname,
      param_vals: param_vals,
      motive: motive,
      sibling_names: Enum.map(siblings, & &1.name)
    }

    with {:ok, branches} <- elaborate_with_motivegen_branches(arms, cfg) do
      case_term = {:case, scrut_term, motive, branches}

      applied =
        Enum.reduce(siblings, case_term, fn %{index: idx}, acc ->
          {:app, acc, {:var, idx}}
        end)

      {:ok, applied}
    end
  end

  # Motive-generalization branches (single sibling, no proof). Each branch binds the
  # REFINED sibling as a fresh λ, at the type `motive @ ctor` computes, and rebinds
  # the sibling's ORIGINAL name to it so the body sees the refined type. No Eq, no
  # transport — the linear sibling stays a real linear resource threaded through the
  # convoy `(case e …) cap`.
  defp elaborate_with_motivegen_branches(arms, %{ctx: ctx, env: env, dname: dname} = cfg) do
    with {:ok, {arm_map, default}} <- partition_arms(arms, ctx, env, dname),
         :ok <- reject_with_default(default) do
      arm_map
      |> Enum.reduce_while({:ok, []}, fn
        {_cname, {:impossible_marked, _pattern}}, {:ok, acc} ->
          {:cont, {:ok, acc}}

        {cname, {:matched, pattern, body_expr}}, {:ok, acc} ->
          case elaborate_with_motivegen_branch(cname, pattern, body_expr, cfg) do
            {:ok, branch} -> {:cont, {:ok, acc ++ [branch]}}
            {:error, _} = err -> {:halt, err}
          end
      end)
    end
  end

  defp elaborate_with_motivegen_branch(cname, pattern, body_expr, cfg) do
    %{names: names, ctx: ctx, env: env, param_vals: param_vals, motive: motive, sibling_names: snames} = cfg

    {:ok, {^cname, pattern_vars}} = constructor_pattern(pattern)
    %{args: telescope, quantities: quantities} = Inductive.get_ctor(env, cname)
    arity = length(telescope)
    branch_names0 = branch_scope(telescope, quantities, pattern_vars) ++ names
    branch_ctx0 = extend_context(ctx, telescope, param_vals)

    ctor_term = branch_constructor_term(cname, arity)
    motive_shifted = Subst.shift(motive, arity, 0)
    # applied = Π(s₁: H₁[e↦pat]) … Π(sₘ: Hₘ[e↦pat]). G[e↦pat]
    applied = Kernel.normalize(branch_ctx0, {:app, motive_shifted, ctor_term})

    # Peel one Π per sibling, extending the branch context and rebinding each
    # refined sibling under its original name (so the arm body reads the refined
    # type; the outer unrefined binder is shadowed). Collect the (grade, domain)
    # pairs to wrap the body in the matching λ-nest.
    {branch_ctx, branch_names, cod, doms_rev} =
      Enum.reduce(snames, {branch_ctx0, branch_names0, applied, []}, fn sname, {c, ns, ty, acc} ->
        {:pi, g, dom_term, cod_ty} = ty
        dom_value = Eval.eval(dom_term, Context.env(c))
        {Context.extend(c, dom_value), [sname | ns], cod_ty, [{g, dom_term} | acc]}
      end)

    cod_expected = Kernel.normalize(branch_ctx, cod)

    with {:ok, inner} <-
           elaborate_branch_body(body_expr, cod_expected, branch_names, branch_ctx, env) do
      # doms_rev is innermost-first; folding wraps λs₁'. … λsₘ'. inner (s₁ outermost).
      wrapped =
        Enum.reduce(doms_rev, inner, fn {g, dom_term}, acc -> {:lam, g, dom_term, acc} end)

      {:ok, {cname, arity, wrapped}}
    end
  end

  # motive = λ(j₀:T₀)…λ(jₙ:Tₙ).λ(x : D j̄). ResultType[scrutinee-indices ↦ j̄]
  #
  # The result type is *generalized* over the scrutinee's index arguments: where
  # the scrutinee is `x : D ā` with each aₖ a variable, every occurrence of aₖ in
  # ResultType is rebound to the motive's k-th index binder. Each branch is then
  # checked with that index specialized to the constructor's computed index —
  # this is what refines `m` to `Z`/`S k` in `match (xs : Vec a m)` so a result
  # like `Vec a (plus m n)` typechecks per branch. When ResultType doesn't
  # mention an index variable the generalization is a no-op, degrading to the
  # constant motive.
  defp build_motive(dname, index_tele, param_terms, idx_terms, scrut_term, result_type_term) do
    k = length(index_tele)
    index_types = Enum.map(index_tele, &elem(&1, 1))
    # The scrutinee-binder type `D params̄ j̄` sits under the k index binders j̄;
    # the parameters were reified in the outer frame, so shift them past the k
    # binders. Parameters are uniform, so they are constant across branches (no
    # generalization) — only the indices become the fresh binders `(k-1)..0`.
    param_terms_shifted = Enum.map(param_terms, &Subst.shift(&1, k, 0))
    scrut_type = {:data, dname, param_terms_shifted, Enum.map((k - 1)..0//-1, &{:var, &1})}

    # Map each scrutinee index to the de Bruijn index of its motive binder jₖ
    # (which sits at depth k-pos above the body). A *variable* index position
    # rebinds directly by its de Bruijn name. A *computed* index position — e.g.
    # `app(p, q)`, whose result index is not a single variable — cannot be named
    # that way, so we abstract the whole index *term* out of the result type:
    # every occurrence of that computed index is replaced by a fresh sentinel
    # variable that then rebinds to the position's motive binder. This is the
    # standard casesOn/kabstract motive extended to computed result indices
    # (Lean `inductive.cpp:643-646` reads each ctor's result-index *terms* — which
    # may be arbitrary computed terms — and applies the motive to them): each
    # branch's goal refines to the constructor's own index (`F(app as bs)`,
    # `F(SNil)`), sound with no carried equation because the kernel checks every
    # branch at `motive @ ctor_indices` while the use site recovers the original
    # goal via `motive @ scrutinee_indices`. Sentinels are chosen above every free
    # de Bruijn index in play so they cannot alias a real variable or each other.
    sentinel_base = 1 + max_free_ref([result_type_term, scrut_term | idx_terms])

    {result_type_term, rebind} =
      idx_terms
      |> Enum.with_index()
      |> Enum.reduce({result_type_term, %{}}, fn
        {{:var, orig}, pos}, {rt, acc} ->
          {rt, Map.put(acc, orig, k - pos)}

        {computed, pos}, {rt, acc} ->
          sentinel = sentinel_base + pos
          {replace_term(rt, computed, {:var, sentinel}), Map.put(acc, sentinel, k - pos)}
      end)

    # The scrutinee VALUE rebinds to the motive's last binder `x`. A variable
    # scrutinee rebinds by name; a *computed* scrutinee (e.g. `view(n)`) is
    # abstracted out of the result type the same sentinel way as a computed
    # index — this is Lean's `kabstract result.matchType discr`
    # (`Elab/Match.lean:137`), which abstracts occurrences of the discriminant
    # TERM whether or not it is a variable. Without it a goal like
    # `Eq(NV(n), view(n), view(n))` keeps `view(n)` opaque per branch, and
    # `vs(toS(m)) ≢ vs(s)` — no amount of index refinement can recover it.
    {result_type_term, rebind} =
      case scrut_term do
        {:var, orig} ->
          {result_type_term, Map.put(rebind, orig, 0)}

        computed ->
          sentinel = sentinel_base + k
          {replace_term(result_type_term, computed, {:var, sentinel}), Map.put(rebind, sentinel, 0)}
      end

    body = generalize(result_type_term, rebind, k + 1, 0)

    (index_types ++ [scrut_type])
    |> Enum.reverse()
    |> Enum.reduce(body, fn type, acc -> {:lam, Cure.Core.Grade.unrestricted(), type, acc} end)
  end

  # Step 3b detection. Return `nil` unless the scrutinee has EXACTLY ONE computed
  # (non-variable) index position whose term is mentioned by at least one sibling
  # in scope (a context variable other than the scrutinee). In that case return
  # `%{pos, idx_term, idx_type_term, siblings}` describing the equation to carry.
  # Restricted to a single computed index with a closed index type (SList, Dec —
  # the FRP carriers); anything else falls back to the plain 3a motive (the kernel
  # then rejects an un-transportable sibling, never mis-accepts it).
  defp detect_carried_index(index_tele, idx_terms, scrut_term, names, ctx, env) do
    computed =
      idx_terms
      |> Enum.with_index()
      |> Enum.reject(fn {t, _pos} -> invertible_index?(t) end)

    with [{idx_term, pos}] <- computed,
         {_name, idx_type_term} <- Enum.at(index_tele, pos),
         true <- MapSet.size(free_indices(idx_type_term, 0)) == 0,
         [_ | _] = siblings <- collect_index_siblings(scrut_term, idx_term, names, ctx, env) do
      %{pos: pos, idx_term: idx_term, idx_type_term: idx_type_term, siblings: siblings}
    else
      _ -> nil
    end
  end

  # A computed index that is a constructor spine over variables (`S(m)`,
  # `Cons(h, t)`) is INVERTIBLE by ordinary index refinement — matching unifies the
  # scrutinee's constructor index with each branch constructor's index directly
  # (Idris's `yr : Vect m a` in the `(::)` branch). It needs no carried equation:
  # the plain 3a motive handles it, and forcing the carried-eq transport onto a
  # sibling with a fresh-variable constructor index (e.g. `S(n')` for a bound tail
  # length) spuriously fails `:branch_type` even when the branch body never uses
  # that sibling. Only a NON-invertible computed index — a defined-function
  # application like `app(p, q)`, whose head is not a constructor and cannot be
  # inverted — genuinely needs the carried equation (see `carried_index_sibling_test`).
  # A bare variable is trivially invertible (and was already excluded before).
  defp invertible_index?({:ctor, _name, args}), do: Enum.all?(args, &invertible_index?/1)
  defp invertible_index?({:var, _}), do: true
  defp invertible_index?(_), do: false

  # Siblings whose (reified) type mentions the computed index term `idx_term`,
  # EXCLUDING the scrutinee itself (its own type mentions the index but it is the
  # thing being eliminated, not transported). Innermost-first, like
  # `collect_with_siblings`. Interdependent siblings are not pre-screened here; a
  # transport that would be ill-typed is caught by the kernel's re-check.
  defp collect_index_siblings(scrut_term, idx_term, names, ctx, env) do
    depth = Context.length(ctx)

    scrut_idx =
      case scrut_term do
        {:var, i} -> i
        _ -> -1
      end

    names
    |> Enum.with_index()
    |> Enum.flat_map(fn {name, i} ->
      if is_binary(name) and i != scrut_idx do
        type_term = resplit_data(Quote.reify(Context.lookup(ctx, i), depth), env)

        if contains_term?(type_term, idx_term),
          do: [%{name: name, index: i, type_term: type_term}],
          else: []
      else
        []
      end
    end)
    |> Enum.sort_by(& &1.index, :desc)
  end

  # Inject the carried index equation into a 3a motive `λj̄. λx. G'`, yielding
  # `λj̄. λx. Eq(T, idx, jₚₒₛ) -> G'`. Under the k+1 motive binders (indices j̄
  # then scrutinee x), `jₚₒₛ` sits at de Bruijn `k - pos`; `idx`/`T` are shifted
  # from the outer frame past all k+1 binders; `G'` shifts +1 past the new Eq
  # binder.
  defp wrap_motive_carried_eq(motive, k, %{pos: pos, idx_term: idx_term, idx_type_term: idx_type_term}) do
    {binder_types, body} = peel_lams(motive, k + 1, [])

    eq_dom =
      mk_eq(Subst.shift(idx_type_term, k + 1, 0), Subst.shift(idx_term, k + 1, 0), {:var, k - pos})

    new_body = {:pi, Cure.Core.Grade.unrestricted(), eq_dom, Subst.shift(body, 1, 0)}

    Enum.reduce(binder_types, new_body, fn type, acc -> {:lam, Cure.Core.Grade.unrestricted(), type, acc} end)
  end

  # Peel `n` leading `{:lam, Cure.Core.Grade.unrestricted(), dom, body}` binders, returning `{doms_outermost_first,
  # inner_body}`.
  defp peel_lams(body, 0, acc), do: {Enum.reverse(acc), body}
  defp peel_lams({:lam, _g, dom, body}, n, acc), do: peel_lams(body, n - 1, [dom | acc])

  # Rewrite the free variables of `term` for placement under the motive's k+1
  # binders (`depth` counts binders entered *within* term): a free variable that
  # names a scrutinee index becomes its motive binder (`rebind`); every other
  # free variable is shifted past the new binders (`shift`).
  defp generalize({:var, i}, _rebind, _shift, depth) when i < depth, do: {:var, i}

  defp generalize({:var, i}, rebind, shift, depth) do
    orig = i - depth

    case Map.fetch(rebind, orig) do
      {:ok, binder} -> {:var, binder + depth}
      :error -> {:var, orig + shift + depth}
    end
  end

  defp generalize({:pi, _g, d, c}, rb, s, depth),
    do: {:pi, Cure.Core.Grade.unrestricted(), generalize(d, rb, s, depth), generalize(c, rb, s, depth + 1)}

  defp generalize({:lam, _g, d, b}, rb, s, depth),
    do: {:lam, Cure.Core.Grade.unrestricted(), generalize(d, rb, s, depth), generalize(b, rb, s, depth + 1)}

  defp generalize({:app, f, a}, rb, s, depth),
    do: {:app, generalize(f, rb, s, depth), generalize(a, rb, s, depth)}

  defp generalize({:data, n, ps, is}, rb, s, depth),
    do: {:data, n, Enum.map(ps, &generalize(&1, rb, s, depth)), Enum.map(is, &generalize(&1, rb, s, depth))}

  defp generalize({:ctor, n, args}, rb, s, depth),
    do: {:ctor, n, Enum.map(args, &generalize(&1, rb, s, depth))}

  defp generalize({:case, scr, m, brs}, rb, s, depth),
    do:
      {:case, generalize(scr, rb, s, depth), generalize(m, rb, s, depth),
       Enum.map(brs, fn {c, ar, b} -> {c, ar, generalize(b, rb, s, depth + ar)} end)}

  defp generalize(leaf, _rb, _s, _depth), do: leaf

  # Coverage/discharge pass (spec §5). Partition the surface arms, then emit a
  # branch for EVERY declared constructor of `dname` — matched arms elaborate
  # their bodies; omitted or explicit-impossible constructors are discharged
  # (verdict :impossible ⇒ {:absurd} placeholder body) or rejected. The kernel
  # then re-checks and re-discharges the assembled {:case,…} independently.
  # `idx_vals` are the scrutinee's index VALUES (for branch_unify); each
  # branch's expected type comes from the kernel's branch_unify verdict subst
  # plus the scrutinee-value refinement (see elaborate_matched_branch).
  #
  # Returns `{:ok, branches, join}`. `join` is `nil`, or `{join_ty, join_val}` —
  # the JOIN POINT (plan slice 4c): the catch-all body, elaborated ONCE, which
  # `wrap_join/2` binds around the assembled `:case`. Branches that would have
  # re-elaborated it carry the `@join_marker` body until then.
  defp elaborate_branches(
         arms,
         names,
         ctx,
         env,
         dname,
         idx_vals,
         param_vals,
         scrut_term,
         result_type_term,
         carried,
         motive
       ) do
    with {:ok, {arm_map, default}} <- partition_arms(arms, ctx, env, dname) do
      sig = Context.signature(ctx)
      cnames = sig |> Inductive.ctors_of(dname) |> Enum.map(& &1.name)

      known_value =
        case Eval.eval(scrut_term, Context.env(ctx)) do
          {:vctor, _cname, _args} = value -> value
          _ -> nil
        end

      verdicts =
        Map.new(cnames, fn cname ->
          verdict = Kernel.branch_unify(ctx, dname, cname, idx_vals, param_vals)

          verdict =
            case known_value do
              {:vctor, known_ctor, _args} when cname != known_ctor -> :impossible
              {:vctor, ^cname, args} -> merge_known_ctor_args(verdict, args, Context.length(ctx))
              _ -> verdict
            end

          {cname, verdict}
        end)

      uncovered =
        Enum.filter(cnames, fn c ->
          not Map.has_key?(arm_map, c) and Map.get(verdicts, c) != :impossible
        end)

      join? = join_point?(default, uncovered, carried, idx_vals, motive)

      branches =
        cnames
        |> Enum.reduce_while({:ok, []}, fn cname, {:ok, acc} ->
          verdict = Map.fetch!(verdicts, cname)

          case Map.get(arm_map, cname) do
            {:matched, pattern, body_expr} ->
              case elaborate_matched_branch(
                     verdict,
                     pattern,
                     body_expr,
                     names,
                     ctx,
                     env,
                     param_vals,
                     scrut_term,
                     result_type_term,
                     carried
                   ) do
                {:ok, branch} -> {:cont, {:ok, acc ++ [branch]}}
                {:error, _} = err -> {:halt, err}
              end

            {:impossible_marked, _pattern} ->
              if verdict == :impossible do
                # omit (K4 §H)
                {:cont, {:ok, acc}}
              else
                {:halt, {:error, {:reachable_impossible, cname}}}
              end

            nil ->
              # omitted constructor — discharge if impossible, else covered by a
              # variable/wildcard catch-all (`x -> …`), else a genuine gap.
              cond do
                verdict == :impossible ->
                  # omit (K4 §H)
                  {:cont, {:ok, acc}}

                # The join point covers this constructor: leave a marker whose body
                # `wrap_join/2` fills with `{:app, j, scrut}` once it knows the
                # let-binder's depth. The catch-all body is elaborated exactly once,
                # below, instead of once per uncovered constructor.
                join? ->
                  arity = length(Inductive.get_ctor(env, cname).args)
                  {:cont, {:ok, acc ++ [{cname, arity, @join_marker}]}}

                default != nil ->
                  case elaborate_default_branch(
                         verdict,
                         cname,
                         default,
                         names,
                         ctx,
                         env,
                         param_vals,
                         scrut_term,
                         result_type_term,
                         carried
                       ) do
                    {:ok, branch} -> {:cont, {:ok, acc ++ [branch]}}
                    {:error, _} = err -> {:halt, err}
                  end

                true ->
                  {:halt, {:error, {:missing_branch, cname}}}
              end
          end
        end)

      with {:ok, brs} <- branches,
           {:ok, join} <- elaborate_join(join?, default, names, ctx, env, motive) do
        {:ok, brs, join}
      end
    end
  end

  defp merge_known_ctor_args(:impossible, _args, _depth), do: :impossible

  defp merge_known_ctor_args(verdict, args, depth) do
    arity = length(args)

    value_subst =
      args
      |> Enum.with_index()
      |> Map.new(fn {value, p} ->
        ctor_key = arity - 1 - p
        shifted = value |> Quote.reify(depth) |> Cure.Core.Term.shift(arity, 0)

        case shifted do
          {:var, outer_key} -> {outer_key, {:var, ctor_key}}
          closed -> {ctor_key, closed}
        end
      end)

    index_subst =
      case verdict do
        {:solved, subst} -> subst
        :trivial -> %{}
      end

    {:solved, Map.merge(index_subst, value_subst)}
  end

  # --- as-pattern desugaring (parity #4) -------------------------------------
  #
  # `name @ <pattern>` binds the whole matched value to `name` as well as
  # destructuring it. Inline `{:as_pattern, _, [name, sub]}` nodes may sit at the
  # arm's top level OR nested inside constructor arguments (`Cons(h, t @ …)`).
  # Strip them out of the pattern tree and, since a pattern and its
  # value-reconstruction share the same surface shape, substitute each `name` by
  # its (cleaned) sub-pattern in the body — the cleaned pattern then flows through
  # nested-pattern lowering unchanged.
  defp desugar_as_patterns(arms) do
    Enum.reduce_while(arms, {:ok, []}, fn {:match_arm, meta, body} = arm, {:ok, acc} ->
      pattern = Keyword.fetch!(meta, :pattern)
      {clean, subs} = strip_as_patterns(pattern)

      cond do
        subs == [] ->
          {:cont, {:ok, acc ++ [arm]}}

        binds_any?(single_body(body), Enum.map(subs, &elem(&1, 0))) ->
          {:halt, {:error, {:unsupported_pattern, :shadowed_as}}}

        true ->
          b2 =
            Enum.reduce(subs, single_body(body), fn {name, recon}, b ->
              subst_surface_var(b, name, recon)
            end)

          {:cont, {:ok, acc ++ [{:match_arm, Keyword.put(meta, :pattern, clean), b2}]}}
      end
    end)
  end

  # Strip inline as-patterns from a pattern tree → `{cleaned_pattern, [{name,
  # reconstruction}]}`. The reconstruction is the cleaned sub-pattern (valid as an
  # expression). Handles nesting: `w @ S(t @ Z())` yields `w ↦ S(Z())`, `t ↦ Z()`.
  defp strip_as_patterns({:as_pattern, _m, [name, sub]}) do
    {clean_sub, subs} = strip_as_patterns(sub)
    {clean_sub, [{name, strip_named_implicits(clean_sub)} | subs]}
  end

  defp strip_as_patterns({:function_call, m, args}) do
    {clean_args, subs} =
      Enum.map_reduce(args, [], fn a, acc ->
        {ca, s} = strip_as_patterns(a)
        {ca, acc ++ s}
      end)

    {{:function_call, m, clean_args}, subs}
  end

  defp strip_as_patterns(other), do: {other, []}

  # --- tuple sub-patterns inside a constructor argument (parity #4) -----------
  #
  # `A(%[x, y]) -> body` destructures a Σ-typed field. Replace each tuple
  # constructor-argument with a fresh `$tup_i` binder (the `$` prefix cannot clash
  # with a user identifier) and substitute the tuple's variables by projections of
  # that binder in the body — so `A(%[x, y]) -> body` becomes
  # `A($tup_0) -> body[x ↦ $tup_0.1, y ↦ $tup_0.2]`, which then flows through the
  # ordinary all-variable constructor path. Only direct constructor arguments are
  # rewritten; a top-level tuple pattern is left for `try_tuple_match`, and a tuple
  # nested inside a *nested* constructor falls through to that path's clean error.
  defp desugar_tuple_args(arms) do
    Enum.reduce_while(arms, {:ok, []}, fn {:match_arm, meta, body} = arm, {:ok, acc} ->
      case strip_tuple_args_in_ctor(Keyword.fetch!(meta, :pattern)) do
        {:ok, _clean, []} ->
          {:cont, {:ok, acc ++ [arm]}}

        {:ok, clean, subs} ->
          b = single_body(body)

          if binds_any?(b, Enum.map(subs, &elem(&1, 0))) do
            {:halt, {:error, {:unsupported_pattern, :shadowed_tuple_arg}}}
          else
            b2 = Enum.reduce(subs, b, fn {n, r}, acc_b -> subst_surface_var(acc_b, n, r) end)
            {:cont, {:ok, acc ++ [{:match_arm, Keyword.put(meta, :pattern, clean), b2}]}}
          end

        {:error, _} = err ->
          {:halt, err}
      end
    end)
  end

  defp strip_tuple_args_in_ctor({:function_call, m, args}) do
    args
    |> Enum.with_index()
    |> Enum.reduce_while({:ok, [], []}, fn {arg, i}, {:ok, cargs, subs} ->
      case arg do
        {:tuple, _tm, [_, _ | _] = elems} ->
          fresh_var = {:variable, [], "$tup_" <> Integer.to_string(i)}

          case tuple_subs(elems, fresh_var) do
            {:ok, s} -> {:cont, {:ok, cargs ++ [fresh_var], subs ++ s}}
            {:error, _} = err -> {:halt, err}
          end

        _ ->
          {:cont, {:ok, cargs ++ [arg], subs}}
      end
    end)
    |> case do
      {:ok, cargs, subs} -> {:ok, {:function_call, m, cargs}, subs}
      {:error, _} = err -> err
    end
  end

  defp strip_tuple_args_in_ctor(other), do: {:ok, other, []}

  # --- tuple-scrutinee matching (parity #6) ----------------------------------
  #
  # `match %[e₀, e₁, …] | %[p₀, p₁, …] -> body` (simultaneous / Idris'
  # `case (e₀, e₁) of`) is desugared, ONE column at a time, into a nested
  # single-scrutinee match `match e₀ | p₀ -> match %[e₁, …] | %[p₁, …] -> body`.
  # The remaining columns re-enter this same path (their scrutinee is a smaller
  # tuple, or the bare element when only one column is left), so the whole tree
  # is built by re-entry. Each first-column constructor keeps its argument
  # patterns inline, so `desugar_nested_arms` still lowers any nested args, and
  # the inner match on an index-refined scrutinee elides the impossible sibling
  # constructors (e.g. two `Vector`s that share index `n` cannot be `empty`/
  # `prepend`), exactly as the hand-written nested form relies on.
  #
  # Fires only for a tuple scrutinee (≥2 elems) whose arms are ALL guardless
  # tuple patterns of matching arity, with DISTINCT constructor heads in the
  # first column. Anything else (non-tuple scrutinee, a variable/wildcard or a
  # repeated head in the first column) is returned UNCHANGED, so ordinary
  # matches are untouched and still-unsupported shapes reach their existing
  # clean rejection rather than being miscompiled.
  defp desugar_tuple_scrutinee({:tuple, _meta, elems} = scrut, arms)
       when length(elems) >= 2 do
    with {:ok, rows} <- tuple_scrutinee_rows(elems, arms),
         {:ok, new_scrut, new_arms} <- split_first_tuple_column(elems, rows) do
      {new_scrut, new_arms}
    else
      _ -> {scrut, arms}
    end
  end

  defp desugar_tuple_scrutinee(scrut, arms), do: {scrut, arms}

  # Validate every arm is a guardless tuple pattern of the scrutinee's arity;
  # return the rows as `{[col-patterns], body-expr}`.
  defp tuple_scrutinee_rows(elems, arms) do
    n = length(elems)

    Enum.reduce_while(arms, {:ok, []}, fn
      {:match_arm, meta, body}, {:ok, acc} ->
        case Keyword.fetch!(meta, :pattern) do
          {:tuple, _tm, pats} when length(pats) == n ->
            if Keyword.has_key?(meta, :guard) do
              {:halt, :not_applicable}
            else
              {:cont, {:ok, acc ++ [{pats, single_body(body)}]}}
            end

          _ ->
            {:halt, :not_applicable}
        end

      _other, _acc ->
        {:halt, :not_applicable}
    end)
  end

  # Split the first column: outer scrutinee `e₀`, one outer arm per row keeping
  # its first-column pattern, whose body matches the remaining columns. Requires
  # all first-column patterns to be constructors with distinct heads (disjoint,
  # so first-match order is preserved and no row is shadowed).
  defp split_first_tuple_column([e0 | erest], rows) do
    col0 = Enum.map(rows, fn {[p0 | _], _} -> p0 end)

    heads =
      Enum.map(col0, fn
        {:function_call, fm, _} -> {:ok, Keyword.fetch!(fm, :name)}
        _ -> :error
      end)

    cond do
      not Enum.all?(heads, &match?({:ok, _}, &1)) ->
        :not_applicable

      not distinct?(Enum.map(heads, fn {:ok, h} -> h end)) ->
        :not_applicable

      true ->
        arms =
          Enum.map(rows, fn {[p0 | prest], body} ->
            {:match_arm, [pattern: p0], [build_inner_tuple_match(erest, prest, body)]}
          end)

        {:ok, e0, arms}
    end
  end

  # The remaining columns become the inner match. A single remaining column is a
  # bare single-scrutinee match; two or more re-enter `desugar_tuple_scrutinee`
  # as a smaller tuple scrutinee.
  defp build_inner_tuple_match([e1], [p1], body) do
    {:pattern_match, [], [e1, {:match_arm, [pattern: p1], [body]}]}
  end

  defp build_inner_tuple_match(erest, prest, body) when length(erest) >= 2 do
    {:pattern_match, [], [{:tuple, [], erest}, {:match_arm, [pattern: {:tuple, [], prest}], [body]}]}
  end

  defp distinct?(list), do: length(Enum.uniq(list)) == length(list)

  # --- tuple-pattern matching (parity #4) ------------------------------------
  #
  # A Σ/pair is irrefutable — a single tuple-pattern arm `%[x, y] -> body` just
  # destructures. Lower it to the (already-supported) projections `.1`/`.2`:
  # `body[x ↦ p.1, y ↦ p.2]`, elaborated directly. Restricted to a VARIABLE
  # scrutinee (so the projections are cheap and re-evaluation-free) and a flat
  # 2-element tuple of variables/wildcards; anything else falls through to the
  # ordinary (`{:vdata}`) dispatch and its clean error.
  defp try_tuple_match({:variable, _sm, _sn} = scrut, [{:match_arm, meta, body}], expected, names, ctx, env) do
    case Keyword.fetch!(meta, :pattern) do
      {:tuple, _tm, [_, _ | _] = elems} ->
        with {:ok, subs} <- tuple_subs(elems, scrut) do
          b = single_body(body)

          if binds_any?(b, Enum.map(subs, &elem(&1, 0))) do
            {:error, {:unsupported_pattern, :shadowed_tuple}}
          else
            b2 = Enum.reduce(subs, b, fn {n, r}, acc -> subst_surface_var(acc, n, r) end)
            elaborate_expr_checked(b2, expected, names, ctx, env)
          end
        end

      _ ->
        :not_applicable
    end
  end

  defp try_tuple_match(_scrut, _arms, _expected, _names, _ctx, _env), do: :not_applicable

  # A single variable/wildcard arm ignores the scrutinee's structure — an
  # irrefutable bind valid at ANY scrutinee type (Σ, primitive, data), not just
  # `{:vdata}`. The scrutinee is already elaborated (so it is well-typed) before
  # this runs; `_` discards it and a name binds the whole value. This lets a
  # pair/primitive scrutinee carry a lone catch-all without the vdata dispatch
  # rejecting it as `:match_scrutinee_not_data`.
  defp try_trivial_match(scrut_expr, [{:match_arm, meta, body}], expected, names, ctx, env) do
    case Keyword.fetch!(meta, :pattern) do
      {:variable, _m, "_"} ->
        elaborate_expr_checked(single_body(body), expected, names, ctx, env)

      {:variable, _m, name} ->
        b = single_body(body)

        cond do
          # A complex scrutinee would be duplicated by substitution; leave those to
          # the ordinary path (which binds via the case machinery).
          not match?({:variable, _sm, _sn}, scrut_expr) -> :not_applicable
          binds_any?(b, [name]) -> {:error, {:unsupported_pattern, :shadowed_catchall}}
          true -> elaborate_expr_checked(subst_surface_var(b, name, scrut_expr), expected, names, ctx, env)
        end

      _ ->
        :not_applicable
    end
  end

  defp try_trivial_match(_scrut, _arms, _expected, _names, _ctx, _env), do: :not_applicable

  # A `when` guard on a variable/catch-all pattern desugars to a `:case`-on-Bool
  # chain (`bool_case/5`): `match n | x when g -> a | x -> b` becomes
  # `case g[x↦n] of True -> a[x↦n] | False -> b`, each guarded arm testing its
  # guard and falling through (the `ff` branch) to the remaining arms. The chain
  # must end in an *unguarded* catch-all — the fall-through when every guard is
  # false — unless the untrusted Z3 lint proves the guards exhaustive, in which
  # case the final guarded arm becomes that catch-all (§2.3a); otherwise a
  # still-guarded final arm is non-exhaustive and rejected. Restricted to a
  # variable scrutinee so the substituted `n` is not duplicated-with-effects;
  # richer patterns error rather than silently drop the guard. Lowers through
  # `bool_case/5`; no kernel change. Returns `:not_applicable` only when NO arm
  # is guarded.
  defp try_guard_match(scrut_expr, arms, expected, names, ctx, env) do
    cond do
      not Enum.any?(arms, &guarded_arm?/1) ->
        :not_applicable

      # A variable scrutinee is substituted into the guard chain as-is: only a
      # variable is duplicated (no recomputation), so the surface path is safe.
      match?({:variable, _, _}, scrut_expr) ->
        guard_chain(scrut_expr, arms, expected, names, ctx, env, [])

      # A non-variable scrutinee would be DUPLICATED (and recomputed) by surface
      # substitution across the guard chain. Bind it ONCE under a fresh Core
      # λ and run the chain over the binder VARIABLE, so every substitution is of a
      # variable — a real `(λ s:T. <chain over s>) e` β-redex the kernel reduces
      # with `e` evaluated once. Closes the `:complex_scrutinee` reach gap.
      true ->
        bind_once_guard(scrut_expr, arms, expected, names, ctx, env)
    end
  end

  # Bind `scrut_expr` once under a fresh λ, then elaborate the guard chain with the
  # fresh binder as a (variable) scrutinee. The outer goal `expected` never mentions
  # the fresh binder, so it is shifted under the binder and the β-redex checks back
  # against `expected` exactly. The fresh name is depth-unique (`$gscrut<n>`) so a
  # nested non-variable guarded match binds a distinct name.
  defp bind_once_guard(scrut_expr, arms, expected, names, ctx, env) do
    with {:ok, scrut_core, scrut_type} <- elaborate_expr_typed(scrut_expr, names, ctx, env) do
      fresh = "$gscrut" <> Integer.to_string(Context.length(ctx))
      dom = Quote.reify(scrut_type, Context.length(ctx))
      ctx1 = Context.extend(ctx, scrut_type)
      names1 = [fresh | names]
      expected1 = Subst.shift(expected, 1, 0)

      with {:ok, chain} <-
             guard_chain({:variable, [], fresh}, arms, expected1, names1, ctx1, env, []) do
        {:ok, {:app, {:lam, Cure.Core.Grade.unrestricted(), dom, chain}, scrut_core}}
      end
    end
  end

  defp guarded_arm?({:match_arm, meta, _body}), do: Keyword.has_key?(meta, :guard)

  # The final arm closes the chain: it must be an unguarded catch-all — unless
  # the untrusted Z3 lint proves the chain's guards exhaustive (spec
  # 2026-07-08-guard-coverage-lint §2.3a), in which case the final guarded arm
  # IS the catch-all: its provably-true test is elided and its body goes
  # through the ordinary bind_catchall_body path, so the kernel re-checks
  # exactly the term an unguarded catch-all would have produced. Every lint
  # failure (unproven / untranslatable / Z3 unavailable) reproduces today's
  # rejection byte-for-byte — including when the final guard itself fails to
  # elaborate, which was never reached pre-lint.
  defp guard_chain(scrut_expr, [{:match_arm, meta, body}], expected, names, ctx, env, acc) do
    case Keyword.get(meta, :guard) do
      nil ->
        bind_catchall_body(
          scrut_expr,
          Keyword.fetch!(meta, :pattern),
          single_body(body),
          expected,
          names,
          ctx,
          env
        )

      guard ->
        pat = Keyword.fetch!(meta, :pattern)

        elaborated =
          with {:ok, guard_expr} <- guard_bind(scrut_expr, pat, guard) do
            elaborate_expr_checked(guard_expr, bool_type_term(Context.signature(ctx)), names, ctx, env)
          end

        case elaborated do
          {:ok, test} ->
            maybe_warn_shadowed(test, acc, ctx)

            if GuardLint.prove_exhaustive(acc ++ [test], ctx) == :proven do
              bind_catchall_body(scrut_expr, pat, single_body(body), expected, names, ctx, env)
            else
              {:error, {:unsupported_guard, :non_exhaustive}}
            end

          _error ->
            {:error, {:unsupported_guard, :non_exhaustive}}
        end
    end
  end

  # A guarded arm becomes a `:case` on the inductive Bool (`bool_case/5`); an
  # unguarded catch-all before the end shadows every later arm and closes the
  # chain early.
  defp guard_chain(scrut_expr, [{:match_arm, meta, body} | rest], expected, names, ctx, env, acc) do
    pat = Keyword.fetch!(meta, :pattern)

    case Keyword.get(meta, :guard) do
      nil ->
        bind_catchall_body(scrut_expr, pat, single_body(body), expected, names, ctx, env)

      guard ->
        with {:ok, guard_expr} <- guard_bind(scrut_expr, pat, guard),
             {:ok, body_expr} <- guard_bind(scrut_expr, pat, single_body(body)),
             {:ok, test} <-
               elaborate_expr_checked(guard_expr, bool_type_term(Context.signature(ctx)), names, ctx, env),
             {:ok, tt} <- elaborate_expr_checked(body_expr, expected, names, ctx, env),
             # Warn for THIS arm before recursing into the later ones. The check needs only
             # `test` and `acc`, both bound here; running it after the recursion meant every
             # later arm had already recorded its own warning, so `GuardLint.warnings/0` —
             # which restores insertion order by reversing a prepended list — handed back a
             # chain's shadow warnings in descending arm index.
             :ok <- maybe_warn_shadowed(test, acc, ctx),
             {:ok, ff} <- guard_chain(scrut_expr, rest, expected, names, ctx, env, acc ++ [test]) do
          {:ok, bool_case(test, expected, tt, ff, ctx)}
        end
    end
  end

  # Dead-arm lint (§2.1): a guard implied by the disjunction of the guards
  # before it can never fire. Warning only — elaboration is unaffected. The
  # index is the guard's 0-based position among the chain's guarded arms.
  defp maybe_warn_shadowed(_test, [], _ctx), do: :ok

  defp maybe_warn_shadowed(test, acc, ctx) do
    if GuardLint.shadowed?(test, acc, ctx),
      do: GuardLint.record_warning({:guard_shadowed, length(acc)})

    :ok
  end

  # Bind a catch-all pattern's variable to the scrutinee and check the body: `_`
  # discards, a name substitutes the (variable) scrutinee expression. A non-
  # variable pattern under a guarded match is out of this slice's scope.
  defp bind_catchall_body(_scrut, {:variable, _m, "_"}, body, expected, names, ctx, env),
    do: elaborate_expr_checked(body, expected, names, ctx, env)

  defp bind_catchall_body(scrut_expr, {:variable, _m, name}, body, expected, names, ctx, env) do
    cond do
      not match?({:variable, _sm, _sn}, scrut_expr) -> {:error, {:unsupported_guard, :complex_scrutinee}}
      binds_any?(body, [name]) -> {:error, {:unsupported_guard, :shadowed}}
      true -> elaborate_expr_checked(subst_surface_var(body, name, scrut_expr), expected, names, ctx, env)
    end
  end

  defp bind_catchall_body(_scrut, _pat, _body, _expected, _names, _ctx, _env),
    do: {:error, {:unsupported_guard, :non_catchall_pattern}}

  # Substitute the pattern variable with the (variable) scrutinee in a guard or
  # body expression, guarding against complex scrutinees and shadow-capture.
  defp guard_bind(_scrut, {:variable, _m, "_"}, expr), do: {:ok, expr}

  defp guard_bind(scrut_expr, {:variable, _m, name}, expr) do
    cond do
      not match?({:variable, _sm, _sn}, scrut_expr) -> {:error, {:unsupported_guard, :complex_scrutinee}}
      binds_any?(expr, [name]) -> {:error, {:unsupported_guard, :shadowed}}
      true -> {:ok, subst_surface_var(expr, name, scrut_expr)}
    end
  end

  defp guard_bind(_scrut, _pat, _expr), do: {:error, {:unsupported_guard, :non_catchall_pattern}}

  # Literal patterns on a PRIMITIVE scrutinee (Int/Bool/Float) desugar to a chain
  # of `:case`-on-Bool decisions (`bool_case/5`) — there is no `:vdata` to
  # dispatch on. `match n | 0 -> a | _ -> b` becomes
  # `case (n == 0) of True -> a | False -> b`; `match b | true -> t | false ->
  # f` becomes `case b of True -> t | False -> f`. The already-elaborated Core scrutinee is reused
  # in each equality test (no surface duplication), and the kernel re-checks the
  # assembled chain. Returns `:not_applicable` for a non-primitive scrutinee or
  # arms that are not a clean literal/catch-all list (the ordinary path handles it).
  defp try_literal_match(scrut_expr, arms, scrut_term, scrut_type, expected, names, ctx, env) do
    case primitive_scrut_kind(scrut_type, Context.signature(ctx)) do
      {:ok, prim} ->
        pats = Enum.map(arms, fn {:match_arm, m, b} -> {Keyword.fetch!(m, :pattern), single_body(b)} end)

        cond do
          prim == :bool and bool_exhaustive?(pats) ->
            {tb, fb} = bool_bodies(pats)

            with {:ok, t_core} <- elaborate_match_body(tb, expected, names, ctx, env),
                 {:ok, f_core} <- elaborate_match_body(fb, expected, names, ctx, env) do
              {:ok, bool_case(scrut_term, expected, t_core, f_core, ctx)}
            end

          literal_chain?(pats, prim) ->
            literal_chain(scrut_expr, scrut_term, scrut_type, prim, pats, expected, names, ctx, env)

          true ->
            :not_applicable
        end

      :error ->
        :not_applicable
    end
  end

  # The Core **term** for the canonical Bool inductive (the term-level counterpart
  # of Kernel.bool_type_value/1); `eval(bool_type_term(sig), _) == bool_type_value(sig)`.
  defp bool_type_term(sig) do
    fid = Inductive.builtin(sig, :bool) || raise "builtin :bool not seeded (bootstrap/load-order bug)"
    {:data, fid, [], []}
  end

  # Lower a two-way Bool decision to a `:case` on the inductive Bool, with the
  # constant motive `λ_:Bool. motive_body_type` (both branches share the type).
  # The kernel re-checks the assembled `:case`, so nothing built here is trusted.
  defp bool_case(scrut_term, motive_body_type, tt, ff, ctx) do
    sig = Context.signature(ctx)
    bool_ty = bool_type_term(sig)
    true_ctor = resolve_ctor_key(sig, :True)
    false_ctor = resolve_ctor_key(sig, :False)
    motive = {:lam, Cure.Core.Grade.unrestricted(), bool_ty, Cure.Core.Term.shift(motive_body_type, 1, 0)}
    {:case, scrut_term, motive, [{true_ctor || :True, 0, tt}, {false_ctor || :False, 0, ff}]}
  end

  # A Bool scrutinee is now the inductive family (`{:vdata, :Bool, []}`), resolved
  # via the registry; Int/Float stay primitive type-values.
  defp primitive_scrut_kind({:vint_type}, _sig), do: {:ok, :int}
  defp primitive_scrut_kind({:vfloat_type}, _sig), do: {:ok, :float}

  defp primitive_scrut_kind({:vdata, fid, []}, sig) do
    if fid == Inductive.builtin(sig, :bool), do: {:ok, :bool}, else: :error
  end

  # An applied `Bounded(n)` (Char's underlying type) is an indexed family that
  # erases to a native int. It is NOT one of the monomorphic int/float/bool eq
  # twins, so equality is the polymorphic `struct_eq` — but a literal chain over
  # it lowers exactly like the primitive chains. Arithmetic on it stays rejected
  # (the arithmetic `build_binop` clause has no `:bounded` arm), preserving the
  # `0 ≤ k < n` invariant.
  defp primitive_scrut_kind({:vdata, fid, [_bound]}, sig) do
    if fid == Inductive.builtin(sig, :bounded), do: {:ok, :bounded}, else: :error
  end

  defp primitive_scrut_kind(_type, _sig), do: :error

  defp bool_exhaustive?([{p1, _}, {p2, _}]),
    do: Enum.sort([bool_pat_value(p1), bool_pat_value(p2)]) == [false, true]

  defp bool_exhaustive?(_), do: false

  defp bool_pat_value({:literal, _m, v}) when is_boolean(v), do: v
  defp bool_pat_value(_), do: nil

  defp bool_bodies([{p1, b1}, {_p2, b2}]),
    do: if(bool_pat_value(p1) == true, do: {b1, b2}, else: {b2, b1})

  defp elaborate_match_body(body, expected, names, ctx, env) do
    if effect_goal?(expected, ctx),
      do: elaborate_effect_branch(body, expected, names, ctx, env),
      else: elaborate_expr_checked(body, expected, names, ctx, env)
  end

  # A literal chain is zero or more literal arms of the scrutinee's primitive type
  # followed by a single variable/wildcard catch-all.
  defp literal_chain?(pats, prim) when length(pats) >= 1 do
    {lits, [{last_pat, _}]} = Enum.split(pats, length(pats) - 1)
    Enum.all?(lits, fn {p, _} -> literal_of?(p, prim) or pin_var?(p) end) and catchall_pat?(last_pat)
  end

  defp literal_chain?(_pats, _prim), do: false

  # A pin arm `^x` on a primitive scrutinee behaves like a literal arm whose
  # compared value is the current value of the bound variable `x` (an equality
  # constraint, not a fresh binding). It always needs a trailing catch-all — a pin
  # is never known to be exhaustive.
  defp pin_var?({:pin, _m, [{:variable, _vm, _name}]}), do: true
  defp pin_var?(_p), do: false

  defp literal_of?({:literal, _m, v}, :int), do: is_integer(v)
  defp literal_of?({:literal, _m, v}, :float), do: is_float(v)
  defp literal_of?({:literal, _m, v}, :bool), do: is_boolean(v)
  # A char literal `'a'` carries its integer codepoint (subtype `:char`).
  defp literal_of?({:literal, _m, v}, :bounded), do: is_integer(v)
  defp literal_of?(_p, _prim), do: false

  defp catchall_pat?({:variable, _m, _name}), do: true
  defp catchall_pat?(_p), do: false

  defp lit_core(v, :int), do: {:int_lit, v}
  defp lit_core(v, :float), do: {:float_lit, v}
  defp lit_core(v, :bounded), do: {:bounded_lit, v}

  defp lit_core(v, :bool, env), do: {:ctor, resolve_ctor_key(env, if(v, do: :True, else: :False)), []}
  defp lit_core(v, prim, _env), do: lit_core(v, prim)

  # The final (catch-all) arm: the chain's innermost default branch.
  defp literal_chain(scrut_expr, _scrut_term, _scrut_type, _prim, [{pat, body}], expected, names, ctx, env) do
    case pat do
      {:variable, _m, "_"} ->
        elaborate_match_body(body, expected, names, ctx, env)

      {:variable, _m, name} ->
        cond do
          not match?({:variable, _sm, _sn}, scrut_expr) -> :not_applicable
          binds_any?(body, [name]) -> {:error, {:unsupported_pattern, :shadowed_literal_catchall}}
          true -> elaborate_match_body(subst_surface_var(body, name, scrut_expr), expected, names, ctx, env)
        end
    end
  end

  # A literal arm: test the scrutinee against the literal (a type-directed
  # equality global spine yielding the inductive Bool — K2 phase 2), take this
  # body if equal, else recurse on the rest — the test scrutinised by a `:case`
  # on Bool. `prim` (the scrutinee's primitive kind, already in scope) picks the
  # monomorphic twin; a Bool literal chain uses the Std.Bool `eq` case-def.
  # A `:bounded` (Char) chain uses the polymorphic `struct_eq` — `scrut_type`
  # supplies its erased type argument — instead of a monomorphic eq twin.
  defp literal_chain(
         scrut_expr,
         scrut_term,
         scrut_type,
         prim,
         [{{:literal, _m, v}, body} | rest],
         expected,
         names,
         ctx,
         env
       ) do
    with {:ok, body_core} <- elaborate_match_body(body, expected, names, ctx, env),
         {:ok, rest_core} <-
           literal_chain(scrut_expr, scrut_term, scrut_type, prim, rest, expected, names, ctx, env) do
      test = eq_test_core(prim, scrut_term, lit_core(v, prim, env), scrut_type, ctx)
      {:ok, bool_case(test, expected, body_core, rest_core, ctx)}
    end
  end

  # A pin arm `^x`: same as a literal arm, but the compared value is the current
  # value of the bound variable `x` (elaborated to its core term) rather than a
  # constant. `scrut == x` picks the identical type-directed equality twin.
  defp literal_chain(
         scrut_expr,
         scrut_term,
         scrut_type,
         prim,
         [{{:pin, _m, [{:variable, _vm, name}]}, body} | rest],
         expected,
         names,
         ctx,
         env
       ) do
    with {:ok, x_core, _x_type} <- elaborate_expr_typed({:variable, [], name}, names, ctx, env),
         {:ok, body_core} <- elaborate_match_body(body, expected, names, ctx, env),
         {:ok, rest_core} <-
           literal_chain(scrut_expr, scrut_term, scrut_type, prim, rest, expected, names, ctx, env) do
      test = eq_test_core(prim, scrut_term, x_core, scrut_type, ctx)
      {:ok, bool_case(test, expected, body_core, rest_core, ctx)}
    end
  end

  # The per-arm equality test `scrut == literal` yielding the inductive Bool. A
  # `:bounded` scrutinee (Char) has no monomorphic eq twin, so it uses the
  # polymorphic `struct_eq` applied to the signature-aware readback of the
  # scrutinee type (its type argument is erased at emit).
  # The per-arm equality test `scrut == rhs` yielding the inductive Bool, where
  # `rhs` is an already-built core term (a literal for a literal arm, the pinned
  # variable's term for a pin arm). A `:bounded` scrutinee (Char) has no monomorphic
  # eq twin, so it uses the polymorphic `struct_eq` applied to the signature-aware
  # readback of the scrutinee type (its type argument is erased at emit).
  defp eq_test_core(:bounded, scrut_term, rhs_core, scrut_type, ctx) do
    ty = Quote.reify(scrut_type, Context.length(ctx), Context.signature(ctx))
    {:app, app2(builtin_op_global(:struct_eq), ty, scrut_term), rhs_core}
  end

  defp eq_test_core(prim, scrut_term, rhs_core, _scrut_type, _ctx) do
    eq_global =
      case prim do
        :int -> builtin_op_global(:int_eq)
        :float -> builtin_op_global(:float_eq)
        :bool -> :eq
      end

    app2(eq_global, scrut_term, rhs_core)
  end

  # A flat n-element tuple projects POSITIONALLY: `%[e1, …, en]` binds
  # `e1 = base.1`, `e2 = base.2`, …, `en = base.n` (each `.i` resolves against the
  # flat lowering via `positional_projection`). Each element may itself be a
  # nested tuple, recursing on its own projection base (`base.i.1`, `base.i.2`, …).
  defp tuple_subs(elems, base) do
    elems
    |> Enum.with_index(1)
    |> Enum.reduce_while({:ok, []}, fn {e, i}, {:ok, acc} ->
      case tuple_elem_sub(e, tuple_proj(base, Integer.to_string(i))) do
        {:ok, s} -> {:cont, {:ok, acc ++ s}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp tuple_proj(base, n), do: {:attribute_access, [attribute: n], [base]}

  defp tuple_elem_sub({:variable, _m, "_"}, _proj), do: {:ok, []}
  defp tuple_elem_sub({:variable, _m, name}, proj), do: {:ok, [{name, proj}]}
  defp tuple_elem_sub({:tuple, _m, [_, _ | _] = sub_elems}, proj), do: tuple_subs(sub_elems, proj)
  defp tuple_elem_sub(_other, _proj), do: {:error, {:unsupported_pattern, :nested_tuple_element}}

  # --- nested-pattern desugaring (parity #3) ---------------------------------
  #
  # Lower nested constructor sub-patterns (`S(S(m))`, `MkPair(Z(), y)`) into
  # nested *single-level* matches, so the existing dependent match machinery
  # (motives, index refinement, catch-all) handles every level unchanged — the
  # kernel `:case` already nests, so this is purely a surface lowering pass. Runs
  # one level per `elaborate_match`; deeper nesting is lowered on re-entry when
  # the emitted inner match is elaborated.
  #
  # Scope: arms are grouped by their outer constructor; each group's argument
  # columns are compiled by the standard pattern-matrix algorithm
  # (Augustsson/Maranget) — left-to-right column selection producing a tree of
  # single-scrutinee matches, so ANY number of nested columns is handled. A
  # top-level catch-all (`_`/`x`) mixed with nesting is woven in as a fallback
  # row for the sub-patterns each nested group leaves uncovered, and kept as the
  # outer catch-all for wholly-unmatched constructors.
  # ── Guards on constructor patterns ──────────────────────────────────────────
  # `match n | S(k) when g -> a | S(k) -> b | Z() -> c` — a guard on a
  # constructor pattern. Idris has no pattern guards; it collapses such an arm
  # into an `if` inside that constructor's case branch, falling through to the
  # next same-constructor arm when the guard is false. We reproduce exactly that:
  # fold each constructor group that carries a guard into ONE guardless arm
  # `C(w…) -> if g₁ then a else if g₂ then … else <closer>`, where the closer is
  # the group's trailing unguarded arm or the match's catch-all. The result is a
  # plain guardless match the ordinary `:vdata` path compiles; the `if`s lower to
  # `:case` on the inductive Bool (through the general `:conditional` clause). No
  # matrix-compiler or kernel change.

  defp ctor_guarded_arm?({:match_arm, meta, _body}) do
    Keyword.has_key?(meta, :guard) and
      match?({:function_call, _m, _args}, Keyword.get(meta, :pattern))
  end

  defp desugar_ctor_guards(arms, scrut_expr) do
    if Enum.any?(arms, &ctor_guarded_arm?/1),
      do: fold_ctor_guard_groups(arms, scrut_expr),
      else: {:ok, arms}
  end

  defp fold_ctor_guard_groups(arms, scrut_expr) do
    {ctor_arms, defaults} = Enum.split_with(arms, &(not default_arm?(&1)))

    with {:ok, closer} <- default_closer(defaults, scrut_expr) do
      order = ctor_arms |> Enum.map(&arm_ctor_name/1) |> Enum.uniq()
      grouped = Enum.group_by(ctor_arms, &arm_ctor_name/1)

      folded =
        Enum.reduce_while(order, {:ok, []}, fn cname, {:ok, acc} ->
          group = Map.fetch!(grouped, cname)

          # Only groups carrying a guard are folded; a plain group passes through
          # unchanged so a genuine duplicate constructor still reaches the
          # downstream duplicate check rather than being silently collapsed.
          if Enum.any?(group, &guarded_arm?/1) do
            case fold_ctor_group(group, closer) do
              {:ok, arm} -> {:cont, {:ok, acc ++ [arm]}}
              {:error, _} = e -> {:halt, e}
            end
          else
            {:cont, {:ok, acc ++ group}}
          end
        end)

      with {:ok, folded_arms} <- folded, do: {:ok, folded_arms ++ defaults}
    end
  end

  # The match's trailing catch-all is the fall-through for a group whose last arm
  # is still guarded. `:none` = no catch-all (a still-guarded last arm is then
  # non-exhaustive). More than one default is out of scope.
  defp default_closer([], _scrut), do: {:ok, :none}

  defp default_closer([{:match_arm, dmeta, dbody0}], scrut_expr) do
    {:variable, _m, dvname} = Keyword.fetch!(dmeta, :pattern)

    case resolve_default_body(dvname, single_body(dbody0), scrut_expr) do
      {:ok, db} -> {:ok, {:some, db}}
      {:error, reason} -> {:error, {:unsupported_guard, reason}}
    end
  end

  defp default_closer(_multi, _scrut), do: {:error, {:unsupported_guard, :multiple_defaults}}

  # Fold one constructor group's rows (each `C(v…) [when g] -> body`, all single
  # level and sharing arity k) into a single `C(w₁..w_k) -> <if-chain>`.
  defp fold_ctor_group([{:match_arm, meta0, _} | _] = group, closer) do
    {:function_call, fmeta, args0} = Keyword.fetch!(meta0, :pattern)
    cname = Keyword.fetch!(fmeta, :name)
    k = length(args0)
    wilds = for i <- 1..k//1, do: {:variable, [], "$g" <> cname <> Integer.to_string(i)}
    wnames = Enum.map(wilds, fn {:variable, _m, n} -> n end)

    with {:ok, chain} <- build_guard_chain(group, wnames, closer) do
      {:ok, {:match_arm, [pattern: {:function_call, fmeta, wilds}], [chain]}}
    end
  end

  # An unguarded row terminates the chain (its body; later rows shadowed). A
  # guarded last row falls through to the catch-all, or is non-exhaustive if
  # there is none.
  defp build_guard_chain([{:match_arm, meta, body}], wnames, closer) do
    with {:ok, subs} <- guard_row_renaming(meta, wnames, body) do
      case Keyword.get(meta, :guard) do
        nil ->
          {:ok, rename_all(single_body(body), subs)}

        guard ->
          case closer do
            {:some, db} ->
              {:ok, mk_if(rename_all(guard, subs), rename_all(single_body(body), subs), db)}

            :none ->
              {:error, {:unsupported_guard, :non_exhaustive}}
          end
      end
    end
  end

  defp build_guard_chain([{:match_arm, meta, body} | rest], wnames, closer) do
    with {:ok, subs} <- guard_row_renaming(meta, wnames, body) do
      case Keyword.get(meta, :guard) do
        nil ->
          {:ok, rename_all(single_body(body), subs)}

        guard ->
          with {:ok, else_} <- build_guard_chain(rest, wnames, closer) do
            {:ok, mk_if(rename_all(guard, subs), rename_all(single_body(body), subs), else_)}
          end
      end
    end
  end

  defp mk_if(cond, then_, else_), do: {:conditional, [], [cond, then_, else_]}

  # Map a row's constructor-argument variable names onto the shared fresh binders
  # `w₁..w_k`. Rejects (shadow) if the row's body/guard rebinds a source name, to
  # keep the surface substitution capture-free (mirrors `compile_group`).
  defp guard_row_renaming(meta, wnames, body) do
    {:function_call, _fm, argpats} = Keyword.fetch!(meta, :pattern)
    oldnames = Enum.map(argpats, fn {:variable, _m, n} -> n end)
    subs = Enum.zip(oldnames, wnames)
    guard = Keyword.get(meta, :guard)
    exprs = [single_body(body) | if(guard, do: [guard], else: [])]

    if Enum.any?(exprs, fn e -> binds_any?(e, oldnames) end),
      do: {:error, {:unsupported_guard, :shadowed}},
      else: {:ok, subs}
  end

  defp rename_all(expr, subs) do
    Enum.reduce(subs, expr, fn {old, new}, e ->
      subst_surface_var(e, old, {:variable, [], new})
    end)
  end

  # A monotonic per-process counter yielding a unique infix for generated
  # scrutinee names, so nested-pattern lowerings at different match sites (and
  # different nesting depths) never produce colliding — hence capturing — names.
  # Process-local: one elaboration runs sequentially in one process, and tests
  # assert only on the {:ok, _} verdict, never on generated names.
  defp fresh_tag do
    n = Process.get(:cure_desugar_gensym, 0)
    Process.put(:cure_desugar_gensym, n + 1)
    Integer.to_string(n) <> "$"
  end

  defp desugar_nested_arms(arms, scrut_expr) do
    cond do
      not Enum.any?(arms, &arm_has_nested?/1) ->
        {:ok, arms}

      Enum.any?(arms, &default_arm?/1) ->
        desugar_with_default(arms, scrut_expr)

      true ->
        compile_nested_groups(arms)
    end
  end

  # A nested match with a trailing top-level catch-all `… | x -> d`. Resolve the
  # catch-all body (binding its name to the scrutinee), weave it as a wildcard
  # fallback row into every nested group so uncovered sub-patterns fall through to
  # it, then keep a top-level `_ -> d` for constructors with no arm at all.
  defp desugar_with_default(arms, scrut_expr) do
    {ctor_arms, defaults} = Enum.split_with(arms, &(not default_arm?(&1)))

    with [{:match_arm, dmeta, dbody0}] <- defaults,
         true <- default_arm?(List.last(arms)) or :not_last,
         {:variable, _m, dvname} <- Keyword.fetch!(dmeta, :pattern),
         {:ok, dbody} <- resolve_default_body(dvname, single_body(dbody0), scrut_expr) do
      with {:ok, compiled} <- compile_nested_groups(weave_default(ctor_arms, dbody)) do
        {:ok, compiled ++ [{:match_arm, [pattern: {:variable, [], "_"}], dbody}]}
      end
    else
      _ -> {:error, {:unsupported_pattern, :catchall_with_nesting}}
    end
  end

  # `_` needs no binding; a named catch-all binds the whole scrutinee, so it is
  # only supported over a variable scrutinee (substitute its name), never a
  # complex scrutinee expression (nothing to bind to).
  defp resolve_default_body("_", dbody, _scrut), do: {:ok, dbody}

  defp resolve_default_body(dvname, dbody, {:variable, _m, sname}) do
    if binds_any?(dbody, [dvname]),
      do: {:error, :shadowed},
      else: {:ok, subst_surface_var(dbody, dvname, {:variable, [], sname})}
  end

  defp resolve_default_body(_dvname, _dbody, _scrut), do: {:error, :nonvariable_scrutinee}

  # Append a wildcard fallback arm (`C(_…) -> d`) to each group that has nesting,
  # so the group's matrix falls back to the catch-all body for uncovered
  # sub-patterns. Non-nested groups are already exhaustive and left untouched.
  defp weave_default(ctor_arms, dbody) do
    order = ctor_arms |> Enum.map(&arm_ctor_name/1) |> Enum.uniq()
    grouped = Enum.group_by(ctor_arms, &arm_ctor_name/1)

    Enum.flat_map(order, fn cname ->
      group = Map.fetch!(grouped, cname)

      if Enum.any?(group, &arm_has_nested?/1) do
        {:function_call, fmeta, args0} = arm_pattern(hd(group))
        wilds = for i <- 1..length(args0)//1, do: {:variable, [], "$fb" <> cname <> Integer.to_string(i)}
        group ++ [{:match_arm, [pattern: {:function_call, fmeta, wilds}], dbody}]
      else
        group
      end
    end)
  end

  defp arm_pattern({:match_arm, meta, _body}), do: Keyword.fetch!(meta, :pattern)

  defp default_arm?({:match_arm, meta, _body}),
    do: match?({:variable, _m, _v}, Keyword.fetch!(meta, :pattern))

  defp arm_has_nested?({:match_arm, meta, _body}) do
    case Keyword.fetch!(meta, :pattern) do
      {:function_call, _m, args} -> Enum.any?(args, &(not pat_arg_leaf?(&1)))
      _ -> false
    end
  end

  # A constructor-pattern argument is a LEAF (not a nested sub-pattern needing
  # matrix lowering) if it is a bare variable or a named-implicit annotation.
  defp pat_arg_leaf?({:variable, _m, _v}), do: true
  defp pat_arg_leaf?({:named_implicit_pat, _m, _children}), do: true
  defp pat_arg_leaf?(_), do: false

  # Group arms by outer constructor (first-appearance order, within-group order
  # preserved for first-match), then compile each group to one single-level arm.
  defp compile_nested_groups(arms) do
    order = arms |> Enum.map(&arm_ctor_name/1) |> Enum.uniq()
    grouped = Enum.group_by(arms, &arm_ctor_name/1)

    Enum.reduce_while(order, {:ok, []}, fn cname, {:ok, acc} ->
      case compile_ctor_group(cname, Map.fetch!(grouped, cname)) do
        {:ok, group_arms} -> {:cont, {:ok, acc ++ group_arms}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp arm_ctor_name({:match_arm, meta, _body}) do
    {:function_call, fmeta, _args} = Keyword.fetch!(meta, :pattern)
    Keyword.fetch!(fmeta, :name)
  end

  # A group with a nested arm is compiled by the matrix algorithm; a group with
  # none is passed through unchanged (so a genuine duplicate constructor still
  # reaches `partition_arms`' duplicate check).
  defp compile_ctor_group(_cname, arms) do
    if Enum.any?(arms, &arm_has_nested?/1), do: compile_group(arms), else: {:ok, arms}
  end

  # `arms` all share an outer constructor `C/k`. Emit `C(v₁..v_k) -> <matrix>`,
  # where `<matrix>` compiles the k argument columns (rows = each arm's sub-
  # patterns → body) into a tree of single-scrutinee matches.
  defp compile_group([{:match_arm, meta0, _} | _] = arms) do
    {:function_call, fmeta, args0} = Keyword.fetch!(meta0, :pattern)
    cname = Keyword.fetch!(fmeta, :name)
    k = length(args0)

    # Shadow guard: a naive surface substitution would capture if a body rebinds
    # one of the pattern variables it substitutes. Reject rather than miscompile.
    pvars =
      arms
      |> Enum.flat_map(fn {:match_arm, m, _} ->
        {:function_call, _fm, as} = Keyword.fetch!(m, :pattern)
        Enum.flat_map(as, &pattern_vars_deep/1)
      end)
      |> Enum.uniq()

    if Enum.any?(arms, fn {:match_arm, m, b} ->
         binds_any?(single_body(b), pvars) or
           (Keyword.get(m, :guard) && binds_any?(Keyword.get(m, :guard), pvars))
       end) do
      {:error, {:unsupported_pattern, :shadowed_nested}}
    else
      # Seed the fresh scrutinee names with a per-invocation unique tag. Every
      # deeper name (`split_ctor_arms`, `split_default`) derives from these, so a
      # unique seed makes the WHOLE lowered subtree's names unique. Without it,
      # two independently-desugared nested matches — an outer arm whose body is
      # itself a nested match — regenerate identical names (`$nSome1_Y1`) and the
      # inner binder captures a reference the outer desugaring baked into the
      # body (variable capture → spurious `:branch_type`). See
      # nested_match_capture_test.exs.
      tag = fresh_tag()
      fresh = for i <- 1..k//1, do: "$n" <> tag <> cname <> Integer.to_string(i)

      rows =
        Enum.map(arms, fn {:match_arm, m, b} ->
          {:function_call, _fm, as} = Keyword.fetch!(m, :pattern)
          {as, Keyword.get(m, :guard), single_body(b)}
        end)

      case compile_matrix(fresh, rows) do
        {:ok, inner} ->
          outer_pat = {:function_call, fmeta, Enum.map(fresh, &{:variable, [], &1})}
          {:ok, [{:match_arm, [pattern: outer_pat], inner}]}

        {:error, _} = err ->
          err
      end
    end
  end

  defp pattern_vars_deep({:variable, _m, v}), do: [v]
  defp pattern_vars_deep({:function_call, _m, args}), do: Enum.flat_map(args, &pattern_vars_deep/1)
  defp pattern_vars_deep(_), do: []

  # Pattern-matrix compilation. `scruts` are fresh scrutinee variable NAMES; each
  # row is `{[pattern…], guard, body}` (guard is `nil` or a surface expr) with one
  # pattern per remaining scrutinee. Emits a tree of single-scrutinee
  # `{:pattern_match}` nodes; every emitted match is single-level, so it re-uses
  # the dependent elaborator per node. At a leaf (no columns left), the reached
  # rows are folded into a `:case`-on-Bool `if`-chain: a guarded row tests its guard
  # and falls through to the next reached row, an unguarded row terminates the
  # chain (later rows shadowed), à la the Wadler/Augustsson `match … default`
  # continuation. All still over surface names, so no de-Bruijn weakening.
  defp compile_matrix([], rows), do: fold_leaf_rows(rows)

  defp compile_matrix([v | vs], rows) do
    col = Enum.map(rows, fn {[p | _ps], _g, _b} -> p end)

    if Enum.all?(col, &match?({:variable, _m, _n}, &1)) do
      # All-variable column: bind each row's variable to `v`, drop the column.
      rows2 =
        Enum.map(rows, fn {[{:variable, _m, x} | ps], g, body} ->
          repl = {:variable, [], v}
          {ps, subst_guard(g, x, repl), subst_surface_var(body, x, repl)}
        end)

      compile_matrix(vs, rows2)
    else
      compile_matrix_split(v, vs, rows, col)
    end
  end

  # Fold the rows reaching a matrix leaf into an `if`-chain. An unguarded row is
  # an unconditional match: it terminates the chain (identical to the previous
  # first-match behaviour when no row is guarded). A guarded final row with no
  # unguarded successor is non-exhaustive.
  defp fold_leaf_rows([{[], nil, body} | _]), do: {:ok, body}

  defp fold_leaf_rows([{[], guard, body} | rest]) do
    with {:ok, else_} <- fold_leaf_rows(rest) do
      {:ok, {:conditional, [], [guard, body, else_]}}
    end
  end

  defp fold_leaf_rows([]), do: {:error, {:unsupported_guard, :non_exhaustive}}

  defp subst_guard(nil, _name, _repl), do: nil
  defp subst_guard(guard, name, repl), do: subst_surface_var(guard, name, repl)

  # Column `v` has ≥1 constructor pattern: branch on each distinct constructor
  # (first-appearance order), plus a catch-all if any row has a variable there.
  defp compile_matrix_split(v, vs, rows, col) do
    ctors =
      col
      |> Enum.flat_map(fn
        {:function_call, m, _a} -> [Keyword.fetch!(m, :name)]
        _ -> []
      end)
      |> Enum.uniq()

    has_var = Enum.any?(col, &match?({:variable, _m, _n}, &1))

    with {:ok, ctor_arms} <- split_ctor_arms(ctors, v, vs, rows) do
      arms =
        if has_var do
          {:ok, default_inner} = split_default(v, vs, rows)
          ctor_arms ++ [{:match_arm, [pattern: {:variable, [], v <> "_d"}], default_inner}]
        else
          ctor_arms
        end

      {:ok, {:pattern_match, [], [{:variable, [], v} | arms]}}
    end
  end

  defp split_ctor_arms(ctors, v, vs, rows) do
    Enum.reduce_while(ctors, {:ok, []}, fn cname, {:ok, acc} ->
      arity = split_arity(cname, rows)
      ws = for i <- 1..arity//1, do: v <> "_" <> cname <> Integer.to_string(i)

      sub_rows =
        Enum.flat_map(rows, fn {[p | ps], g, body} ->
          case p do
            {:function_call, m, qs} ->
              if Keyword.fetch!(m, :name) == cname, do: [{qs ++ ps, g, body}], else: []

            {:variable, _m, x} ->
              wilds = for w <- ws, do: {:variable, [], w <> "_x"}
              repl = {:variable, [], v}
              [{wilds ++ ps, subst_guard(g, x, repl), subst_surface_var(body, x, repl)}]
          end
        end)

      case compile_matrix(ws ++ vs, sub_rows) do
        {:ok, inner} ->
          pat = {:function_call, [name: cname], Enum.map(ws, &{:variable, [], &1})}
          {:cont, {:ok, acc ++ [{:match_arm, [pattern: pat], inner}]}}

        {:error, _} = err ->
          {:halt, err}
      end
    end)
  end

  # Arity of `cname` from the first row that mentions it explicitly.
  defp split_arity(cname, rows) do
    Enum.find_value(rows, 0, fn {[p | _], _g, _b} ->
      case p do
        {:function_call, m, qs} -> if Keyword.fetch!(m, :name) == cname, do: length(qs)
        _ -> nil
      end
    end)
  end

  # Catch-all sub-matrix for constructors not explicitly listed: only the
  # variable rows survive (each binding its variable to `v`), column dropped.
  defp split_default(v, vs, rows) do
    default_rows =
      Enum.flat_map(rows, fn {[p | ps], g, body} ->
        case p do
          {:variable, _m, x} ->
            repl = {:variable, [], v}
            [{ps, subst_guard(g, x, repl), subst_surface_var(body, x, repl)}]

          _ ->
            []
        end
      end)

    compile_matrix(vs, default_rows)
  end

  # Build `{arm_map, default}` where arm_map is cname => {:matched, pattern, body}
  # | {:impossible_marked, pattern}, and `default` is `nil` or `{vname, body}` for
  # a single variable/wildcard catch-all arm (`x -> …` / `_ -> …`), which covers
  # every constructor not explicitly matched (Idris/Lean variable-pattern
  # coverage). Validates every constructor arm names one of dname's OWN declared
  # constructors (spec §5 step 2 gap) and rejects duplicate arms / duplicate
  # defaults / an impossible-marked catch-all.
  # A bare capitalized pattern (`Lt`) parses as a variable — the parser has no
  # type information — but when the name resolves to a NULLARY constructor of the
  # scrutinee's family it is a constructor pattern, not a fresh binder: `Lt` ≡
  # `Lt()` (Idris/Agda/Lean read an uppercase bare pattern as a nullary
  # constructor). Rewrite it to the canonical `Ctor()` node so the constructor
  # path handles it identically to the parenthesized spelling. Every genuine
  # variable/wildcard pattern — and any capitalized name that is NOT a nullary
  # constructor of this family — is left untouched, so it still binds/defaults.
  defp desugar_nullary_ctor_pattern({:variable, _meta, vname} = pat, sig, env, dname) do
    cname = resolve_ctor_key(env, String.to_atom(vname))

    case Inductive.get_ctor(env, cname) do
      %{args: []} ->
        if Inductive.ctor_family(sig, cname) == dname,
          do: {:function_call, [name: vname], []},
          else: pat

      _ ->
        pat
    end
  end

  defp desugar_nullary_ctor_pattern(pat, _sig, _env, _dname), do: pat

  defp partition_arms(arms, ctx, env, dname) do
    sig = Context.signature(ctx)

    Enum.reduce_while(arms, {:ok, {%{}, nil}}, fn {:match_arm, arm_meta, body}, {:ok, {acc, default}} ->
      pattern = arm_meta |> Keyword.fetch!(:pattern) |> desugar_nullary_ctor_pattern(sig, env, dname)

      case pattern do
        {:variable, _vmeta, vname} ->
          cond do
            Keyword.get(arm_meta, :impossible) == true ->
              {:halt, {:error, {:impossible_default_pattern, vname}}}

            default != nil ->
              {:halt, {:error, {:duplicate_default_pattern, vname}}}

            true ->
              {:cont, {:ok, {acc, {vname, single_body(body)}}}}
          end

        _ ->
          case constructor_pattern(pattern) do
            {:error, _} = err ->
              {:halt, err}

            {:ok, {cname0, _vars}} ->
              cname = resolve_ctor_key(env, cname0)
              pattern = rekey_pattern_name(pattern, cname)

              cond do
                Inductive.get_ctor(env, cname) == nil ->
                  {:halt, {:error, {:unknown_pattern_constructor, cname}}}

                Inductive.ctor_family(sig, cname) != dname ->
                  {:halt, shadowed_or_foreign_ctor(env, sig, cname0, cname, dname)}

                Map.has_key?(acc, cname) ->
                  {:halt, {:error, {:duplicate_branch, cname}}}

                Keyword.get(arm_meta, :impossible) == true ->
                  {:cont, {:ok, {Map.put(acc, cname, {:impossible_marked, pattern}), default}}}

                true ->
                  {:cont, {:ok, {Map.put(acc, cname, {:matched, pattern, single_body(body)}), default}}}
              end
          end
      end
    end)
  end

  # ── Join points (plan slice 4c) ─────────────────────────────────────────────
  # Core `:case` has no default branch, so a surface catch-all becomes one branch
  # per uncovered constructor — and `elaborate_default_branch/10` re-elaborates
  # its body for each. The copies MULTIPLY through nesting: `k` nested catch-alls
  # over an `n`-constructor type used to yield `(n-1)^k` copies (measured: 25 for
  # k=2, n=6). A join point binds the body once and calls it from each branch.
  #
  # No new Core former is needed. Given the motive `λ(s : S). R`, bind
  #
  #     j = {:lam, ω, S, body}   at   {:pi, ω, S, R}
  #
  # in the `:let` binder, and make each defaulted branch `{:app, j, scrut}`. The λ
  # is load-bearing: a bare `:let` of `body` would be EAGER (`Emit` lowers `:let`
  # to a match block), so the catch-all would run even when a real arm matched.
  # It also subsumes the surface substitution — a named catch-all `x -> …` is
  # precisely the λ's binder, so `x` is the scrutinee's value by construction.
  #
  # NOT a soundness fix. Idris combines branch usages by agreement rather than
  # summation (`LinearCheck.idr:528-540`), and the copies always landed in
  # DISJOINT constructor branches, so a linear variable in the catch-all was
  # already counted once. This buys term size, which on an ESP32 is flash.
  #
  # Fire only where it pays and where it is obviously type-correct:
  #
  #   * ≥2 uncovered constructors — one call site would pay a closure to save
  #     nothing;
  #   * no carried index equality, and an UNINDEXED family — otherwise `motive`
  #     is not the plain `λ(s : S). R` this encoding reads it as;
  #   * a NON-DEPENDENT motive (`R` does not mention `s`). A dependent `R` would
  #     type each branch at `R[s := C(args…)]`, so the join would have to be
  #     applied to the branch's reconstructed constructor — including its erased
  #     telescope args — rather than to `scrut`. Left as today's expansion.
  defp join_point?(default, uncovered, carried, idx_vals, motive) do
    # `:qtt_join_disabled` is a TEST HOOK: the usage checker (`Relevance`) now
    # un-joins the shared continuation correctly (review F11), so the join is safe
    # to emit even in graded defs. The differential test sets this flag to force the
    # per-branch form and assert the un-join verdict matches it. Unset in production.
    default != nil and length(uncovered) >= 2 and carried == nil and idx_vals == [] and
      match?({:lam, _g, _s, _r}, motive) and
      not MapSet.member?(free_indices(elem(motive, 3), 0), 0) and
      not Process.get(:qtt_join_disabled, false)
  end

  defp elaborate_join(false, _default, _names, _ctx, _env, _motive), do: {:ok, nil}

  defp elaborate_join(true, {vname, body_expr}, names, ctx, env, {:lam, _g, s_term, r_term}) do
    # `r_term` already lives under the motive's binder, so in `ctx1` it IS the
    # catch-all's expected type — no shift.
    ctx1 = Context.extend(ctx, Eval.eval(s_term, Context.env(ctx)))
    names1 = [vname | names]

    with {:ok, body} <- elaborate_expr_checked(body_expr, r_term, names1, ctx1, env) do
      {:ok, {{:pi, Grade.unrestricted(), s_term, r_term}, {:lam, Grade.unrestricted(), s_term, body}}}
    end
  end

  # Wrap the assembled `:case` in the join binder and discharge every marker.
  # Inserting a binder between the context and the case shifts everything inside
  # by one: `scrut` and `motive` at cutoff 0, a branch body at cutoff `arity` (its
  # own constructor binders must not move). Inside a branch the join sits at index
  # `arity`, and the scrutinee it is applied to has travelled under `1 + arity`
  # binders.
  defp wrap_join(case_term, nil), do: case_term

  defp wrap_join({:case, scrut, motive, branches}, {join_ty, join_val}) do
    branches1 =
      Enum.map(branches, fn
        {c, arity, @join_marker} -> {c, arity, {:app, {:var, arity}, Subst.shift(scrut, 1 + arity, 0)}}
        {c, arity, body} -> {c, arity, Subst.shift(body, 1, arity)}
      end)

    inner = {:case, Subst.shift(scrut, 1, 0), Subst.shift(motive, 1, 0), branches1}
    {:let, Grade.unrestricted(), join_ty, join_val, inner}
  end

  # A variable/wildcard catch-all covers `cname` (not explicitly matched): rebuild
  # the constructor pattern `cname(fresh…)`, substitute the catch-all's name with
  # that reconstruction in the body (so the bound var resolves to the very term
  # the kernel's branch goal expects), and route through the normal matched-branch
  # path — index inversion, goal refinement, carried-eq, and scrutinee
  # substitution all apply unchanged. E-layer, no TCB.
  defp elaborate_default_branch(
         verdict,
         cname,
         {vname, body_expr},
         names,
         ctx,
         env,
         param_vals,
         scrut_term,
         result_type_term,
         carried
       ) do
    # A surface constructor pattern names only the PRESENT (non-erased) args; the
    # erased indices are reconstructed from the telescope, not bound in the source.
    %{quantities: quantities} = Inductive.get_ctor(env, cname)
    present = Enum.count(quantities, &Grade.present?/1)
    fresh = default_pattern_vars(cname, present)
    syn_pattern = {:function_call, [name: Atom.to_string(cname)], Enum.map(fresh, &{:variable, [], &1})}

    cond do
      vname == "_" ->
        elaborate_matched_branch(
          verdict,
          syn_pattern,
          body_expr,
          names,
          ctx,
          env,
          param_vals,
          scrut_term,
          result_type_term,
          carried
        )

      binds_any?(body_expr, [vname]) ->
        # The catch-all's name is rebound inside its own body; a naive surface
        # substitution would capture. Reject rather than miscompile.
        {:error, {:unsupported_pattern, :shadowed_default}}

      true ->
        body2 = subst_surface_var(body_expr, vname, syn_pattern)

        elaborate_matched_branch(
          verdict,
          syn_pattern,
          body2,
          names,
          ctx,
          env,
          param_vals,
          scrut_term,
          result_type_term,
          carried
        )
    end
  end

  # Fresh, collision-proof binder names for a synthesized catch-all constructor
  # pattern (`$<ctor>_<n>`); empty for a nullary constructor.
  defp default_pattern_vars(cname, arity) do
    for i <- 1..arity//1, do: "$" <> Atom.to_string(cname) <> "_" <> Integer.to_string(i)
  end

  defp elaborate_matched_branch(
         verdict,
         pattern,
         body_expr,
         names,
         ctx,
         env,
         scrut_param_vals,
         scrut_term,
         result_type_term,
         carried
       ) do
    {:ok, {cname, pattern_vars}} = constructor_pattern(pattern)
    %{args: telescope, quantities: quantities, result_indices: result_indices} = Inductive.get_ctor(env, cname)
    branch_names = branch_scope(telescope, quantities, pattern_vars) ++ names

    case verdict do
      :impossible ->
        # Matched arm on a genuinely unreachable constructor the user did NOT mark
        # impossible: elaborate the body unchecked (the kernel discharges it too).
        branch_ctx = extend_context(ctx, telescope, scrut_param_vals)

        with {:ok, body_term, _type} <- elaborate_expr_typed(body_expr, branch_names, branch_ctx, env) do
          {:ok, {cname, length(telescope), body_term}}
        end

      _solved_or_trivial ->
        arity = length(telescope)

        # The kernel's `branch_unify` verdict is the COMPLETE index inversion for
        # this branch — both `ctor-arg := scrut-index` (Vec-style) AND
        # `scrut-index-var := ctor-result` (e.g. `n := Z` for `v : NV(n)` matched
        # by `vz : NV(Z)`). The with-rematch path already uses it; the plain path
        # previously reimplemented a strictly weaker subset (`branch_index_subst`)
        # that missed the second direction, so a goal mentioning the scrutinee's
        # index in a nested position (`Eq(NV(n), …)`) never refined per branch.
        subst =
          case verdict do
            {:solved, s} -> s
            :trivial -> %{}
          end

        # C-c (spec 2026-07-08 §2.3): split the pattern's named implicits into
        # BINDINGS (an unforced position written as a bare variable — binds the
        # anonymized erased telescope slot at quantity 0, Relevance policing any
        # relevant use) and CHECKS (forced positions, plus unforced dot/non-var
        # forms that keep the `{:named_implicit_unforced,…}` reject). Compute the
        # split and the renamed branch scope ONCE, before the carried/plain
        # dispatch, so BOTH paths honor the binding.
        {bindings, checks} = split_named_implicits(pattern, subst, arity, telescope)

        tele_names =
          Enum.reduce(bindings, branch_scope(telescope, quantities, pattern_vars), fn {name, {:variable, _, vname}},
                                                                                      acc ->
            p = Enum.find_index(telescope, fn {n, _t} -> n == String.to_atom(name) end)
            List.replace_at(acc, arity - 1 - p, to_string(vname))
          end)

        branch_names = tele_names ++ names

        if carried != nil do
          elaborate_carried_eq_branch(
            cname,
            telescope,
            result_indices,
            body_expr,
            branch_names,
            ctx,
            env,
            scrut_param_vals,
            result_type_term,
            carried,
            checks,
            subst
          )
        else
          branch_ctx =
            ctx
            |> extend_context(telescope, scrut_param_vals)
            |> specialize_branch_context_subst(subst)

          # Merge in the scrutinee VALUE substitution (`v ↦ ctor`) so a goal that
          # mentions the scrutinee value itself (`Eq(T, v, v)`) refines to the
          # branch constructor alongside the index inversion — the shared
          # `refine_branch_goal` (Task 3.4), also used by the with-rematch path.
          branch_expected =
            refine_branch_goal(result_type_term, scrut_term, cname, arity, subst, branch_ctx)

          # Lean substitutes a variable major premise by `ctor fields` in the
          # entire subgoal — context AND everything elaborated inside it
          # (`Meta/Tactic/Cases.lean:219-227`, the `subst.insert majorFVarId
          # ctorApp`). Cure's surface analog: free occurrences of the scrutinee
          # NAME in the branch body become the branch pattern expression, whose
          # vars are already bound in branch scope and elaborate to exactly the
          # `ctor_term` the kernel's branch goal expects. Without this, a body
          # like `refl(v)` keeps `v` opaque (`v ≢ vz`) even though the goal
          # correctly refined to `Eq(NV(Z), vz, vz)`.
          body_expr = refine_scrutinee_in_body(body_expr, scrut_term, pattern, pattern_vars, names)

          with :ok <-
                 check_named_implicits(checks, subst, arity, telescope, branch_ctx, branch_names, env),
               {:ok, body_term} <-
                 elaborate_branch_body(body_expr, branch_expected, branch_names, branch_ctx, env) do
            {:ok, {cname, arity, body_term}}
          end
        end
    end
  end

  # Named-implicit annotations `{k = <expr>}` on this branch's constructor
  # pattern are check-and-discard: for each, resolve the named erased index to
  # its telescope position `p`, read the forced value `d` the kernel's index
  # inversion pinned at that position (`subst[arity-1-p]`), elaborate the user's
  # forced inner expression to a term `t` in the branch frame, and require `t`
  # convertible with `d`. The annotation binds nothing and produces no runtime
  # term, so on success we simply continue; on mismatch the branch is rejected.
  #
  # The `checks` argument is the pre-split CHECK list from
  # `split_named_implicits/4` (C-c, spec 2026-07-08 §2.3) — the bindings have
  # already been peeled off and named in the branch scope. An unforced position
  # written as a bare variable BINDS instead (split off there); reaching the
  # `{:named_implicit_unforced,…}` error below with a dot/non-variable inner
  # means nothing was pinned to check against — write a bare variable to bind
  # the index instead.
  defp check_named_implicits(checks, subst, arity, telescope, branch_ctx, branch_names, env) do
    checks
    |> Enum.reduce_while(:ok, fn {name, inner}, :ok ->
      case named_implicit_forced_value(name, subst, arity, telescope) do
        {:ok, d} ->
          expr = forced_inner_expr(inner)

          case elaborate_expr_typed(expr, branch_names, branch_ctx, env) do
            {:ok, t_term, _ty} ->
              if Cure.Core.Conv.conv?(
                   t_term,
                   d,
                   Context.env(branch_ctx),
                   Context.length(branch_ctx),
                   Context.signature(branch_ctx)
                 ) do
                {:cont, :ok}
              else
                {:halt, {:error, {:forced_pattern_mismatch, t_term, d}}}
              end

            {:error, _} = err ->
              {:halt, err}
          end

        :error ->
          {:halt, {:error, {:named_implicit_unforced, name}}}
      end
    end)
  end

  # Position of the erased index named `name` in the constructor telescope, then
  # the forced value the branch-unify substitution pinned there. de Bruijn: the
  # telescope binds left-to-right, so position `p` is variable `arity-1-p`.
  defp named_implicit_forced_value(name, subst, arity, telescope) do
    key = String.to_atom(name)

    case Enum.find_index(telescope, fn {n, _t} -> n == key end) do
      nil ->
        :error

      p ->
        case Map.get(subst, arity - 1 - p) do
          nil -> :error
          d -> {:ok, d}
        end
    end
  end

  # The forced inner of a named-implicit is normally a dot pattern `.<expr>`; peel
  # the forced wrapper (it is not valid in ordinary expression elaboration) and
  # elaborate the underlying expression. A non-dot inner is elaborated as-is.
  defp forced_inner_expr({:forced_pattern, _m, [inner]}), do: inner
  defp forced_inner_expr(other), do: other

  @doc """
  Public soundness-probe shim for the forced-annotation check of ONE named
  implicit `{name = .t}` on constructor `cname`, exposed for the Antigen
  `forcing/dot` metatheory vertical (#24). It rebuilds the branch frame exactly
  as `elaborate_matched_branch/10` does — `extend_context(ctx, telescope,
  scrut_param_vals) |> specialize_branch_context_subst(subst)` — and DELEGATES to
  the same `named_implicit_forced_value/4` (telescope-position → pinned forced
  value) and `Cure.Core.Conv.conv?/5` the real `check_named_implicits/7` uses.

  The caller supplies the ALREADY-ELABORATED written value `t_term` (the vertical
  builds it correct-by-construction), so this omits only the surface
  `elaborate_expr_typed` step; the forced-value resolution, the `:unforced` gate,
  and the convertibility decision are the production code paths verbatim. Returns
  `:ok` | `{:forced_pattern_mismatch, t_term, d}` | `{:named_implicit_unforced,
  name}`, matching `check_named_implicits/7`'s three outcomes.
  """
  @spec forced_check_probe(
          Env.t(),
          Context.t(),
          atom(),
          [term()],
          %{optional(integer()) => term()},
          String.t(),
          term()
        ) :: :ok | {:forced_pattern_mismatch, term(), term()} | {:named_implicit_unforced, String.t()}
  def forced_check_probe(env, ctx, cname, scrut_param_vals, subst, name, t_term) do
    %{args: telescope} = Inductive.get_ctor(env, cname)
    arity = length(telescope)

    branch_ctx =
      ctx
      |> extend_context(telescope, scrut_param_vals)
      |> specialize_branch_context_subst(subst)

    case named_implicit_forced_value(name, subst, arity, telescope) do
      {:ok, d} ->
        if Cure.Core.Conv.conv?(
             t_term,
             d,
             Context.env(branch_ctx),
             Context.length(branch_ctx),
             Context.signature(branch_ctx)
           ) do
          :ok
        else
          {:forced_pattern_mismatch, t_term, d}
        end

      :error ->
        {:named_implicit_unforced, name}
    end
  end

  # Step 3b branch. The motive (see `wrap_motive_carried_eq`) makes this branch's
  # expected type `Π(prf : Eq(T, idx, ctor_idx)). G'[jₚₒₛ↦ctor_idx]`, where
  # `ctor_idx` is this constructor's result index at the carried position. Bind
  # `prf`, transport each index-mentioning sibling `h : H[idx]` to `H[ctor_idx]`
  # via `rewrite prf (λz. H[idx↦z]) h`, and emit `λprf. (λh'. body) transport`.
  # Mirrors capability-B's `elaborate_with_eq_branch`, keyed on the index term.
  defp elaborate_carried_eq_branch(
         cname,
         telescope,
         result_indices,
         body_expr,
         branch_names,
         ctx,
         env,
         scrut_param_vals,
         result_type_term,
         carried,
         pattern,
         subst
       ) do
    %{pos: pos, idx_term: idx_term, idx_type_term: idx_type_term, siblings: siblings} = carried
    arity = length(telescope)
    branch_ctx0 = extend_context(ctx, telescope, scrut_param_vals)

    # C-a (spec 2026-07-08 §2.1): run the forced named-implicit check on this
    # carried-eq branch too, in the same pre-proof frame the plain path uses
    # (`branch_ctx0` specialized by the branch-unify subst) — otherwise a wrong
    # dot on a carried branch is silently discarded.
    check_ctx = specialize_branch_context_subst(branch_ctx0, subst)

    with :ok <- check_named_implicits(pattern, subst, arity, telescope, check_ctx, branch_names, env) do
      # `ctor_idx` — this constructor's result index at the carried position, in the
      # branch_ctx0 frame (telescope bound). `Eq(T, idx, ctor_idx)` is the proof the
      # motive hands each branch (kernel checks the branch at `motive @ ctor_idx`).
      ctor_idx = Enum.at(result_indices, pos)
      eq_dom_term = mk_eq(Subst.shift(idx_type_term, arity, 0), Subst.shift(idx_term, arity, 0), ctor_idx)
      branch_ctx1 = Context.extend(branch_ctx0, Eval.eval(eq_dom_term, Context.env(branch_ctx0)))

      # Constants in branch_ctx1 (ctx + telescope + prf). `sc` shifts a ctx-frame
      # term past the telescope and the prf binder; `pat_b1` is `ctor_idx` past prf.
      sc = arity + 1
      idx_b1 = Subst.shift(idx_term, sc, 0)
      t_b1 = Subst.shift(idx_type_term, sc, 0)
      pat_b1 = Subst.shift(ctor_idx, 1, 0)

      sib_data =
        Enum.map(siblings, fn %{index: idx, name: sname, type_term: h_ctx} ->
          h_b1 = Subst.shift(h_ctx, sc, 0)
          motive_j = {:lam, Cure.Core.Grade.unrestricted(), t_b1, abstract_term(h_b1, idx_b1, 0)}
          # J/subst transport (Phase B): prf {:var,0} : Eq(T, idx, ctor_idx); the
          # case's type is (M_j@idx) -> (M_j@ctor_idx), applied to the sibling.
          # Annotation-safety (transport_case doc): M_j abstracts the carried
          # index out of an OUTER-frame sibling type, so it mentions neither
          # `ctor_idx` nor the ctor telescope vars pair-2 could bind.
          transport =
            {:app, transport_case({:var, 0}, t_b1, motive_j, idx_b1), {:var, idx + sc}}

          %{name: sname, dom: replace_term(h_b1, idx_b1, pat_b1), transport: transport}
        end)

      m = length(sib_data)

      branch_ctx_full =
        Enum.reduce(sib_data, branch_ctx1, fn %{dom: d}, c ->
          Context.extend(c, Eval.eval(d, Context.env(c)))
        end)

      body_names = Enum.reduce(sib_data, [carried_prf_name() | branch_names], fn %{name: s}, acc -> [s | acc] end)

      # Refined goal for this branch (`result_type[idx ↦ ctor_idx]`) in the full
      # frame (ctx + telescope + prf + siblings), for checking-mode body forms.
      over = sc + m

      cod_expected =
        Subst.shift(result_type_term, over, 0)
        |> replace_term(Subst.shift(idx_term, over, 0), Subst.shift(ctor_idx, 1 + m, 0))
        |> then(&Kernel.normalize(branch_ctx_full, &1))

      with {:ok, inner} <- elaborate_branch_body(body_expr, cod_expected, body_names, branch_ctx_full, env) do
        wrapped =
          sib_data
          |> Enum.with_index()
          |> Enum.reverse()
          |> Enum.reduce(inner, fn {%{dom: d, transport: t}, i}, acc ->
            {:app, {:lam, Cure.Core.Grade.unrestricted(), Subst.shift(d, i, 0), acc}, Subst.shift(t, i, 0)}
          end)

        {:ok, {cname, arity, {:lam, Cure.Core.Grade.unrestricted(), eq_dom_term, wrapped}}}
      end
    end
  end

  defp carried_prf_name, do: "$carried_idx_prf"

  defp elaborate_branch_body({:rewrite_expr, _meta, _children} = expr, expected, names, ctx, env),
    do: elaborate_expr_checked(expr, expected, names, ctx, env)

  # A nested `match` arm body is a checking-mode expression: `expected` is the
  # (index-refined) result type for this branch, exactly what its motive needs.
  defp elaborate_branch_body({:pattern_match, _meta, _children} = expr, expected, names, ctx, env),
    do:
      if(effect_goal?(expected, ctx),
        do: elaborate_effect_branch(expr, expected, names, ctx, env),
        else: elaborate_expr_checked(expr, expected, names, ctx, env)
      )

  # A nested `with` arm body: like a nested `match` body, a checking-mode
  # expression whose `expected` is this branch's (index/value-refined) goal —
  # route to the checked dispatcher so with-abstractions nest and compose.
  defp elaborate_branch_body({:with_abs, _meta, _children} = expr, expected, names, ctx, env),
    do:
      if(effect_goal?(expected, ctx),
        do: elaborate_effect_branch(expr, expected, names, ctx, env),
        else: elaborate_expr_checked(expr, expected, names, ctx, env)
      )

  defp elaborate_branch_body({:function_call, meta, _args} = expr, expected, names, ctx, env) do
    if effect_goal?(expected, ctx) do
      elaborate_effect_branch(expr, expected, names, ctx, env)
    else
      name = Keyword.get(meta, :name)

      cond do
        name == "reflexive" ->
          elaborate_expr_checked(expr, expected, names, ctx, env)

        is_binary(name) and Inductive.get_ctor(env, String.to_atom(name)) != nil ->
          # A constructor branch body. Infer FIRST — this preserves every case that
          # already worked, including a reconstruction whose indices the present
          # arguments determine and the carried-index-Eq transport (which wraps an
          # inferred body). Retry in checking mode — letting the branch's expected
          # type drive the constructor — when inference cannot pin the erased indices
          # (`prim()`/`seq(l,r)` reconstructed at a refined index with no present
          # argument to solve `av`/`bv` from: `:unsolved_metavariables`) OR when a
          # field is not inferable at all (`:unsupported_expression`) — e.g. an
          # unannotated lambda in a field like `MkLensRep(v, fn new -> ...)`, whose
          # domain only the field type supplies. Both are exactly the cases Idris
          # handles by checking the arm body against the match's expected type; the
          # kernel re-checks either way, so this only ever accepts well-typed terms.
          case elaborate_expr_typed(expr, names, ctx, env) do
            {:ok, term, _type} -> {:ok, term}
            {:error, {:unsolved_metavariables, _}} -> elaborate_expr_checked(expr, expected, names, ctx, env)
            {:error, {:unsupported_expression, _}} -> elaborate_expr_checked(expr, expected, names, ctx, env)
            {:error, _} = err -> err
          end

        true ->
          # An ordinary (non-constructor) function-call arm body. Infer FIRST to
          # preserve every case that already worked; retry in checking mode when
          # inference cannot solve the call's result-type metavariables — a
          # polymorphic nullary function like `empty() -> Iter(t)` whose `t` has no
          # argument to fix it (`:unsolved_metavariables`) — or when an argument is
          # not inferable (`:unsupported_expression`, e.g. an unannotated lambda
          # passed to a higher-order call), letting the branch's expected type drive
          # it. Mirrors the constructor-arm path above; Idris checks arm bodies
          # against the match's expected type, and the kernel re-checks either way.
          case elaborate_expr_typed(expr, names, ctx, env) do
            {:ok, term, _type} -> {:ok, term}
            {:error, {:unsolved_metavariables, _}} -> elaborate_expr_checked(expr, expected, names, ctx, env)
            {:error, {:unsupported_expression, _}} -> elaborate_expr_checked(expr, expected, names, ctx, env)
            {:error, _} = err -> err
          end
      end
    end
  end

  # A tuple `%[a, b, …]` (dependent-pair / flat Σ-telescope introduction) as a
  # branch body: a checking-mode expression against this branch's (index-refined)
  # Σ type — the expected type pins the components' erased indices (an FRP `step`'s
  # `prim()` continuation has no other way to solve its index metas; likewise a
  # flat n-ary tuple whose last component is a bare `[]` needs the goal's `List(_)`
  # to solve the inner `Nil` element). Without this a Σ-returning eliminator fails
  # its arms with `:unsupported_expression`, or an inner `[]` fails infer-only with
  # `{:unsolved_metavariables, :Nil}`. Matches ANY arity ≥ 2: the 2-tuple is a bare
  # dependent pair, arity ≥ 3 is the flat telescope (#35) — both check identically.
  #
  # Under an `Effect(R)` goal the type to check against is `R`, not `Effect(R)` —
  # there is no effect head to check a Σ against — and the pure value is then
  # lifted with `pure`. `elaborate_effect_branch` does exactly that.
  defp elaborate_branch_body({:tuple, _meta, elems} = expr, expected, names, ctx, env)
       when length(elems) >= 2 do
    if effect_goal?(expected, ctx),
      do: elaborate_effect_branch(expr, expected, names, ctx, env),
      else: elaborate_expr_checked(expr, expected, names, ctx, env)
  end

  # A `[] -> []` (or `[a,b] -> [...]`) arm body: check it against the branch goal
  # so a bare `[]` arm pins its element type from the goal instead of failing
  # infer-only with `{:unsolved_metavariables, :Nil}` (Finding A). `expected` here
  # is the refined branch goal; `elaborate_expr_checked` self-desugars the `:list`.
  # Under an `Effect(R)` goal the element type lives in `R`, so the same detour
  # through the pure-lift applies (a bare `[]` arm would otherwise fail with
  # `{:unsolved_metavariables, :Nil}`).
  defp elaborate_branch_body({:list, _, _} = expr, expected, names, ctx, env) do
    if effect_goal?(expected, ctx),
      do: elaborate_effect_branch(expr, expected, names, ctx, env),
      else: elaborate_expr_checked(expr, expected, names, ctx, env)
  end

  # The general branch body: inferred. `maybe_inject_union/5` is a strict no-op unless
  # this branch's goal is a generated anonymous-union family — in which case the
  # inferred body is injected (a member value) or widened (a narrower union, as
  # produced by a sub-union arm's `assert_type` ascription) into the goal. Without it
  # a sub-union arm's body has the SUB-union's type while the motive demands the wide
  # one, and the kernel rejects the branch with `:branch_type`.
  defp elaborate_branch_body(expr, expected, names, ctx, env) do
    if effect_goal?(expected, ctx) do
      elaborate_effect_branch(expr, expected, names, ctx, env)
    else
      with {:ok, term, type} <- elaborate_expr_typed(expr, names, ctx, env) do
        {:ok, maybe_inject_union(term, type, expected, ctx, env)}
      end
    end
  end

  # `R` of an `Effect(R)` goal, as a Core type. Only call under `effect_goal?/2`.
  defp effect_result_type(expected, ctx) do
    sig = Context.signature(ctx)
    {:veffect_type, result_value} = Normalise.whnf_value(Eval.eval(expected, Context.env(ctx)), sig)

    Quote.reify(result_value, Context.length(ctx), sig)
  end

  @doc false
  def effect_goal?(expected, ctx) do
    value = Eval.eval(expected, Context.env(ctx))
    whnf = Normalise.whnf_value(value, Context.signature(ctx))
    match?({:veffect_type, _}, whnf)
  end

  # Check a branch against its goal, lifting a pure value into `Effect(T)` when
  # direct elaboration shows that it is pure. Direct checking comes first: it
  # lets an expected `Effect(Pid(m))` solve the concrete process-index implicit
  # on `beam_ops self` instead of attempting unconstrained inference.
  @doc false
  def elaborate_effect_branch(expr, expected, names, ctx, env) do
    if effect_goal?(expected, ctx) do
      case expr do
        {:pattern_match, _, _} ->
          elaborate_expr_checked(expr, expected, names, ctx, env)

        {:with_abs, _, _} ->
          elaborate_expr_checked(expr, expected, names, ctx, env)

        {:conditional, _, _} ->
          elaborate_expr_checked(expr, expected, names, ctx, env)

        _ ->
          case elaborate_expr_checked(expr, expected, names, ctx, env) do
            {:ok, _term} = ok ->
              ok

            {:error, checked_error} ->
              case elaborate_expr_typed(expr, names, ctx, env) do
                {:ok, _term, {:veffect_type, _}} ->
                  {:error, checked_error}

                {:ok, _term, type} ->
                  result_type = effect_result_type(expected, ctx)

                  with {:ok, pure_term} <- elaborate_expr_checked(expr, result_type, names, ctx, env) do
                    {:ok, {:effect_pure, maybe_inject_union(pure_term, type, result_type, ctx, env)}}
                  else
                    {:error, _} -> {:error, checked_error}
                  end

                # Inference failed — but an INTRODUCTION FORM has no inference rule
                # at all (a bare data constructor is `:ctor_requires_checking_mode`;
                # a bare `[]` is `{:unsolved_metavariables, :Nil}`), so a pure branch
                # body like `%[:noreply, state]` is never inferable and would never
                # reach the lift above. Check it at the result type and lift, exactly
                # as the trailing expression of an effectful `let`-block does.
                {:error, _} ->
                  result_type = effect_result_type(expected, ctx)

                  case elaborate_expr_checked(expr, result_type, names, ctx, env) do
                    {:ok, pure_term} -> {:ok, effect_pure_for_bind(pure_term, result_type, ctx)}
                    {:error, _} -> {:error, checked_error}
                  end
              end
          end
      end
    else
      with {:ok, term, type} <- elaborate_expr_typed(expr, names, ctx, env) do
        {:ok, maybe_inject_union(term, type, expected, ctx, env)}
      end
    end
  end

  # A `let x = e ⏎ …` block elaborates to the Core `:let` binder:
  # `{:let, Cure.Core.Grade.unrestricted(), T, e, body}`, binding `e` EXACTLY ONCE.
  #
  # Previously this desugared by SURFACE substitution (`body[x := e]`), which
  # re-elaborated `e` at every use site and dropped it entirely at zero uses —
  # the recorded root cause of let-duplication and the join-point residual, and a
  # silent aliasing engine that would defeat any future linearity check.
  # Substitution was kept only because it made a let-bound value *transparent* in
  # a later dependent type; a β-redex binds once but loses that transparency.
  #
  # The Core `:let` supplies both (Idris `Core/TT/Binder.idr` `Let`, Lean
  # `Expr.letE`): ζ makes the variable definitionally its value. Here the
  # elaborator's own context gets the same treatment via `Context.extend_def/3`,
  # so `elaborate_expr_typed` on the remainder sees `x` as its value and dependent
  # lets keep checking. The kernel re-checks the emitted `:let` regardless.
  defp elaborate_let_block([final], expected_core, names, ctx, env) do
    sig = Context.signature(ctx)

    case Normalise.whnf_value(Eval.eval(expected_core, Context.env(ctx)), sig) do
      # The block's result type is `Effect(R)`. The final expression is either
      # already effectful (return it, checked against `Effect(R)`) or a plain
      # value to lift with `pure` — Idris's `do`-block whose last statement is a
      # value gets an implicit `pure` (design 2026-07-09-effect-type-former §5.1).
      {:veffect_type, r_val} ->
        r_reified = Quote.reify(r_val, Context.length(ctx), sig)

        case elaborate_expr_typed(final, names, ctx, env) do
          {:ok, _core, ty} ->
            case Normalise.whnf_value(ty, sig) do
              # Already effectful — check against `Effect(R)` and keep it.
              {:veffect_type, _} ->
                elaborate_expr_checked(final, expected_core, names, ctx, env)

              # A pure value — check at `R` and wrap in `pure`.
              _ ->
                with {:ok, r_core} <- elaborate_expr_checked(final, r_reified, names, ctx, env) do
                  {:ok, effect_pure_for_bind(r_core, r_reified, ctx)}
                end
            end

          # Non-inferable final: try the pure-wrap; if THAT fails too, surface the
          # original inference error rather than the (likely less informative) one.
          {:error, _} = err ->
            case elaborate_expr_checked(final, r_reified, names, ctx, env) do
              {:ok, r_core} -> {:ok, effect_pure_for_bind(r_core, r_reified, ctx)}
              {:error, _} -> err
            end
        end

      # A pure block — the existing behaviour.
      _ ->
        elaborate_expr_checked(final, expected_core, names, ctx, env)
    end
  end

  defp elaborate_let_block(
         [{:macro_check, _meta, [condition, failure]} | rest],
         expected_core,
         names,
         ctx,
         env
       )
       when rest != [] do
    with {:ok, condition_core} <-
           elaborate_expr_checked(condition, bool_type_term(Context.signature(ctx)), names, ctx, env),
         {:ok, failure_core} <- elaborate_expr_checked(failure, expected_core, names, ctx, env),
         {:ok, body_core} <- elaborate_let_block(rest, expected_core, names, ctx, env) do
      {:ok, bool_case(condition_core, expected_core, body_core, failure_core, ctx)}
    end
  end

  defp elaborate_let_block(
         [{:assignment, meta, [{:variable, _, name}, rhs]} | rest],
         expected_core,
         names,
         ctx,
         env
       ) do
    if not Keyword.get(meta, :let, false) do
      {:error, {:unsupported_block_statement, meta}}
    else
      # A surface grade (`let c :linear = e`, plan slice 5b); absent means ω.
      grade = Keyword.get(meta, :grade, Grade.unrestricted())

      case Keyword.get(meta, :type_annotation) do
        nil -> let_inferred(name, rhs, meta, grade, rest, expected_core, names, ctx, env)
        ann -> let_ascribed(name, rhs, ann, grade, rest, expected_core, names, ctx, env)
      end
    end
  end

  defp elaborate_let_block(other, _expected_core, _names, _ctx, _env),
    do: {:error, {:unsupported_block, other}}

  defp elaborate_macro_failure(meta, args, names, ctx, env) do
    syntax_family = Env.resolve_key(env, env.families, :Syntax)
    syntax_type = {:data, syntax_family, [], []}

    with {:ok, arg_terms} <-
           Enum.reduce_while(args, {:ok, []}, fn arg, {:ok, acc} ->
             case elaborate_expr_checked(arg, syntax_type, names, ctx, env) do
               {:ok, term} -> {:cont, {:ok, [term | acc]}}
               {:error, _} = error -> {:halt, error}
             end
           end),
         %{name: failure_ctor} <- Inductive.get_ctor(env, :Failure) do
      name = Keyword.get(meta, :name, "?")
      {:ok, {:ctor, failure_ctor, [{:atom_lit, String.to_atom(name)}, core_list(Enum.reverse(arg_terms))]}}
    else
      nil -> {:error, {:unknown_macro_failure, Keyword.get(meta, :name, "?")}}
    end
  end

  defp core_list(items), do: Enum.reduce(Enum.reverse(items), {:ctor, :Nil, []}, &{:ctor, :Cons, [&1, &2]})

  # INFERENCE-mode block: build the `:let` Core chain (the final statement is
  # inferred, each `let` binds its rhs with a ζ definition so a later statement
  # sees the concrete value) and return only the term — the `{:block}` clause of
  # `elaborate_expr_typed/4` hands it to `Kernel.infer` for its type. Mirrors
  # `elaborate_let_block/5`/`bind_once_let/10`, minus the threaded expected type.
  defp infer_block_term([final], names, ctx, env) do
    with {:ok, term, _type} <- elaborate_expr_typed(final, names, ctx, env), do: {:ok, term}
  end

  defp infer_block_term(
         [{:assignment, meta, [{:variable, _, name}, rhs]} | rest],
         names,
         ctx,
         env
       ) do
    if not Keyword.get(meta, :let, false) do
      {:error, {:unsupported_block_statement, meta}}
    else
      grade = Keyword.get(meta, :grade, Grade.unrestricted())

      with {:ok, rhs_core, ty_core, ty_value} <- block_rhs(rhs, meta, names, ctx, env) do
        rhs_value = Eval.eval(rhs_core, Context.env(ctx))
        ctx1 = Context.extend_def(ctx, ty_value, rhs_value)

        with {:ok, body_core} <- infer_block_term(rest, [name | names], ctx1, env) do
          {:ok, {:let, grade, ty_core, rhs_core, body_core}}
        end
      end
    end
  end

  defp infer_block_term(other, _names, _ctx, _env), do: {:error, {:unsupported_block, other}}

  # A `let` binding's rhs, settled to `{rhs_core, ty_core, ty_value}`. An
  # unannotated `let x = e` synthesises `e`'s type (SIGNATURE-AWARE reify, as
  # `let_inferred/9`); an ascribed `let x : T = e` checks `e` against `T`.
  defp block_rhs(rhs, meta, names, ctx, env) do
    case Keyword.get(meta, :type_annotation) do
      nil ->
        with {:ok, rhs_core, rhs_type} <- elaborate_expr_typed(rhs, names, ctx, env) do
          ty_core = Quote.reify(rhs_type, Context.length(ctx), Context.signature(ctx))
          {:ok, rhs_core, ty_core, rhs_type}
        end

      ann ->
        with {:ok, ty_core} <- elaborate_type(ann, names, env),
             {:ok, rhs_core} <- elaborate_expr_checked(rhs, ty_core, names, ctx, env) do
          {:ok, rhs_core, ty_core, Eval.eval(ty_core, Context.env(ctx))}
        end
    end
  end

  # `let x : T = e` — BIDIRECTIONAL. The ascription supplies the type a
  # check-only rhs cannot synthesise, so the rhs is elaborated in CHECKING mode
  # (exactly what surface substitution did at each use site) and bound ONCE.
  # This is the general escape from the check-only residual.
  defp let_ascribed(name, rhs, ann, grade, rest, expected_core, names, ctx, env) do
    with {:ok, ty_core} <- elaborate_type(ann, names, env),
         ty_value = Eval.eval(ty_core, Context.env(ctx)) do
      case Normalise.whnf_value(ty_value, Context.signature(ctx)) do
        {:veffect_type, _} ->
          with {:ok, rhs_core} <- elaborate_expr_checked(rhs, ty_core, names, ctx, env) do
            bind_once_let(name, rhs_core, ty_core, ty_value, grade, rest, expected_core, names, ctx, env)
          end

        _ ->
          effect_type = {:effect_type, ty_core}

          case elaborate_expr_checked(rhs, effect_type, names, ctx, env) do
            {:ok, rhs_core} ->
              effectful_let_bind(
                name,
                rhs_core,
                ty_value,
                grade,
                rest,
                expected_core,
                names,
                ctx,
                env
              )

            {:error, _} ->
              with {:ok, rhs_core} <- elaborate_expr_checked(rhs, ty_core, names, ctx, env) do
                bind_once_let(name, rhs_core, ty_core, ty_value, grade, rest, expected_core, names, ctx, env)
              end
          end
      end
    end
  end

  # `let x = e` — synthesise `e`'s type, then bind once.
  defp let_inferred(name, rhs, meta, grade, rest, expected_core, names, ctx, env) do
    case elaborate_expr_typed(rhs, names, ctx, env) do
      {:ok, rhs_core, rhs_type} ->
        case Normalise.whnf_value(rhs_type, Context.signature(ctx)) do
          # An EFFECTFUL rhs: `let x = eff()` where `eff() : Effect(T)`. Do NOT
          # bind `x : Effect(T)` via `:let`; sequence with `bind`, whose
          # continuation binds `x : T` — the UNWRAPPED payload the effect
          # produces (Idris's `x <- eff; rest` ⟶ `bind eff (λ x:T. rest)`,
          # design 2026-07-09-effect-type-former §5.1). The kernel re-checks the
          # emitted `effect_bind`.
          {:veffect_type, payload_val} ->
            # A surface grade (`let r :linear = eff()`) rides onto the `bind`
            # continuation's binder — the effect's RESULT `r` is used per `grade`
            # (linear channels: used exactly once). Relevance enforces it; the
            # kernel's `bind` accepts the continuation's own grade.
            effectful_let_bind(name, rhs_core, payload_val, grade, rest, expected_core, names, ctx, env)

          # A PURE rhs — the existing path. SIGNATURE-AWARE reify: a
          # `{:vdata, name, args}` value flattens a family's params and indices
          # into one list; without the signature the split is not recoverable and
          # the read-back puts them all in `params`, so a `:let` over an indexed
          # family fails the kernel's arity check (`:arg_arity`). Agda
          # `getNumberOfParameters` / Lean `inductive_val.get_nparams`.
          _ ->
            ty_core = Quote.reify(rhs_type, Context.length(ctx), Context.signature(ctx))
            bind_once_let(name, rhs_core, ty_core, rhs_type, grade, rest, expected_core, names, ctx, env)
        end

      # The rhs has no INFERABLE type — a bare lambda, an `if`/`pickup`, any
      # check-only shape. Surface substitution never had to infer it: it
      # re-elaborated the rhs in CHECKING mode at each use site. A `:let` must
      # commit to one type up front, so it needs `let x : T = e` (`let_ascribed/8`).
      {:error, _} = err ->
        cond do
          # A GRADE cannot survive this branch. Every path below abandons the `:let`
          # node and surface-substitutes the rhs, so there is nowhere to record the
          # grade and it would be silently dropped — the program would compile, pass,
          # and lie about its linearity. A graded `let` must produce a real `:let`.
          # Ascribing the binding gives `let_ascribed/9`, which always builds one.
          Keyword.has_key?(meta, :grade) ->
            {:error, {:graded_let_needs_annotation, name, meta}}

          # Shadowing + non-inferable is unrepresentable: substitution would
          # capture and `:let` cannot be built. Surface the inference error.
          Enum.any?(rest, &binds_any?(&1, [name])) ->
            err

          # Substitution is only safe at EXACTLY ONE use:
          #
          #   * ≥2 uses  — it DUPLICATES the rhs. That is what made surface
          #     substitution a silent aliasing engine.
          #   * 0 uses   — it DROPS the rhs, which is therefore never elaborated:
          #     an ill-typed unused binding sails through to a green build.
          #     (It also means a zero-use binding would not RUN once effects
          #     arrive — that is `effect_bind`'s job, not this path's.)
          #
          # Both are refused, and the message says how to fix it: ascribe the
          # binding (`let x : T = e`) and it binds once, checked.
          count_surface_uses(rest, name) != 1 ->
            {:error, {:let_needs_annotation, name, meta}}

          # Exactly one use: the rhs is elaborated once, in checking mode, at that
          # use site. No duplication, and it IS type-checked.
          true ->
            rest
            |> Enum.map(&subst_surface_var(&1, name, rhs))
            |> elaborate_let_block(expected_core, names, ctx, env)
        end
    end
  end

  # `let x : T = e ⏎ rest`  ⟶  `{:let, Cure.Core.Grade.unrestricted(), T, e, rest}` with `x := e` in the context.
  defp bind_once_let(name, rhs_core, ty_core, ty_value, grade, rest, expected_core, names, ctx, env) do
    rhs_value = Eval.eval(rhs_core, Context.env(ctx))

    # `extend_def/3`, not `extend/2`: the binder is definitionally its value (ζ),
    # so a later `SNat(k)` sees `k`'s concrete value — the one thing a β-redex
    # cannot give. A shadowing binder deeper in `rest` correctly shadows this de
    # Bruijn binder, so no capture guard is needed on this path.
    ctx1 = Context.extend_def(ctx, ty_value, rhs_value)
    names1 = [name | names]
    expected1 = Subst.shift(expected_core, 1, 0)

    with {:ok, body_core} <- elaborate_let_block(rest, expected1, names1, ctx1, env) do
      {:ok, {:let, grade, ty_core, rhs_core, body_core}}
    end
  end

  # `let x = eff  ⏎ rest`  where `eff : Effect(T)`  ⟶  `bind(eff, λ x:T. rest)`.
  #
  # The continuation binds the UNWRAPPED payload `x : T` as an OPAQUE binder
  # (`extend/2`, not `extend_def/3`): the effect's result is NOT definitionally
  # known — it is whatever the effect will produce at run time — so `x` must stay
  # a variable, unlike a pure `let` whose value is transparent (ζ).
  #
  # de Bruijn: `t_core` is the lambda's DOMAIN, well-formed OUTSIDE its own binder,
  # so it is reified at the current depth `Context.length(ctx)`. `rest` is the
  # lambda BODY, elaborated under one new binder (`ctx1`, `names1`), so the block's
  # expected type is shifted by one (`expected1`). The kernel re-checks the node.
  defp effectful_let_bind(name, rhs_core, payload_val, grade, rest, expected_core, names, ctx, env) do
    t_core = Quote.reify(payload_val, Context.length(ctx), Context.signature(ctx))
    ctx1 = Context.extend(ctx, payload_val)
    names1 = [name | names]
    expected1 = Subst.shift(expected_core, 1, 0)

    with {:ok, body_core} <- elaborate_let_block(rest, expected1, names1, ctx1, env) do
      {:ok, {:effect_bind, rhs_core, {:lam, grade, t_core, body_core}}}
    end
  end

  # `effect_bind` is inferred without a continuation result goal. A pure tuple
  # therefore cannot be inferred directly inside `effect_pure`, even after it
  # has been checked against the surrounding effect result. Bind the checked
  # payload with an ordinary Core let so the continuation infers `pure(var)`
  # from the let domain. The let is erased by the normal emitter and preserves
  # the single evaluation of the payload.
  defp effect_pure_for_bind(core, type_core, ctx) do
    case Kernel.infer(ctx, {:effect_pure, core}) do
      {:ok, _} ->
        {:effect_pure, core}

      {:error, _} ->
        {:let, Grade.unrestricted(), type_core, core, {:effect_pure, {:var, 0}}}
    end
  end

  # Free occurrences of surface variable `name` in the remaining statements.
  # Mirrors `subst_surface_var/3`'s traversal (which is likewise shadowing-blind;
  # the shadowing case is rejected before either is reached).
  defp count_surface_uses(list, name) when is_list(list),
    do: Enum.reduce(list, 0, &(count_surface_uses(&1, name) + &2))

  defp count_surface_uses({:variable, _meta, name}, name), do: 1

  defp count_surface_uses({_tag, _meta, children}, name) when is_list(children),
    do: Enum.reduce(children, 0, &(count_surface_uses(&1, name) + &2))

  defp count_surface_uses(_other, _name), do: 0

  # Surface-level scrutinee refinement (Lean `Cases.lean:219-227`): in a branch,
  # a VARIABLE scrutinee *is* the pattern, so free occurrences of its name in
  # the branch body are replaced by the pattern expression. Bails out — leaving
  # today's behavior, which the kernel re-check keeps sound — when the name does
  # not uniquely resolve to the scrutinee (an inner binding shadows it), when
  # the pattern itself rebinds the name, or when a nested match arm binds a name
  # that would shadow the scrutinee or capture a pattern var.
  defp refine_scrutinee_in_body(body_expr, {:var, i}, pattern, pattern_vars, names) do
    scrut_name = Enum.at(names, i)

    stripped = strip_named_implicits(pattern)

    if is_binary(scrut_name) and
         Enum.find_index(names, &(&1 == scrut_name)) == i and
         scrut_name not in pattern_vars and
         expressible_pattern?(stripped) and
         not binds_any?(body_expr, [scrut_name | pattern_vars]) do
      subst_surface_var(body_expr, scrut_name, stripped)
    else
      body_expr
    end
  end

  defp refine_scrutinee_in_body(body_expr, _scrut_term, _pattern, _pattern_vars, _names),
    do: body_expr

  # Can this branch pattern be rendered into TERM position? A wildcard `_` has
  # no value, so a pattern containing one (`[_ | _]`) is not expressible; the
  # surface scrutinee-refinement must be skipped for it (the scrutinee variable
  # stays in branch scope with its original type and the body checks against
  # that directly). Rendering `[_ | _]` as an expression resolved both `_`s to
  # the head element binder and mis-typed the tail slot.
  defp expressible_pattern?({:variable, _meta, "_"}), do: false

  defp expressible_pattern?({_tag, _meta, children}) when is_list(children),
    do: Enum.all?(children, &expressible_pattern?/1)

  defp expressible_pattern?(list) when is_list(list),
    do: Enum.all?(list, &expressible_pattern?/1)

  defp expressible_pattern?(_other), do: true

  defp subst_surface_var({:variable, _meta, name}, name, replacement), do: replacement

  defp subst_surface_var({tag, meta, children}, name, replacement) when is_list(children),
    do:
      {tag, subst_surface_meta(meta, name, replacement), Enum.map(children, &subst_surface_var(&1, name, replacement))}

  defp subst_surface_var(other, _name, _replacement), do: other

  # A curried call `f(x)(y)` parses with its callee expression stashed in META
  # (`callee:`, parser.ex `parse_call`), NOT in the node's children — so the
  # generic child walk above would skip any variable inside the callee. Rewrite
  # the `:callee` sub-expression too, or a nested-match desugaring (or a `let`)
  # that renames `x` leaves the `x` inside `f(x)` untouched, and it reaches the
  # kernel as an undefined `{:global, :x}`.
  defp subst_surface_meta(meta, name, replacement) when is_list(meta) do
    case Keyword.fetch(meta, :callee) do
      {:ok, callee} ->
        Keyword.put(meta, :callee, subst_surface_var(callee, name, replacement))

      :error ->
        meta
    end
  end

  # Does any nested binder in the remaining statements bind one of `avoid`?
  #
  # This guards `elaborate_let_block`'s surface-substitution branch against CAPTURE.
  # Answering `false` sends the block down the substitution path, so a binder we fail
  # to see here silently rewrites a position it must not touch. Both binding forms
  # must be recognized:
  #
  #   * a match arm's pattern — which lives in the arm's META, not its children, so
  #     the generic child walk never sees it. Previously only a `{:function_call, …}`
  #     pattern's DIRECT variable arguments were collected, so a bare catch-all arm
  #     (`x -> S(x)`) and any nested/aliased pattern went unnoticed.
  #   * a lambda's parameters — likewise in META (`params:`), not children. A lambda
  #     shadowing an outer `let` name had its body rewritten, so `let x = Z()` turned
  #     `fn(x) -> S(x)` into `fn(x) -> S(Z())`: still well-typed, kernel-accepted, and
  #     computing the wrong value.
  #
  # Over-reporting merely costs the (safe) bind-once β-redex path; under-reporting is a
  # miscompilation. When in doubt, say true.
  defp binds_any?({:match_arm, meta, body}, avoid) do
    vars = meta |> Keyword.get(:pattern) |> pattern_binders()
    Enum.any?(vars, &(&1 in avoid)) or binds_any?(body, avoid)
  end

  defp binds_any?({:lambda, meta, children}, avoid) do
    params = for {:param, _pmeta, p} <- Keyword.get(meta, :params, []), do: p

    Enum.any?(params, &(&1 in avoid)) or
      children |> List.wrap() |> Enum.any?(&binds_any?(&1, avoid))
  end

  defp binds_any?({_tag, _meta, children}, avoid) when is_list(children),
    do: Enum.any?(children, &binds_any?(&1, avoid))

  defp binds_any?(list, avoid) when is_list(list),
    do: Enum.any?(list, &binds_any?(&1, avoid))

  defp binds_any?(_other, _avoid), do: false

  # Every name a pattern binds. In pattern position every `{:variable, _, v}` node IS a
  # binder, at any depth — nested constructor arguments, as-patterns, list/tuple
  # patterns. Constructor NAMES live in meta (`name:`), never as children, so this
  # never mistakes a constructor for a binder.
  defp pattern_binders({:variable, _meta, v}), do: [v]

  # `n: Int` (a UNION type member) or `rest: Bool | Atom` (a sub-union) — the bound
  # name is a bare STRING in the child list (`parser.ex` `maybe_wrap_as/2`'s `:colon`
  # clause), not a `{:variable, …}` node, so the generic clause below would silently
  # miss it: `Enum.flat_map(["n", type_ast], &pattern_binders/1)` finds nothing for the
  # bare string "n" and instead picks up names from `type_ast` (e.g. "Int"), which are
  # TYPE references, not binders. Without this clause, `binds_any?/2` — the capture
  # guard `elaborate_let_block` and every other surface-substitution site relies on —
  # silently fails to see a typed-pattern's shadowing, letting `let n = <check-only
  # rhs>` substitute straight through a later `n: Int -> n` arm and rewrite the INNER,
  # freshly-matched `n` into the OUTER let-bound expression.
  defp pattern_binders({:typed_pattern, _meta, [name, _type_ast]}) when is_binary(name),
    do: [name]

  defp pattern_binders({_tag, _meta, children}) when is_list(children),
    do: Enum.flat_map(children, &pattern_binders/1)

  defp pattern_binders(list) when is_list(list), do: Enum.flat_map(list, &pattern_binders/1)
  defp pattern_binders(_other), do: []

  # Wave-2 List sugar → ctor-call surface form (reuses all ctor machinery).
  #   []            -> Nil()
  #   [h | t]       -> Cons(h, t)              (meta carries `cons: true`)
  #   [e1, …, eN]   -> Cons(e1, Cons(…, Nil))  (right fold)
  # Recurses into sub-elements/sub-patterns so a list-of-lists desugars fully.
  # `m` threads the original node's line/col into the synthesized ctor calls.
  defp desugar_list({:list, m, []}), do: ctor_call("Nil", m, [])

  defp desugar_list({:list, m, [h, t]} = _node) do
    if Keyword.get(m, :cons, false) do
      ctor_call("Cons", m, [desugar_list(h), desugar_list(t)])
    else
      # a 2-element literal (no cons flag) folds like any other literal
      fold_list_literal([h, t], m)
    end
  end

  defp desugar_list({:list, m, elems}), do: fold_list_literal(elems, m)
  defp desugar_list(other), do: other

  # Wadler comprehension translation, right-folded over the qualifier list. The
  # body of an exhausted qualifier list is a singleton `[e]`; a generator wraps
  # the remainder in a `flat_map` lambda; a filter guards it with `if … else []`.
  defp desugar_comprehension([], body, line), do: {:ok, {:list, [line: line], [body]}}

  defp desugar_comprehension([{:generator, _gm, [pat, source]} | rest], body, line) do
    with {:ok, param} <- generator_param(pat),
         {:ok, inner} <- desugar_comprehension(rest, body, line) do
      lambda = {:lambda, [params: [param], line: line], [inner]}
      {:ok, {:function_call, [name: "flat_map", line: line], [source, lambda]}}
    end
  end

  # A byte generator is an ordinary list generator after the standard-library
  # byte view has been applied. Sized/typed bit segments remain a deliberate
  # unsupported extension until their runtime representation exists.
  defp desugar_comprehension([{:binary_generator, _gm, [pattern, source]} | rest], body, line) do
    with {:ok, param} <- binary_generator_param(pattern),
         {:ok, inner} <- desugar_comprehension(rest, body, line) do
      lambda = {:lambda, [params: [param], line: line], [inner]}
      bytes = {:function_call, [name: "to_bytes", line: line], [source]}
      {:ok, {:function_call, [name: "flat_map", line: line], [bytes, lambda]}}
    end
  end

  defp desugar_comprehension([qual | rest], body, line) do
    cond_ast =
      case qual do
        {:filter, _fm, [c]} -> c
        other -> other
      end

    with {:ok, inner} <- desugar_comprehension(rest, body, line) do
      {:ok, {:conditional, [line: line], [cond_ast, inner, {:list, [line: line], []}]}}
    end
  end

  # A generator binds a single variable in this first port; a destructuring
  # generator (`{a, b} <- xs`) is rejected rather than silently mistyped.
  defp generator_param({:variable, _m, name}), do: {:ok, {:param, [], name}}
  defp generator_param(other), do: {:error, {:unsupported_comprehension_pattern, other}}

  defp binary_generator_param({:literal, meta, [{:bin_segment, segment_meta, [pattern]}]}) do
    if Keyword.get(meta, :subtype) == :bytes and
         is_nil(Keyword.get(segment_meta, :size)) and
         is_nil(Keyword.get(segment_meta, :type)) do
      generator_param(pattern)
    else
      {:error, {:unsupported_binary_generator_pattern, pattern}}
    end
  end

  defp binary_generator_param(pattern),
    do: {:error, {:unsupported_binary_generator_pattern, pattern}}

  # `%{k: v, …}` → nested `Std.Map.put(k, v, …)` over `Std.Map.new()`. `%{}`
  # folds to a bare `new()`. Shared by the typed and checked map clauses.
  defp desugar_map(pairs, line) do
    Enum.reduce(Enum.reverse(pairs), {:function_call, [name: "new", line: line], []}, fn
      {:pair, _pm, [key, value]}, acc ->
        {:function_call, [name: "put", line: line], [key, value, acc]}
    end)
  end

  # A `match` whose arms are map patterns cannot go through the constructor-match
  # machinery (an Erlang map is not a Cure inductive). Map matching is OPEN — keys
  # absent from the pattern are ignored — so it desugars to `has_key`-guarded
  # conditionals over `Std.Map`, exactly the shape a hand-written lookup takes:
  #
  #   match m
  #     %{a: v, tag: :hit} -> body
  #     _                  -> default
  #
  #   ⇒ if has_key(:a, m) and has_key(:tag, m) and get(:tag, m) == :hit
  #        then (let v = get(:a, m); body)
  #        else default
  #
  # Because matching is open it is non-exhaustive, so the arm list MUST end in a
  # wildcard/variable default. Value positions are variable binders, `_`, or
  # literals (an equality guard). The enclosing module must `use Std.Map` so the
  # emitted `has_key`/`get` resolve, like map literals.
  def map_match_arms?(arms) do
    Enum.any?(arms, fn
      {:match_arm, meta, _body} when is_list(meta) ->
        match?({:map, _m, _pairs}, Keyword.get(meta, :pattern))

      _ ->
        false
    end)
  end

  # A binary pattern arm is a `:bytes` literal used as a match pattern.
  def binary_match_arms?(arms) do
    Enum.any?(arms, fn
      {:match_arm, meta, _body} when is_list(meta) ->
        case Keyword.get(meta, :pattern) do
          {:literal, lmeta, segs} when is_list(lmeta) and is_list(segs) ->
            Keyword.get(lmeta, :subtype) == :bytes

          _ ->
            false
        end

      _ ->
        false
    end)
  end

  # Map and byte-binary patterns are not Cure inductives, so a `match` carrying
  # them desugars (surface → surface) to guarded conditionals rather than going
  # through the constructor-match machinery. Both entry-point modes share this.
  def special_match_arms?(arms), do: map_match_arms?(arms) or binary_match_arms?(arms)

  def desugar_special_match(scrut, arms, line) do
    cond do
      map_match_arms?(arms) -> desugar_map_arms(scrut, arms, line)
      binary_match_arms?(arms) -> desugar_binary_arms(scrut, arms, line)
    end
  end

  def desugar_map_match(scrut, arms, line), do: desugar_map_arms(scrut, arms, line)

  # A wildcard/variable arm terminates the chain: `_` yields its body directly, a
  # named binder binds the whole scrutinee first.
  defp desugar_map_arms(_scrut, [], _line), do: {:error, {:map_match_needs_default}}

  defp desugar_map_arms(scrut, [{:match_arm, meta, [body]} | rest], line) do
    case Keyword.get(meta, :pattern) do
      {:map, _mm, pairs} ->
        with {:ok, presence, value_eqs, binds} <- map_arm_guard_binds(scrut, pairs, line),
             {:ok, else_expr} <- desugar_map_arms(scrut, rest, line) do
          # Cure's `and` is strict, so a value `get` must never run on an absent
          # key: gate all `get`s behind the (total) presence guard structurally.
          # Only once every listed key is present are the value-equality checks
          # and the binding `get`s evaluated.
          then_body = if binds == [], do: body, else: {:block, [line: line], binds ++ [body]}

          inner =
            case value_eqs do
              [] -> then_body
              _ -> {:conditional, [line: line], [conjoin(value_eqs, line), then_body, else_expr]}
            end

          {:ok, {:conditional, [line: line], [conjoin(presence, line), inner, else_expr]}}
        end

      {:variable, _vm, "_"} ->
        {:ok, body}

      {:variable, vm, name} ->
        bind = {:assignment, [let: true, line: line], [{:variable, vm, name}, scrut]}
        {:ok, {:block, [line: line], [bind, body]}}

      other ->
        {:error, {:unsupported_map_match_arm, other}}
    end
  end

  # Fold a map pattern's pairs into (a) presence guards — every listed key must be
  # present (`has_key`, total), (b) value-equality guards for literal positions
  # (`get(k) == lit`, evaluated only after presence holds), and (c) the `let`
  # bindings for variable value positions.
  defp map_arm_guard_binds(scrut, pairs, line) do
    Enum.reduce_while(pairs, {:ok, [], [], []}, fn
      {:pair, _pm, [{:literal, kmeta, key}, valpat]}, {:ok, presence, value_eqs, binds}
      when is_atom(key) ->
        if Keyword.get(kmeta, :subtype) in [:symbol, :atom] do
          key_lit = {:literal, [subtype: :symbol], key}
          present = mk_call("has_key", [key_lit, scrut], line)

          case valpat do
            {:variable, _vm, "_"} ->
              {:cont, {:ok, presence ++ [present], value_eqs, binds}}

            {:variable, _vm, _name} ->
              bind =
                {:assignment, [let: true, line: line], [valpat, mk_call("get", [key_lit, scrut], line)]}

              {:cont, {:ok, presence ++ [present], value_eqs, binds ++ [bind]}}

            {:literal, _lm, _lv} = lit ->
              eq =
                {:binary_op, [category: :comparison, operator: :==, line: line],
                 [mk_call("get", [key_lit, scrut], line), lit]}

              {:cont, {:ok, presence ++ [present], value_eqs ++ [eq], binds}}

            other ->
              {:halt, {:error, {:unsupported_map_value_pattern, other}}}
          end
        else
          {:halt, {:error, {:unsupported_map_key_pattern, key}}}
        end

      {:pair, _pm, [other_key, _v]}, _acc ->
        {:halt, {:error, {:unsupported_map_key_pattern, other_key}}}
    end)
    |> case do
      {:ok, presence, value_eqs, binds} -> {:ok, presence, value_eqs, binds}
      {:error, _} = e -> e
    end
  end

  # An empty pattern `%{}` matches any map, so an absent guard is `true`.
  defp conjoin([], _line), do: {:literal, [subtype: :boolean], true}
  defp conjoin([g], _line), do: g

  defp conjoin([g | rest], line),
    do: {:binary_op, [category: :boolean, operator: :and, line: line], [g, conjoin(rest, line)]}

  defp mk_call(name, args, line), do: {:function_call, [name: name, line: line], args}

  # Byte-binary patterns, the destructuring twin of `desugar_map_arms`. A match
  # whose arms are `<<…>>` patterns desugars to `byte_size`-guarded conditionals
  # over `Std.Binary`: the length guard (`==` for a fixed pattern, `>=` when a
  # `rest/binary` tail is present) gates the byte reads, then literal byte
  # positions add `byte_at(b, i) == lit` guards and variable positions bind
  # `byte_at(b, i)` / `drop_bytes(b, k)`. Open-ended, so a trailing default arm is
  # required. Sized/typed segments (`x/float`) are rejected, not mislowered.
  defp desugar_binary_arms(_scrut, [], _line), do: {:error, {:binary_match_needs_default}}

  defp desugar_binary_arms(scrut, [{:match_arm, meta, [body]} | rest], line) do
    case Keyword.get(meta, :pattern) do
      {:literal, lmeta, segs} = pat ->
        if Keyword.get(lmeta, :subtype) == :bytes do
          with {:ok, length_guard, value_guards, binds} <- binary_arm_guard_binds(scrut, segs, line),
               {:ok, else_expr} <- desugar_binary_arms(scrut, rest, line) do
            then_body = if binds == [], do: body, else: {:block, [line: line], binds ++ [body]}

            inner =
              case value_guards do
                [] -> then_body
                _ -> {:conditional, [line: line], [conjoin(value_guards, line), then_body, else_expr]}
              end

            {:ok, {:conditional, [line: line], [length_guard, inner, else_expr]}}
          end
        else
          {:error, {:unsupported_binary_match_arm, pat}}
        end

      {:variable, _vm, "_"} ->
        {:ok, body}

      {:variable, vm, name} ->
        bind = {:assignment, [let: true, line: line], [{:variable, vm, name}, scrut]}
        {:ok, {:block, [line: line], [bind, body]}}

      other ->
        {:error, {:unsupported_binary_match_arm, other}}
    end
  end

  # Split a byte pattern's segments into (a) the length guard, (b) literal-byte
  # equality guards, and (c) the variable/tail `let` bindings. The optional
  # `rest/binary` tail must come last; any other typed segment is rejected.
  defp binary_arm_guard_binds(scrut, segs, line) do
    {fixed, tail} = split_binary_tail(segs)

    with {:ok, value_guards, binds} <- fixed_byte_guards(scrut, fixed, line),
         {:ok, tail_binds} <- tail_bind(scrut, tail, length(fixed), line) do
      n = {:literal, [subtype: :integer, line: line], length(fixed)}
      size = mk_call("byte_size", [scrut], line)

      op = if tail == :none, do: :==, else: :>=
      length_guard = {:binary_op, [category: :comparison, operator: op, line: line], [size, n]}

      {:ok, length_guard, value_guards, binds ++ tail_binds}
    end
  end

  # The last segment is a tail iff it is a `_v/binary` (division-marker) segment.
  defp split_binary_tail(segs) do
    case List.last(segs) do
      {:bin_segment, _sm, [{:binary_op, opm, [v, {:variable, _tm, "binary"}]}]} = seg ->
        if Keyword.get(opm, :operator) == :/ do
          {segs |> Enum.reverse() |> tl() |> Enum.reverse(), {:tail, v, seg}}
        else
          {segs, :none}
        end

      _ ->
        {segs, :none}
    end
  end

  defp fixed_byte_guards(scrut, segs, line) do
    segs
    |> Enum.with_index()
    |> Enum.reduce_while({:ok, [], []}, fn {seg, i}, {:ok, guards, binds} ->
      idx = {:literal, [subtype: :integer, line: line], i}

      case seg do
        {:bin_segment, _sm, [{:variable, _vm, "_"}]} ->
          {:cont, {:ok, guards, binds}}

        {:bin_segment, _sm, [{:variable, _vm, _name} = v]} ->
          bind = {:assignment, [let: true, line: line], [v, mk_call("byte_at", [scrut, idx], line)]}
          {:cont, {:ok, guards, binds ++ [bind]}}

        {:bin_segment, _sm, [{:literal, _lm, byteval} = lit]} when is_integer(byteval) ->
          eq =
            {:binary_op, [category: :comparison, operator: :==, line: line],
             [mk_call("byte_at", [scrut, idx], line), lit]}

          {:cont, {:ok, guards ++ [eq], binds}}

        other ->
          {:halt, {:error, {:unsupported_binary_segment, other}}}
      end
    end)
  end

  defp tail_bind(_scrut, :none, _n, _line), do: {:ok, []}

  defp tail_bind(scrut, {:tail, tailvar, seg}, n, line) do
    case tailvar do
      {:variable, _tm, "_"} ->
        {:ok, []}

      {:variable, _tm, _name} ->
        nlit = {:literal, [subtype: :integer, line: line], n}
        {:ok, [{:assignment, [let: true, line: line], [tailvar, mk_call("drop_bytes", [scrut, nlit], line)]}]}

      _ ->
        {:error, {:unsupported_binary_segment, seg}}
    end
  end

  # `<<b1, b2, …>>` → `Std.Binary.of_bytes([b1, b2, …])`: a byte binary literal is
  # a list of byte values packed into a BEAM binary. Only default 8-bit-integer
  # segments are supported here; a `/type` segment (`x/float`, `x/binary`) is a
  # deferred rich-bit-syntax case and is rejected rather than mislowered. The
  # module must `use Std.Binary`.
  # `"a#{e}b"` → `str_concat("a", str_concat(e, "b"))`: a right fold over the
  # segments. Literal chunks stay `:string` literals (each desugars to its
  # `List(Char)`); holes are the segment expressions unchanged, so a hole is
  # elaborated against `str_concat`'s `List(Char)` parameter — a String hole
  # checks, a non-String hole is a type error (Show-based conversion is #21).
  # `str_concat` is auto-preluded (`Std.Binary`), so no import is required.
  defp desugar_interpolation(segments, line) do
    case Enum.reverse(segments) do
      [] ->
        {:literal, [subtype: :string, line: line], ""}

      [last | rest] ->
        Enum.reduce(rest, last, fn seg, acc -> mk_call("str_concat", [seg, acc], line) end)
    end
  end

  # Rich bit-syntax specifiers (`::16`, `/float`, `::size(n)`, unit/signedness/
  # endianness) live in the segment meta after parsing. `of_bytes` packs a list
  # of 8-bit bytes and cannot express any of them, so a sized/typed segment is
  # REJECTED here rather than silently mislowered — dropping a `::16` size would
  # feed a >255 value to `list_to_binary` and crash at runtime. Rich bit-syntax
  # construction is a deferred value-surface case in the dependent pipeline.
  @rich_segment_keys [:size, :type, :unit, :signedness, :endianness]

  def desugar_bytes(segments, line) do
    Enum.reduce_while(segments, {:ok, []}, fn
      {:bin_segment, sm, [expr]} = seg, {:ok, acc} ->
        cond do
          Enum.any?(@rich_segment_keys, &(Keyword.get(sm, &1) != nil)) ->
            {:halt, {:error, {:unsupported_binary_segment, seg}}}

          typed_segment?(expr) ->
            {:halt, {:error, {:unsupported_binary_segment, expr}}}

          true ->
            {:cont, {:ok, acc ++ [expr]}}
        end

      other, _acc ->
        {:halt, {:error, {:unsupported_binary_segment, other}}}
    end)
    |> case do
      {:ok, values} ->
        {:ok, mk_call("of_bytes", [{:list, [line: line], values}], line)}

      {:error, _} = e ->
        e
    end
  end

  # A `/type` segment parses as a division `value / type_name` (`<<x/float>>`,
  # `<<rest/binary>>`); the sole surface marker for a non-default segment.
  defp typed_segment?({:binary_op, meta, [_v, {:variable, _vm, _type}]}),
    do: Keyword.get(meta, :operator) == :/

  defp typed_segment?(_), do: false

  # `"abc"` → the `:list` literal `['a', 'b', 'c']`: one char-literal element per
  # Unicode codepoint (`String.to_charlist` decodes UTF-8), so a string is exactly
  # `List(Char)` and reuses all of `desugar_list`'s Cons/Nil machinery. The empty
  # string yields the empty list (`Nil`).
  defp desugar_string(value, meta) when is_binary(value) do
    loc = Keyword.take(meta, [:line, :col])
    chars = Enum.map(String.to_charlist(value), fn cp -> {:literal, [subtype: :char] ++ loc, cp} end)
    {:list, meta, chars}
  end

  defp fold_list_literal(elems, m) do
    Enum.reduce(Enum.reverse(elems), ctor_call("Nil", m, []), fn e, acc ->
      ctor_call("Cons", m, [desugar_list(e), acc])
    end)
  end

  defp ctor_call(name, m, args),
    do: {:function_call, [name: name] ++ Keyword.take(m, [:line, :col]), args}

  # Rewrite `:list` patterns in each match arm to the ctor-call form before any
  # downstream pattern pass runs (the pattern-position half of desugar_list/1).
  defp desugar_list_patterns(arms) do
    Enum.map(arms, fn
      {:match_arm, meta, body} = arm ->
        case Keyword.get(meta, :pattern) do
          {:list, _, _} = lp ->
            {:match_arm, Keyword.put(meta, :pattern, desugar_list(lp)), body}

          _ ->
            arm
        end

      other ->
        other
    end)
  end

  # Typed constructor payloads (`Some(value: Int)`) are a surface ascription on
  # an ordinary constructor binder. Remove the annotation before the existing
  # pattern matrix, but retain its type AST in arm metadata for the validation
  # pass in `elaborate_match/6`. Keeping this generic avoids teaching any macro
  # about the elaborator's constructor representation.
  defp desugar_typed_constructor_args(arms) do
    Enum.map(arms, fn
      {:match_arm, meta, body} = arm ->
        case Keyword.get(meta, :pattern) do
          {:function_call, pattern_meta, args} ->
            {args, annotations} = clean_typed_constructor_args(args, 0, [], [])

            meta =
              if annotations == [],
                do: meta,
                else: Keyword.put(meta, :typed_pattern_types, Enum.reverse(annotations))

            {:match_arm, Keyword.put(meta, :pattern, {:function_call, pattern_meta, args}), body}

          _ ->
            arm
        end

      other ->
        other
    end)
  end

  defp clean_typed_constructor_args([], _index, args, annotations), do: {Enum.reverse(args), annotations}

  defp clean_typed_constructor_args([{:typed_pattern, pattern_meta, [name, type_ast]} | rest], index, args, annotations)
       when is_binary(name) do
    clean_typed_constructor_args(
      rest,
      index + 1,
      [{:variable, pattern_meta, name} | args],
      [{index, type_ast} | annotations]
    )
  end

  defp clean_typed_constructor_args([arg | rest], index, args, annotations) do
    clean_typed_constructor_args(rest, index + 1, [arg | args], annotations)
  end

  defp validate_typed_pattern_annotations(arms, {:vdata, dname, combined_vals}, names, ctx, env) do
    pc = Inductive.param_count(env, dname)
    {param_vals, _idx_vals} = Enum.split(combined_vals, pc)

    Enum.reduce_while(arms, :ok, fn
      {:match_arm, meta, _body}, :ok ->
        case Keyword.get(meta, :typed_pattern_types, []) do
          [] ->
            {:cont, :ok}

          annotations ->
            pattern = Keyword.fetch!(meta, :pattern)

            with {:ok, {cname, _pattern_vars}} <- constructor_pattern(pattern),
                 %{args: telescope, quantities: quantities} <- Inductive.get_ctor(env, cname),
                 branch_ctx <- extend_context(ctx, telescope, param_vals),
                 :ok <- validate_constructor_payload_types(annotations, telescope, quantities, branch_ctx, names, env) do
              {:cont, :ok}
            else
              {:error, _} = error -> {:halt, error}
              nil -> {:halt, {:error, {:unknown_constructor, cname_from_pattern(pattern)}}}
            end
        end

      _arm, :ok ->
        {:cont, :ok}
    end)
    |> case do
      :ok -> :ok
      {:error, _} = error -> error
    end
  end

  defp validate_typed_pattern_annotations(_arms, _scrut_type, _names, _ctx, _env), do: :ok

  defp validate_constructor_payload_types(annotations, telescope, quantities, branch_ctx, names, env) do
    present_positions =
      quantities
      |> Enum.with_index()
      |> Enum.filter(fn {quantity, _index} -> Grade.present?(quantity) end)
      |> Enum.map(&elem(&1, 1))

    Enum.reduce_while(annotations, :ok, fn {position, type_ast}, :ok ->
      case Enum.at(present_positions, position) do
        nil ->
          {:halt, {:error, {:typed_pattern_arity, position}}}

        telescope_position ->
          branch_index = length(telescope) - 1 - telescope_position
          actual = Context.lookup(branch_ctx, branch_index)

          with {:ok, annotated} <- elaborate_type(type_ast, names, env),
               actual when not is_nil(actual) <- actual,
               actual_term <- Quote.reify(actual, Context.length(branch_ctx)),
               expected_term <- Subst.shift(annotated, length(telescope), 0),
               true <-
                 Conv.conv?(
                   expected_term,
                   actual_term,
                   Context.env(branch_ctx),
                   Context.length(branch_ctx),
                   Context.signature(branch_ctx)
                 ) do
            {:cont, :ok}
          else
            false -> {:halt, {:error, {:typed_pattern_type_mismatch, type_ast}}}
            nil -> {:halt, {:error, {:typed_pattern_type_mismatch, type_ast}}}
            {:error, reason} -> {:halt, {:error, {:typed_pattern_type_error, reason}}}
          end
      end
    end)
  end

  defp cname_from_pattern({:function_call, meta, _args}), do: Keyword.get(meta, :name)
  defp cname_from_pattern(_pattern), do: nil

  defp constructor_pattern({:function_call, meta, args}) do
    cname = meta |> Keyword.fetch!(:name) |> String.to_atom()

    # A named-implicit dot pattern `{k = …}` annotates an erased index by name; it
    # binds nothing at runtime and is check-and-discarded in the branch path, so
    # it is partitioned out here. What REMAINS are the positional (present-arg)
    # sub-patterns, which — as today — must each be a bare variable. A NESTED
    # constructor/literal sub-pattern (`S(S(m))`, `C(Z(),y)`) still needs decision-
    # tree lowering (parity #3), so report a clean error on any non-variable
    # positional arg.
    positional = Enum.reject(args, &named_implicit_arg?/1)

    if Enum.all?(positional, &match?({:variable, _m, _v}, &1)) do
      vars = Enum.map(positional, fn {:variable, _meta, v} -> v end)

      # Patterns must be linear: a repeated binder (`C(x, x)`) is not a valid
      # pattern — the body's reference is ambiguous and equality between two
      # positions must be witnessed by a proof, not a repeated name (Idris/Agda).
      # The bare wildcard `_` binds nothing, so it may repeat.
      non_wild = Enum.reject(vars, &(&1 == "_"))

      case non_wild -- Enum.uniq(non_wild) do
        [] -> {:ok, {cname, vars}}
        [dup | _] -> {:error, {:nonlinear_pattern, String.to_atom(dup)}}
      end
    else
      {:error, {:unsupported_pattern, :nested_constructor_arg}}
    end
  end

  defp constructor_pattern(other), do: {:error, {:unsupported_pattern, pattern_shape(other)}}

  defp named_implicit_arg?({:named_implicit_pat, _m, _children}), do: true
  defp named_implicit_arg?(_), do: false

  # A pattern's value-reconstruction (spliced into a branch body by
  # `desugar_as_patterns` and `refine_scrutinee_in_body`) must carry no
  # `{:named_implicit_pat,…}` annotation nodes — they are pattern-only
  # syntax, invalid in expression position (spec 2026-07-08 §2.2). The
  # positional-only form is what Idris/Lean substitute for the scrutinee.
  # Recursive: nested constructor sub-patterns are cleaned too.
  defp strip_named_implicits({:function_call, m, args}) do
    positional =
      args
      |> Enum.reject(&named_implicit_arg?/1)
      |> Enum.map(&strip_named_implicits/1)

    {:function_call, m, positional}
  end

  defp strip_named_implicits(other), do: other

  # The named-implicit annotations of a constructor pattern, as `{name, inner}`
  # pairs (empty for a pattern without any). Used by `elaborate_matched_branch`
  # to run the forced-index convertibility check.
  defp constructor_named_implicits({:function_call, _meta, args}),
    do: for({:named_implicit_pat, m, [inner]} <- args, do: {Keyword.get(m, :name), inner})

  defp constructor_named_implicits(_), do: []

  # Split a pattern's named implicits per spec 2026-07-08 §2.3: an UNFORCED
  # position written as a bare variable BINDS (Idris quantity-0 pattern
  # variable — probe evidence in the spec); everything else stays on the
  # check path (forced positions check convertibility; unforced dot/non-var
  # forms keep the `{:named_implicit_unforced,…}` reject).
  defp split_named_implicits(pattern, subst, arity, telescope) do
    pattern
    |> constructor_named_implicits()
    |> Enum.split_with(fn {name, inner} ->
      match?({:variable, _, _}, inner) and
        named_implicit_forced_value(name, subst, arity, telescope) == :error and
        Enum.find_index(telescope, fn {n, _t} -> n == String.to_atom(name) end) != nil
    end)
  end

  defp pattern_shape(p) when is_tuple(p) and tuple_size(p) > 0, do: elem(p, 0)
  defp pattern_shape(_), do: :unknown

  @doc """
  LHS re-match (ports Idris `TTImp.WithClause.getMatch`). Match the parent
  function's original parameter patterns positionally against a with-clause's
  RESTATED patterns, producing a substitution `%{parent_var_name => refined
  surface pattern}`. This is the map that refines the branch goal and sibling
  types by the index a with-clause restates (`n` ↦ `S(m)`).

  Handled (the faithful first slice):
    * variable ↦ variable    — an alias (`n` restated as `m`)
    * variable ↦ constructor — the refinement (`n` restated as `S(m)`)
    * constructor ↦ constructor — structural recursion into matching args

  A restated pattern that is a non-constructor EXPRESSION (e.g. `k + k`) is
  rejected with `{:with_rematch_non_constructor_pattern, …}` — that is the
  deferred forced/dot-pattern case (ledger #5), not a crash.
  """
  @spec match_parent_lhs([term()], [term()]) :: {:ok, %{String.t() => term()}} | {:error, term()}
  def match_parent_lhs(originals, restated) when length(originals) == length(restated) do
    originals
    |> Enum.zip(restated)
    |> Enum.reduce_while({:ok, %{}}, fn {orig, pat}, {:ok, acc} ->
      case match_one_lhs(orig, pat, acc) do
        {:ok, acc2} -> {:cont, {:ok, acc2}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  def match_parent_lhs(originals, restated),
    do: {:error, {:with_rematch_arity_mismatch, length(originals), length(restated)}}

  # A parent variable (or `{:param,…}`) binds to its restated pattern, provided
  # the pattern is a variable or a (possibly nested) constructor application.
  defp match_one_lhs({:variable, _, name}, restated, acc), do: bind_var_lhs(name, restated, acc)
  defp match_one_lhs({:param, _, name}, restated, acc), do: bind_var_lhs(name, restated, acc)

  # Parent constructor vs restated constructor: names + arity must agree, then
  # recurse into the arguments (the getMatch IApp case).
  defp match_one_lhs({:function_call, m1, a1}, {:function_call, m2, a2}, acc) do
    n1 = Keyword.get(m1, :name)
    n2 = Keyword.get(m2, :name)

    cond do
      n1 != n2 ->
        {:error, {:with_rematch_ctor_mismatch, n1, n2}}

      length(a1) != length(a2) ->
        {:error, {:with_rematch_arity_mismatch, length(a1), length(a2)}}

      true ->
        a1
        |> Enum.zip(a2)
        |> Enum.reduce_while({:ok, acc}, fn {o, p}, {:ok, a} ->
          case match_one_lhs(o, p, a) do
            {:ok, a2} -> {:cont, {:ok, a2}}
            {:error, _} = err -> {:halt, err}
          end
        end)
    end
  end

  defp match_one_lhs(orig, _restated, _acc),
    do: {:error, {:with_rematch_unsupported_parent_pattern, pattern_shape(orig)}}

  defp bind_var_lhs(name, restated, acc) do
    if valid_restated_pattern?(restated) do
      merge_lhs_match(acc, name, restated)
    else
      {:error, {:with_rematch_non_constructor_pattern, pattern_shape(restated)}}
    end
  end

  # mergeMatches: a name may be restated more than once only if consistently.
  defp merge_lhs_match(acc, name, pat) do
    case Map.fetch(acc, name) do
      :error ->
        {:ok, Map.put(acc, name, pat)}

      {:ok, existing} ->
        if strip_pattern_meta(existing) == strip_pattern_meta(pat),
          do: {:ok, acc},
          else: {:error, {:with_rematch_inconsistent_binding, name}}
    end
  end

  # A restated pattern must be a variable or a constructor application whose
  # every argument is itself such a pattern. Anything else (binary ops, literal
  # arithmetic, …) is a non-constructor expression — the deferred forced case.
  defp valid_restated_pattern?({:variable, _, _}), do: true

  defp valid_restated_pattern?({:function_call, meta, args}) do
    constructor_name?(Keyword.get(meta, :name)) and Enum.all?(args, &valid_restated_pattern?/1)
  end

  defp valid_restated_pattern?(_), do: false

  # Cure constructors are capitalised; ordinary identifiers/operators are not.
  defp constructor_name?(name) when is_binary(name) and name != "",
    do: String.first(name) =~ ~r/[A-Z]/

  defp constructor_name?(_), do: false

  # Structural equality of surface patterns, ignoring meta.
  defp strip_pattern_meta({:variable, _, n}), do: {:variable, n}

  defp strip_pattern_meta({:function_call, meta, args}),
    do: {:function_call, Keyword.get(meta, :name), Enum.map(args, &strip_pattern_meta/1)}

  defp strip_pattern_meta(other), do: other

  # Names for the branch's telescope binders, most-recently-bound first. Surface
  # pattern variables name present (ω) positions. Erased constructor existentials
  # get distinct internal names: they are still quantity-0 (so relevance rejects
  # computational use), but branch substitutions can address each slot without
  # collapsing them all to the old, ambiguous `_erased` name. A source-level name
  # requested with `{index = binder}` replaces this internal name below.
  defp branch_scope(telescope, quantities, pattern_vars) do
    {names_in_order, _rest} =
      Enum.zip(telescope, quantities)
      |> Enum.with_index()
      |> Enum.map_reduce(pattern_vars, fn
        {{{_tele_name, _type}, :unrestricted}, _i}, [v | rest] -> {v, rest}
        {{{tele_name, _type}, :erased}, i}, vars -> {"$erased_#{tele_name}_#{i}", vars}
      end)

    Enum.reverse(names_in_order)
  end

  # Shared branch-goal refinement (Task 3.4) — ONE equation-compiler refinement
  # behind two front-ends (plain `match` `elaborate_matched_branch` and
  # `with`-rematch `elaborate_rematch_branch`). Composes (1a) index inversion (the
  # `branch_unify` verdict `subst`) with (1b) scrutinee-VALUE refinement: a
  # variable scrutinee is keyed into the subst at `i + arity`; a computed one has
  # its occurrences replaced by the branch constructor as a whole term (matching
  # `build_motive`'s kabstract — the kernel checks this branch at `motive @ ctor`).
  defp refine_branch_goal(result_type_term, scrut_term, cname, arity, subst, branch_ctx) do
    ctor_term = branch_constructor_term(cname, arity)

    subst_with_scrut =
      case scrut_term do
        {:var, i} -> Map.put(subst, i + arity, ctor_term)
        _other -> subst
      end

    shifted_goal = Subst.shift(result_type_term, arity, 0)

    shifted_goal =
      case scrut_term do
        {:var, _} -> shifted_goal
        computed -> replace_term(shifted_goal, Subst.shift(computed, arity, 0), ctor_term)
      end

    shifted_goal
    |> replace_branch_vars(subst_with_scrut)
    |> then(&Kernel.normalize(branch_ctx, &1))
  end

  defp branch_constructor_term(cname, 0), do: {:ctor, cname, []}

  defp branch_constructor_term(cname, arity) do
    args = for i <- 0..(arity - 1), do: {:var, arity - 1 - i}
    {:ctor, cname, args}
  end

  # Extend the branch context with a constructor's argument telescope. The
  # telescope's type terms are written in the constructor's own isolated frame
  # `ctx_full = params ++ args`, so — mirroring the kernel's `extend_with_
  # telescope` — evaluate each against a local value environment seeded with the
  # scrutinee's actual parameter values (`param_vals`) beneath fresh neutrals for
  # the args already bound. A parameter reference in an arg type (e.g. `rest : a`
  # in `prepend`) then resolves to the scrutinee's parameter, not a stray outer
  # binder. Values carry absolute de Bruijn *levels*, so param_vals stay valid as
  # the context grows. For a parameter-free family this is the previous behavior.
  defp extend_context(ctx, telescope, param_vals) do
    {ctx_final, _local_vals} =
      Enum.reduce(telescope, {ctx, Enum.reverse(param_vals)}, fn {_name, type_term}, {c, local_vals} ->
        type_value = Eval.eval(type_term, local_vals)
        fresh_val = {:vneutral, {:nvar, Context.length(c)}}
        {Context.extend(c, type_value), [fresh_val | local_vals]}
      end)

    ctx_final
  end

  defp replace_branch_vars({:var, i}, subst), do: replace_branch_var(i, subst, 0)

  defp replace_branch_vars({:pi, _g, d, c}, subst),
    do:
      {:pi, Cure.Core.Grade.unrestricted(), replace_branch_vars(d, subst),
       replace_branch_vars(c, shift_subst(subst, 1))}

  defp replace_branch_vars({:lam, _g, d, b}, subst),
    do:
      {:lam, Cure.Core.Grade.unrestricted(), replace_branch_vars(d, subst),
       replace_branch_vars(b, shift_subst(subst, 1))}

  defp replace_branch_vars({:app, f, a}, subst),
    do: {:app, replace_branch_vars(f, subst), replace_branch_vars(a, subst)}

  defp replace_branch_vars({:data, n, ps, is}, subst),
    do: {:data, n, Enum.map(ps, &replace_branch_vars(&1, subst)), Enum.map(is, &replace_branch_vars(&1, subst))}

  defp replace_branch_vars({:ctor, n, args}, subst),
    do: {:ctor, n, Enum.map(args, &replace_branch_vars(&1, subst))}

  defp replace_branch_vars({:case, scr, m, brs}, subst),
    do:
      {:case, replace_branch_vars(scr, subst), replace_branch_vars(m, subst),
       Enum.map(brs, fn {c, ar, b} -> {c, ar, replace_branch_vars(b, shift_subst(subst, ar))} end)}

  defp replace_branch_vars(other, _subst), do: other

  defp shift_subst(subst, amount) do
    Map.new(subst, fn {k, v} -> {k + amount, Subst.shift(v, amount, 0)} end)
  end

  defp replace_branch_var(i, subst, depth) when depth < 100_000 do
    case Map.get(subst, i) do
      nil -> {:var, i}
      {:var, ^i} -> {:var, i}
      {:var, j} -> replace_branch_var(j, subst, depth + 1)
      term -> replace_branch_vars(term, subst)
    end
  end

  defp replace_branch_var(i, _subst, _depth), do: {:var, i}

  @doc """
  Elaborate a constructor application `C(a₁, …, aₙ)`, inferring the erased index
  arguments (quantity 0) from the runtime-relevant (quantity ω) arguments'
  types (design spec §5.2). `present_args` is `[{core_term, type_value}]` — the
  already-elaborated ω arguments with their inferred types.

  Fresh metavariables stand in for the erased arguments; each ω argument's
  expected telescope type is specialised with the choices so far (`Subst`) and
  unified against the provided argument's type (`Unify`). On success every
  metavariable is solved, and the fully-applied `{:ctor, …}` term plus its result
  type (the family at the computed indices) are returned.

  `present_args` is `[{core_term, type_term}]` — each ω argument with its type
  already reified as a term in the caller's de Bruijn frame.
  """
  @spec elaborate_ctor_app(Env.t(), atom(), [{term(), term()}], Context.t() | nil) ::
          {:ok, term(), Cure.Core.Value.t()} | {:error, term()}
  def elaborate_ctor_app(env, cname, present_args, ctx \\ nil, expected_core \\ nil) do
    ctor = Inductive.get_ctor(env, cname)
    family = Inductive.ctor_family(env, cname)

    if is_nil(ctor) or is_nil(family) do
      {:error, {:unknown_constructor, cname}}
    else
      # The family's parameters are bound outside the constructor's arg telescope
      # (the kernel checks it as `ctx_full = params ++ args`). A constructor arg
      # type — e.g. `prepend`'s `x : a` — can reference a parameter, so model the
      # parameters as leading erased slots: their metavariables are seeded into
      # the substitution frame and solved by unifying the present arguments. For
      # a parameter-free family this prefix is empty (unchanged behavior).
      param_tele = Inductive.param_telescope(env, family) || []
      param_slots = Enum.map(param_tele, fn entry -> {entry, :erased} end)
      telescope = param_slots ++ Enum.zip(ctor.args, ctor.quantities)
      pc = length(param_tele)
      init = {:ok, MetaCtx.new(), [], present_args}

      telescope
      |> Enum.reduce_while(init, &solve_arg(&1, &2, env))
      |> pin_ctor_result(expected_core, family, ctor, pc, env)
      |> finish_ctor_app(cname, family, ctor, pc, ctx)
    end
  end

  # Checking-mode index inference: unify the constructor's RESULT type (built with
  # the erased-index metavariables still open) against the expected type, pinning
  # indices the present arguments could not. A nullary constructor whose indices
  # are all erased — `prim : SF(av, bv, DCau)` reconstructed in a dependent-match
  # branch expecting `SF(as, bs, DCau)` — has NO present argument to solve `av`/`bv`
  # from; the expected type is their only source. In inference mode (`expected_core
  # == nil`) this is a no-op, so ordinary constructor applications are unchanged.
  defp pin_ctor_result({:ok, mctx, chosen, []} = ok, expected_core, family, ctor, pc, env)
       when expected_core != nil do
    {param_vals, args} = Enum.split(chosen, pc)
    seed = param_vals ++ args
    params = Enum.map(Map.get(ctor, :result_params, []), &Subst.instantiate(&1, seed))
    indices = Enum.map(ctor.result_indices, &Subst.instantiate(&1, seed))
    result_term = {:data, family, params, indices}

    case Unify.unify(result_term, expected_core, mctx, env) do
      {:ok, mctx2} -> {:ok, mctx2, chosen, []}
      # Leave the mismatch to `finish_ctor_app` (unsolved metas) or the kernel's
      # own re-check — never silently accept.
      {:error, _} -> ok
    end
  end

  defp pin_ctor_result(acc, _expected_core, _family, _ctor, _pc, _env), do: acc

  # One telescope slot: erased → fresh meta; present → unify expected vs actual.
  # `env` is threaded as the conversion signature so a present argument whose type
  # carries a *computed* index (`seq`'s `dmeet(d1, d2)`) unifies up-to-δ against
  # the expected `DDec` — closing the composed-computed-index reach (Idris parity)
  # without any kernel change (`Unify` uses the trusted `Conv`; the kernel still
  # re-checks the assembled ctor). See `Unify.unify/4`.
  defp solve_arg({{_name, type_term}, :erased}, {:ok, mctx, chosen, present}, _env) do
    {mctx, id} = MetaCtx.fresh(mctx, Subst.instantiate(type_term, chosen))
    {:cont, {:ok, mctx, chosen ++ [{:meta, id}], present}}
  end

  defp solve_arg({{_name, _type_term}, grade}, {:ok, _mctx, _chosen, []}, _env)
       when grade in [:unrestricted, :linear, :affine],
       do: {:halt, {:error, :too_few_arguments}}

  defp solve_arg(
         {{_name, type_term}, grade},
         {:ok, mctx, chosen, [{arg, arg_type_term} | rest]},
         env
       )
       when grade in [:unrestricted, :linear, :affine] do
    expected = Subst.instantiate(type_term, chosen)

    case Unify.unify(expected, arg_type_term, mctx, env) do
      {:ok, mctx} ->
        {:cont, {:ok, mctx, chosen ++ [arg], rest}}

      {:error, reason} ->
        # The domain may be a generated anonymous-union family that goal-directed
        # solving has already pinned (see `elaborate_global_app`). Unification has no
        # coercion, so a MEMBER argument fails against it — inject the member's
        # constructor and retry. This is the same check-position coercion applied
        # everywhere else, at the one place where the argument's domain is only known
        # after the goal has been solved.
        case inject_arg_into_union(arg, arg_type_term, Unify.zonk(expected, mctx), env) do
          nil ->
            {:halt, {:error, {:index_mismatch, reason}}}

          injected ->
            case Unify.unify(expected, Unify.zonk(expected, mctx), mctx, env) do
              {:ok, mctx} -> {:cont, {:ok, mctx, chosen ++ [injected], rest}}
              {:error, _} -> {:halt, {:error, {:index_mismatch, reason}}}
            end
        end
    end
  end

  # Inject a TERM whose inferred type is a member of the (already-solved) union domain.
  # Term-level, not value-level: at this point everything is a Core term, so no Context
  # is needed. Returns nil when the domain is not a union or the argument is not one of
  # its members — the caller then reports the ordinary unification failure.
  defp inject_arg_into_union(arg, arg_type_term, {:data, ukey, [], []}, env) do
    if Cure.Elab.Union.union_family?(ukey) do
      cname = Cure.Elab.Union.ctor_key(ukey, %{key: Cure.Elab.Union.member_key(arg_type_term)})
      if Inductive.get_ctor(env, cname), do: {:ctor, cname, [arg]}, else: nil
    end
  end

  defp inject_arg_into_union(_arg, _arg_type_term, _expected, _env), do: nil

  defp finish_ctor_app({:error, _} = err, _cname, _family, _ctor, _pc, _ctx), do: err

  defp finish_ctor_app({:ok, _mctx, _chosen, [_ | _]}, _cname, _family, _ctor, _pc, _ctx),
    do: {:error, :too_many_arguments}

  defp finish_ctor_app({:ok, mctx, chosen, []}, cname, family, ctor, pc, ctx) do
    all = Enum.map(chosen, &Unify.zonk(&1, mctx))

    if Enum.any?(all, &has_meta?/1) do
      {:error, {:unsolved_metavariables, cname}}
    else
      # `chosen` is [solved parameters] ++ [constructor args]. The Core `:ctor`
      # term carries only the constructor args (parameters are erased and
      # recovered from the value's type); result params/indices reference
      # `ctx_full = params ++ args`, so instantiate them with the full frame.
      {param_vals, args} = Enum.split(all, pc)
      seed = param_vals ++ args
      params = Enum.map(Map.get(ctor, :result_params, []), &Subst.instantiate(&1, seed))
      indices = Enum.map(ctor.result_indices, &Subst.instantiate(&1, seed))

      # The result type's computed indices reference the CALLER's context vars
      # (e.g. `seq`'s result `SF(app(av,cv), …)`). Evaluate under the caller's
      # environment so those free de Bruijn variables get the correct neutral
      # levels — evaluating under `[]` mis-levels them, which is invisible when a
      # ctor is checked directly (the kernel re-infers) but CORRUPTS meta-solving
      # when this inferred type feeds further elaboration (a computed-index ctor
      # applied as another ctor's argument, e.g. `loop(seq(a,b))`). Mirrors
      # `finish_global_app`. With no caller context (isolated unit calls), fall
      # back to `[]` — those terms are closed, so the frame is immaterial.
      caller_env = if ctx, do: Context.env(ctx), else: []
      result_type = Eval.eval({:data, family, params, indices}, caller_env)
      {:ok, {:ctor, cname, args}, result_type}
    end
  end

  # Bidirectional application for a global with implicit (erased) parameters, used
  # only as a fallback when the ordinary inference path fails — a call whose
  # argument cannot be inferred in isolation but *can* be checked once the callee's
  # implicit parameters are solved, e.g. `map(s, Cons(Z(), Nil()))` whose list
  # argument is underdetermined until `a` is fixed from `s : (Nat) -> Nat`.
  #
  # It folds the callee's Π telescope left to right: each erased slot becomes a
  # fresh metavariable; each present slot's domain is instantiated with the
  # arguments chosen so far and zonked — if that domain is now metavariable-free
  # the argument is *checked* against it (so an underdetermined constructor
  # argument reaches the checking-mode constructor path), otherwise the argument is
  # *inferred* and its type unified against the domain to solve the metavariables.
  # `finish_global_app` assembles and the caller's kernel re-check gates the result,
  # so nothing unsound rests on the inference order.
  defp elaborate_implicit_app_bidirectional(env, name, arg_asts, names, ctx, expected \\ nil) do
    %{type: pi_type, quantities: quantities} = Env.get_def(env, name)
    {domains, codomain} = peel_pi(pi_type, length(quantities))

    # Transparent aliases in an expected result must be unfolded before the
    # goal-first implicit solve. Refinement aliases are the load-bearing case:
    # `PositiveNatural` normalizes to `Sigma(Nat, IsPositive)`, which determines
    # the hidden predicate of `refine` before its proof argument is checked.
    # `finish_global_app` already performs this normalization for its final solve;
    # doing the same in the pre-pass prevents argument order from hiding that goal.
    expected_for_goal =
      if expected != nil do
        case Kernel.normalize(ctx, expected) do
          :fuel_exhausted -> expected
          normalized -> normalized
        end
      end

    slots = Enum.zip(domains, quantities)
    init = {:ok, MetaCtx.new(), [], arg_asts, []}

    # GOAL-DIRECTED solving from the concrete return-type goal — ordinary
    # bidirectional propagation (Idris/Agda/Lean): unify the codomain against the
    # expected type FIRST, so a leading implicit determined only by the result is
    # solved before its dependent argument slots are elaborated. This is the path
    # taken when an argument cannot be inferred standalone, in two shapes:
    #
    #   * an anonymous-union value slot (`Std.Map.put(:a, 1, Std.Map.new())` —
    #     `new()`'s implicits have nothing to fix them): without goal-first solving
    #     the domain `?v` stays a meta, the slot is DEFERRED and later resolved by
    #     inferring the argument, locking `?v := Int` and LOSING the union;
    #   * a lambda argument whose domain the goal alone fixes (`mk(fn(x) -> x.1)`
    #     at `Box(Tuple(Int,Int), Int)` — `mk : {s} -> {a} -> (s -> a) -> Box(s,a)`):
    #     without it `?s`/`?a` stay metas, so `fn(x) -> x.1` is checked at `?s -> ?a`
    #     and the projection cannot lower (`:unsupported_expression`). When NO later
    #     argument constrains the implicit (only lambdas, or a single argument), the
    #     cross-argument deferral cannot rescue it, but the goal can.
    #
    # `bidir_solve_codomain_from_goal` swallows unification failure, so a goal that
    # does not inform the codomain leaves the accumulator untouched — the ordinary
    # left-to-right slot solving then runs exactly as before, and the kernel
    # re-checks the assembled term regardless. Restricted to a META-FREE goal so a
    # still-open expected type (nothing to solve against) skips the pre-pass.
    seed_from_goal? =
      union_goal?(expected_for_goal) or
        (not is_nil(expected_for_goal) and not Unify.has_meta?(expected_for_goal))

    {init, slots} =
      if seed_from_goal? do
        # Allocate the REAL leading erased/placeholder metas before solving the
        # codomain. Previously only erased slots were retained; explicit `_`
        # slots were represented by disposable padding metas during goal
        # unification, then allocated afresh in the main pass and stayed
        # unsolved (`box(_) : Box(Z)`). Stop at the first ordinary present
        # argument so its existing bidirectional checking order is unchanged.
        {seeded, rest} = bidir_seed_goal_prefix(slots, init, names, ctx, env)
        seeded = bidir_solve_codomain_from_goal(seeded, codomain, expected_for_goal, env, rest)

        {seeded, rest}
      else
        {init, slots}
      end

    slots
    |> Enum.reduce_while(init, &bidir_app_slot(&1, &2, names, ctx, env))
    |> resolve_deferred_slots(names, ctx, env)
    |> finish_global_app(name, codomain, ctx, env, expected)
  end

  defp bidir_seed_goal_prefix(
         [slot = {_dom, :erased} | rest],
         acc,
         names,
         ctx,
         env
       ) do
    {:cont, acc} = bidir_app_slot(slot, acc, names, ctx, env)
    bidir_seed_goal_prefix(rest, acc, names, ctx, env)
  end

  defp bidir_seed_goal_prefix(
         [slot | rest],
         {:ok, _mctx, _chosen, [{:variable, _meta, "_"} | _], _deferred} = acc,
         names,
         ctx,
         env
       ) do
    {:cont, acc} = bidir_app_slot(slot, acc, names, ctx, env)
    bidir_seed_goal_prefix(rest, acc, names, ctx, env)
  end

  defp bidir_seed_goal_prefix(slots, acc, _names, _ctx, _env), do: {acc, slots}

  # `solve_codomain_from_goal/5` for the bidirectional accumulator's 5-tuple. Same
  # contract: pad `chosen` to the full binder stack (Subst.instantiate indexes against
  # all of it), unify the codomain with the goal, and swallow failure so the ordinary
  # path still produces the honest error.
  defp bidir_solve_codomain_from_goal(
         {:ok, mctx, chosen, args, deferred},
         codomain,
         expected,
         env,
         remaining
       ) do
    {mctx_padded, padded} =
      Enum.reduce(remaining, {mctx, chosen}, fn {dom, _q}, {m, acc} ->
        {m, id} = MetaCtx.fresh(m, Subst.instantiate(dom, acc))
        {m, acc ++ [{:meta, id}]}
      end)

    case Unify.unify(Subst.instantiate(codomain, padded), expected, mctx_padded, env) do
      {:ok, mctx2} -> {:ok, mctx2, chosen, args, deferred}
      {:error, _} -> {:ok, mctx, chosen, args, deferred}
    end
  end

  defp bidir_solve_codomain_from_goal({:error, _} = err, _cod, _exp, _env, _rem), do: err

  @doc """
  Type-position entry for implicit insertion (spec 2026-07-08 §7): elaborate an
  application of a global that carries implicit (erased) parameters, from its
  SURFACE argument ASTs, in the caller's typing context. Used by the
  return-type lowering in `Cure.Elab.Declarations` — term position reaches the
  same machinery via `elaborate_named_call`. The kernel re-checks the assembled
  signature, so nothing unsound rests on this path.
  """
  def elaborate_implicit_global_app(env, name, arg_asts, names, ctx) do
    elaborate_implicit_app_bidirectional(env, name, arg_asts, names, ctx)
  end

  defp bidir_app_slot({dom, :erased}, {:ok, mctx, chosen, args, deferred}, _names, _ctx, _env) do
    {mctx, id} = MetaCtx.fresh(mctx, Subst.instantiate(dom, chosen))
    {:cont, {:ok, mctx, chosen ++ [{:meta, id}], args, deferred}}
  end

  defp bidir_app_slot({_dom, grade}, {:ok, _mctx, _chosen, [], _deferred}, _names, _ctx, _env)
       when grade in [:unrestricted, :linear, :affine],
       do: {:halt, {:error, :too_few_arguments}}

  # An explicit `_` in call-argument position is a goal-directed placeholder,
  # not a reference to a global named `_`. Seed a term metavariable at this
  # slot and continue: a later dependent argument may determine its VALUE.
  # `finish_global_app` rejects it if it remains
  # unsolved, and the assembled application is kernel-checked by the caller, so
  # no placeholder can escape into Core.
  defp bidir_app_slot(
         {dom, grade},
         {:ok, mctx, chosen, [{:variable, _meta, "_"} | rest], deferred},
         _names,
         _ctx,
         _env
       )
       when grade in [:unrestricted, :linear, :affine] do
    dom_inst = Enum.map(chosen, &Unify.zonk(&1, mctx)) |> then(&Subst.instantiate(dom, &1))
    {mctx, id} = MetaCtx.fresh(mctx, dom_inst)
    {:cont, {:ok, mctx, chosen ++ [{:meta, id}], rest, deferred}}
  end

  # A supplied explicit argument — grade governs later USAGE counting
  # (`relevance.ex`), not slot mechanics: :unrestricted / :linear / :affine all
  # consume one surface argument here, mirroring `solve_arg/3`'s telescope slot.
  defp bidir_app_slot({dom, grade}, {:ok, mctx, chosen, [arg | rest], deferred}, names, ctx, env)
       when grade in [:unrestricted, :linear, :affine] do
    # ZONK-then-instantiate, not instantiate-then-zonk: `Subst.instantiate` shifts a
    # substituted term across binders, `Unify.zonk` does not. A domain that is a Π
    # (a function-typed argument, `(a) -> a`) whose earlier sibling already solved the
    # metavariable to a term with FREE de Bruijn variables would otherwise reach the
    # checking mode below with the codomain occurrence unshifted (`{:var,2}` where
    # `{:var,3}` is due). Resolving the metavariables into the substitution first lets
    # `instantiate` place them at the right depth. See the twin fix in
    # `resolve_deferred_slots`; a closed solution shifts to a no-op, so scalar/data
    # domains are unaffected.
    dom_inst = Enum.map(chosen, &Unify.zonk(&1, mctx)) |> then(&Subst.instantiate(dom, &1))

    if has_meta?(dom_inst) do
      # Domain still unsolved — infer the argument and unify to solve metavariables.
      case elaborate_expr_typed(arg, names, ctx, env) do
        {:ok, term, ty} ->
          # Recover the (params, indices) split that the sig-less `Quote.reify`
          # collapses (elaborator.ex:1268 `resplit_data`), so an argument type that
          # carries a NESTED indexed family — e.g. a Sigma projection's `p` whose
          # type is `Sigma(x: Dec, SF(as, bs, x))` — does not reach the kernel with
          # SF's indices smuggled into its param slot (a false `:arg_arity`).
          ty_term = resplit_data(Quote.reify(ty, Context.length(ctx)), env)

          case Unify.unify(dom_inst, ty_term, mctx, env) do
            {:ok, mctx} -> {:cont, {:ok, mctx, chosen ++ [term], rest, deferred}}
            {:error, reason} -> {:halt, {:error, reason}}
          end

        {:error, _} ->
          # A lambda argument whose Π domain still bears a metavariable in its
          # CODOMAIN (`(n:N) -> ?F(n)`) cannot infer standalone; try solving the
          # codomain metavariable under the binder first (higher-order/Miller,
          # ledger #10). Only if that does not apply do we defer.
          case try_lambda_meta_pi(arg, dom_inst, mctx, names, ctx, env) do
            {:ok, mctx, lam_term} ->
              {:cont, {:ok, mctx, chosen ++ [lam_term], rest, deferred}}

            :fallthrough ->
              # An underdetermined argument at a still-unsolved domain — e.g. `fz()` at
              # `Fin(?n)`, whose index only a *later* argument (the vector) determines.
              # It cannot infer standalone, so defer it: a placeholder metavariable holds
              # its position in `chosen` (keeping later domains' de Bruijn frames aligned),
              # and `resolve_deferred_slots` checks it against the now-solved domain and
              # back-patches the placeholder once the later arguments have run.
              {mctx, ph} = MetaCtx.fresh(mctx)
              {:cont, {:ok, mctx, chosen ++ [{:meta, ph}], rest, deferred ++ [{ph, arg, dom, length(chosen)}]}}
          end
      end
    else
      # Domain fully known — check the argument against it (reaches checking mode).
      case elaborate_expr_checked(arg, dom_inst, names, ctx, env) do
        {:ok, term} -> {:cont, {:ok, mctx, chosen ++ [term], rest, deferred}}
        {:error, _} = err -> {:halt, err}
      end
    end
  end

  # A lambda argument at a Π domain whose CODOMAIN still bears a metavariable
  # (`(n:N) -> ?F(n)`) cannot be inferred standalone, and the general checking
  # judgement (`elaborate_expr_checked`) does not thread `mctx`, so it would
  # reject the unsolved codomain. Here `mctx` IS in scope, so we solve it: bind
  # the parameter, INFER the body, and unify the reconstructed Π against the
  # expected one — the codomain metavariable is then solved *under the binder*
  # (the Miller pattern `?F(n) := λn. body_ty`, ledger #10). Single-parameter
  # lambda over a literal Π with a meta-free domain; any other shape falls through
  # to the deferral path. Additive/fallback-only: reached only after inference has
  # already failed, and the assembled call is kernel-re-checked by
  # `finish_global_app`, so nothing unsound rests on the solve.
  defp try_lambda_meta_pi({:lambda, meta, [body_expr]}, {:pi, _g, dom_term, cod_term}, mctx, names, ctx, env) do
    case Keyword.fetch!(meta, :params) do
      [{:param, _pm, pname}] ->
        if has_meta?(dom_term) do
          :fallthrough
        else
          dom_value = Eval.eval(dom_term, Context.env(ctx))
          ctx1 = Context.extend(ctx, dom_value)

          case elaborate_expr_typed(body_expr, [pname | names], ctx1, env) do
            {:ok, body_term, body_ty} ->
              # Pass the signature so an indexed-family body type like
              # `Equivalent(Nat,n,n)` is read back as params+indices instead of the
              # flat `{:data, :Equivalent, all, []}` shape. This term may become the
              # solution for a codomain metavariable (`?P := λn. Equivalent(Nat,n,n)`),
              # and the later `P(Zero)` kernel check expects the split form.
              body_ty_term = Quote.reify(body_ty, Context.length(ctx1), env)

              case Unify.unify(
                     {:pi, Cure.Core.Grade.unrestricted(), dom_term, cod_term},
                     {:pi, Cure.Core.Grade.unrestricted(), dom_term, body_ty_term},
                     mctx,
                     env
                   ) do
                {:ok, mctx} ->
                  {:ok, mctx, {:lam, Cure.Core.Grade.unrestricted(), dom_term, body_term}}

                {:error, _} ->
                  :fallthrough
              end

            {:error, _} ->
              :fallthrough
          end
        end

      _ ->
        :fallthrough
    end
  end

  defp try_lambda_meta_pi(_arg, _dom_inst, _mctx, _names, _ctx, _env), do: :fallthrough

  # Second pass over the arguments deferred by `bidir_app_slot` (each an
  # underdetermined argument whose domain metavariables a later argument solves).
  # By now those metavariables are solved, so each deferred domain instantiates to a
  # concrete type; check the argument against it and solve the placeholder to the
  # resulting term. A deferred domain still bearing a metavariable means no later
  # argument determined it — a genuinely ambiguous call, reported as unsolved.
  defp resolve_deferred_slots({:error, _} = err, _names, _ctx, _env), do: err

  defp resolve_deferred_slots({:ok, mctx, chosen, args, []}, _names, _ctx, _env),
    do: {:ok, mctx, chosen, args}

  defp resolve_deferred_slots({:ok, mctx, chosen, args, deferred}, names, ctx, env) do
    Enum.reduce_while(deferred, {:ok, mctx}, fn {ph, arg, dom, k}, {:ok, mctx} ->
      # ZONK the chosen prefix FIRST, THEN instantiate — not instantiate-then-zonk.
      # `Subst.instantiate` is binder-aware (it shifts a substituted term when it
      # crosses a binder), but `Unify.zonk` is NOT: it replaces a solved `{:meta,id}`
      # with its solution verbatim. When a deferred domain is a Π (`(a) -> a`, a lambda
      # argument's type) and the metavariable a later sibling solved to a term with
      # FREE de Bruijn variables (a rigid parameter, `?a := {:var,2}`), the occurrence
      # in the codomain sits UNDER the domain binder and must shift to `{:var,3}`.
      # Instantiate-then-zonk left it at `{:var,2}` (`conversion_failure {:var,3}
      # {:var,2}`); resolving the metavariables into the substitution and letting
      # `instantiate` place them restores the shift. A closed solution (`Nat`, `Z` —
      # every constructor-domain deferral) shifts to a no-op, so those are unaffected.
      dom_inst =
        Enum.take(chosen, k) |> Enum.map(&Unify.zonk(&1, mctx)) |> then(&Subst.instantiate(dom, &1))

      # If a later sibling argument did not fully determine this deferred domain,
      # the deferred argument may still determine it FROM ITS OWN constructor
      # result type — `empty : Vector(a', Z)` unified against the domain
      # `Vector(Nat, ?n)` solves `?n := Z` (and `a' := Nat`). Attempt that solve in
      # the CALLER's `mctx` so the freshly-solved domain metavariable propagates to
      # the rest of the call (e.g. `prepend`'s result index). Only a genuinely
      # ambiguous domain — one no argument, including the deferred one, determines —
      # survives with a metavariable and is reported as unsolved. The assembled call
      # is kernel-re-checked by `finish_global_app`, so this inference-order change
      # rests on nothing unsound.
      {mctx, dom_inst} =
        if has_meta?(dom_inst) do
          mctx = solve_deferred_domain(arg, dom_inst, mctx, names, ctx, env)
          {mctx, Unify.zonk(dom_inst, mctx)}
        else
          {mctx, dom_inst}
        end

      if has_meta?(dom_inst) do
        # A deferred LAMBDA whose Π domain a later sibling has now solved, but whose
        # CODOMAIN no argument determines (`(Int) -> ?b`): solve the codomain UNDER
        # the binder by inferring the body. This is the same Miller solve
        # `bidir_app_slot` attempts eagerly — there it fell through because the
        # domain was still `?a` at the time (`try_lambda_meta_pi` requires a meta-free
        # domain), and nothing ever re-offered it. Retrying it HERE is the second half
        # of the postponement: an argument is deferred precisely so a later sibling can
        # solve what it needs, and a lambda needs its DOMAIN, not only its family
        # indices (which is all `solve_deferred_domain` recovers). Without this,
        # `app2(fn(x) -> x + 10, xs)` rejects while `app2(xs, fn(x) -> x + 10)`
        # elaborates — argument ORDER decided typability.
        case try_lambda_meta_pi(arg, dom_inst, mctx, names, ctx, env) do
          {:ok, mctx, lam_term} ->
            {:cont, {:ok, MetaCtx.put_solution(mctx, ph, lam_term)}}

          :fallthrough ->
            {:halt, {:error, {:unsolved_metavariables, :deferred_argument}}}
        end
      else
        case elaborate_expr_checked(arg, dom_inst, names, ctx, env) do
          {:ok, term} -> {:cont, {:ok, MetaCtx.put_solution(mctx, ph, term)}}
          {:error, _} = err -> {:halt, err}
        end
      end
    end)
    |> case do
      {:ok, mctx} -> {:ok, mctx, chosen, args}
      {:error, _} = err -> err
    end
  end

  # Solve a deferred argument's remaining domain metavariables from the argument's
  # OWN constructor, threading `mctx`. When `arg` is a constructor application whose
  # family matches `dom_inst`'s, build the constructor's result-type template over
  # fresh metavariables (mirroring `finish_ctor_app`'s `params ++ args` seed) and
  # unify it against `dom_inst` — this LINKS the template's parameter/index
  # metavariables to whatever `dom_inst` already fixes (and vice versa). The
  # template alone rarely settles everything (`prepend`'s result index is `S(n)`,
  # with `n` still open), so we then process each PRESENT field to solve the rest:
  # infer the field argument and unify its type against the field's expected type
  # (`x : a` fixes the parameter), and when a field cannot infer standalone recurse
  # on it (`xs = empty()` fixes the length index from `empty`'s own `Z`). The result
  # is meta-solving only — `mctx` is mutated in place and the caller re-zonks
  # `dom_inst`; the actual argument term is still built by the ordinary
  # checking-mode elaboration once the domain is concrete, and the whole call is
  # kernel-re-checked by `finish_global_app`, so nothing unsound rests on this.
  # Additive and best-effort: a non-constructor argument, a foreign family, or a
  # unification failure (a genuine index mismatch like `empty : …Z` at `…S(n)`)
  # leaves `mctx` untouched, so a genuinely ambiguous domain still rejects.
  defp solve_deferred_domain({:function_call, meta, cargs}, dom_inst, mctx, names, ctx, env) do
    with name when is_binary(name) <- Keyword.get(meta, :name),
         cname = resolve_ctor_key(env, String.to_atom(name)),
         ctor when not is_nil(ctor) <- Inductive.get_ctor(env, cname),
         family when not is_nil(family) <- Inductive.ctor_family(env, cname),
         pc = length(Inductive.param_telescope(env, family) || []),
         {mctx_try, seed} <- fresh_seed(mctx, pc + length(ctor.args)),
         params = Enum.map(Map.get(ctor, :result_params, []), &Subst.instantiate(&1, seed)),
         indices = Enum.map(ctor.result_indices, &Subst.instantiate(&1, seed)),
         {:ok, mctx_try} <- Unify.unify({:data, family, params, indices}, dom_inst, mctx_try, env) do
      solve_ctor_present_fields(ctor, cargs, seed, pc, mctx_try, names, ctx, env)
    else
      _ -> mctx
    end
  end

  defp solve_deferred_domain(_arg, _dom_inst, mctx, _names, _ctx, _env), do: mctx

  # Allocate `n` fresh metavariables from `mctx`, returning the updated context and
  # the `[{:meta, id}]` seed frame.
  defp fresh_seed(mctx, n) do
    Enum.reduce(1..n//1, {mctx, []}, fn _, {m, acc} ->
      {m, id} = MetaCtx.fresh(m)
      {m, acc ++ [{:meta, id}]}
    end)
  end

  # Walk a constructor's fields, solving the seed's remaining metavariables from the
  # PRESENT field arguments. Mirrors `check_ctor_args`' framing exactly: each field
  # type is instantiated over `params ++ (field values so far)` — a growing frame
  # whose LENGTH the de Bruijn indices depend on, so the seed value of every field
  # (the pinned metavariable for an erased index, the elaborated term for a present
  # one) is threaded through `acc`. Erased fields carry no surface argument (their
  # value is a seed metavariable a present field determines); a present field whose
  # instantiated type still bears a metavariable is solved from its argument
  # (inferred and unified, or recursively solved when it cannot infer standalone —
  # `xs = empty()` fixing the length index from `empty`'s own `Z`). Best-effort:
  # any failure returns the `mctx` reached so far, which the caller re-zonks and
  # gates, so a genuinely ambiguous domain still rejects.
  defp solve_ctor_present_fields(ctor, arg_asts, seed, pc, mctx, names, ctx, env) do
    params = Enum.take(seed, pc)
    slots = Enum.zip(ctor.args, ctor.quantities)
    solve_fields(slots, arg_asts, seed, pc, params, [], mctx, names, ctx, env)
  end

  defp solve_fields([], _asts, _seed, _pc, _params, _acc, mctx, _names, _ctx, _env), do: mctx

  defp solve_fields([{{_fn, _ft}, :erased} | slots], asts, seed, pc, params, acc, mctx, names, ctx, env) do
    val = seed |> Enum.at(pc + length(acc)) |> Unify.zonk(mctx)
    solve_fields(slots, asts, seed, pc, params, [val | acc], mctx, names, ctx, env)
  end

  defp solve_fields([{{_fn, _ft}, :unrestricted} | _slots], [], _seed, _pc, _params, _acc, mctx, _names, _ctx, _env),
    do: mctx

  defp solve_fields([{{_fn, ftype}, :unrestricted} | slots], [arg | rest], seed, pc, params, acc, mctx, names, ctx, env) do
    ftype_inst = ftype |> Subst.instantiate(params ++ Enum.reverse(acc)) |> Unify.zonk(mctx)

    {mctx, val} = solve_field(arg, ftype_inst, mctx, names, ctx, env)
    solve_fields(slots, rest, seed, pc, params, [val | acc], mctx, names, ctx, env)
  end

  # Solve a present field's expected type from its argument and return an updated
  # `mctx` and a value term for the frame. When the type is concrete, check the
  # argument; when it still bears a metavariable, infer the argument and unify its
  # type against the expected type (or, if it cannot infer standalone, recursively
  # solve it from its own constructor and then check against the now-concrete type).
  # A field that cannot be elaborated contributes the expected type's own shape as an
  # opaque placeholder value — enough to keep later fields' frames aligned; the
  # caller's re-zonk and the kernel re-check gate correctness regardless.
  defp solve_field(arg, ftype_inst, mctx, names, ctx, env) do
    cond do
      not has_meta?(ftype_inst) ->
        term =
          case elaborate_expr_checked(arg, ftype_inst, names, ctx, env) do
            {:ok, term} -> term
            {:error, _} -> ftype_inst
          end

        {mctx, term}

      true ->
        case elaborate_expr_typed(arg, names, ctx, env) do
          {:ok, term, ty} ->
            ty_term = Quote.reify(ty, Context.length(ctx))

            case Unify.unify(ftype_inst, ty_term, mctx, env) do
              {:ok, mctx} -> {mctx, term}
              {:error, _} -> {mctx, term}
            end

          {:error, _} ->
            mctx = solve_deferred_domain(arg, ftype_inst, mctx, names, ctx, env)
            concrete = Unify.zonk(ftype_inst, mctx)

            term =
              if has_meta?(concrete) do
                concrete
              else
                case elaborate_expr_checked(arg, concrete, names, ctx, env) do
                  {:ok, term} -> term
                  {:error, _} -> concrete
                end
              end

            {mctx, term}
        end
    end
  end

  # Bidirectional checking-mode constructor elaboration, used only as a fallback
  # when the inference path fails (an underdetermined nested constructor like
  # `Cons(Z(), Nil())` at `-> List(Nat)`). Rather than infer each argument, it
  # solves the family parameters from the *expected* type — the constructor's
  # result applied to fresh metavariables, unified against `expected_core` — and
  # then *checks* each present argument against its field type instantiated with
  # the solved parameters (and the arguments checked so far, mirroring
  # `solve_arg`'s frame). The assembled constructor is still kernel-re-checked by
  # the caller, so this can only ever accept a term the kernel independently
  # accepts. Restricted to all-present constructors (List/Maybe/tree shapes); an
  # erased field bails so the caller reports the original inference error.
  defp elaborate_ctor_app_bidirectional(env, cname, arg_asts, names, ctx, expected_core)
       when expected_core != nil do
    ctor = Inductive.get_ctor(env, cname)
    family = Inductive.ctor_family(env, cname)
    param_tele = Inductive.param_telescope(env, family) || []
    pc = length(param_tele)

    cond do
      is_nil(ctor) or is_nil(family) ->
        {:error, {:unknown_constructor, cname}}

      # Guard-ordered AFTER the nil check: `ctor.quantities` is only reached once
      # `ctor` is known non-nil (an unknown ctor would otherwise crash here before
      # the graceful error above could fire).
      Enum.count(ctor.quantities, &Grade.present?/1) != length(arg_asts) ->
        {:error, {:constructor_arity_mismatch, cname}}

      true ->
        # Fresh metas for the params ++ every argument (including erased index
        # fields), so the constructor's result type — which references that whole
        # frame — can be built and pinned against the goal before any argument is
        # known. Pinning solves the parameters and the erased indices; the present
        # fields are then checked against their now-concrete types.
        {mctx, seed} =
          Enum.reduce(1..(pc + length(ctor.args)), {MetaCtx.new(), []}, fn _, {m, acc} ->
            {m, id} = MetaCtx.fresh(m)
            {m, acc ++ [{:meta, id}]}
          end)

        params = Enum.map(Map.get(ctor, :result_params, []), &Subst.instantiate(&1, seed))
        indices = Enum.map(ctor.result_indices, &Subst.instantiate(&1, seed))

        case Unify.unify({:data, family, params, indices}, expected_core, mctx, env) do
          {:error, _} ->
            {:error, {:constructor_result_mismatch, cname}}

          {:ok, mctx} ->
            solved_params = seed |> Enum.take(pc) |> Enum.map(&Unify.zonk(&1, mctx))

            if Enum.any?(solved_params, &has_meta?/1) do
              {:error, {:unsolved_parameters, cname}}
            else
              slots =
                ctor.args
                |> Enum.zip(ctor.quantities)
                |> Enum.with_index()
                |> Enum.map(fn {{{_fn, ftype}, q}, i} -> {i, ftype, q} end)

              check_ctor_args(slots, arg_asts, seed, pc, solved_params, [], mctx, names, ctx, env, cname)
            end
        end
    end
  end

  # Assemble a constructor's argument list against the solved parameters and the
  # binder-solved erased indices. Walks every field: an erased field takes its
  # value from the pinned metavariable (an index the expected type determined); a
  # present field is checked against its field type instantiated with the
  # parameters and every earlier field value (the same `params ++ fields` frame the
  # de Bruijn layout uses). The erased field values are kept in the assembled
  # `{:ctor, …}`, matching `finish_ctor_app`.
  defp check_ctor_args(slots, arg_asts, seed, pc, params, _acc0, mctx, names, ctx, env, cname) do
    # Idris-style DEFERRAL (TTImp.Elab.App `checkRestApp`/`checkRtoL`): a present field whose
    # instantiated type still carries a metavariable is POSTPONED, its siblings resolved first —
    # which solves that metavariable — and it is then checked. Iterated to a fixpoint so any
    # dependency order works. Erased index slots seed the assembly with their goal-pinned
    # metavariable and are re-zonked at the end; positions are kept so the de Bruijn frame stays
    # correct regardless of resolution order.
    args_by_pos =
      slots
      |> Enum.filter(fn {_i, _ft, q} -> q == :unrestricted end)
      |> Enum.map(&elem(&1, 0))
      |> Enum.zip(arg_asts)
      |> Map.new()

    acc0 = for {i, _ft, :erased} <- slots, into: %{}, do: {i, Enum.at(seed, pc + i)}
    pending = for {i, ft, :unrestricted} <- slots, do: {i, ft}

    case resolve_ctor_fields(pending, acc0, args_by_pos, seed, pc, params, mctx, names, ctx, env, cname) do
      {:ok, acc_map, mctx} ->
        vals = for i <- 0..(length(slots) - 1)//1, do: Unify.zonk(Map.fetch!(acc_map, i), mctx)

        if Enum.any?(vals, &has_meta?/1) do
          {:error, {:unsolved_index, cname}}
        else
          {:ok, {:ctor, cname, vals}}
        end

      {:error, _} = err ->
        err
    end
  end

  # One sweep over the still-pending present fields, recursing while progress is made. A field
  # whose instantiated type is CONCRETE is checked; one whose type still has a metavariable is
  # tried by INFERENCE (solving the metavariable from the argument's own type, as a recursive
  # call or concrete constructor does) and otherwise DEFERRED to a later sweep, once a sibling
  # solves it.
  defp resolve_ctor_fields([], acc_map, _args, _seed, _pc, _params, mctx, _names, _ctx, _env, _cname),
    do: {:ok, acc_map, mctx}

  defp resolve_ctor_fields(pending, acc_map, args, seed, pc, params, mctx, names, ctx, env, cname) do
    swept =
      Enum.reduce(pending, {[], acc_map, mctx, false, nil}, fn {i, ftype}, {pend, amap, mctx, prog, err} ->
        if err != nil do
          {pend, amap, mctx, prog, err}
        else
          frame = params ++ frame_prefix(amap, seed, pc, i, mctx)
          ftype_inst = ftype |> Subst.instantiate(frame) |> Unify.zonk(mctx)
          arg = Map.fetch!(args, i)

          if has_meta?(ftype_inst) do
            case try_infer_field(arg, ftype_inst, mctx, names, ctx, env) do
              {:ok, term, mctx2} -> {pend, Map.put(amap, i, term), mctx2, true, nil}
              :defer -> {[{i, ftype} | pend], amap, mctx, prog, nil}
            end
          else
            case elaborate_expr_checked(arg, ftype_inst, names, ctx, env) do
              {:ok, term} -> {pend, Map.put(amap, i, term), mctx, true, nil}
              {:error, _} = e -> {pend, amap, mctx, prog, e}
            end
          end
        end
      end)

    case swept do
      {_pend, _amap, _mctx, _prog, {:error, _} = err} ->
        err

      {[], acc_map, mctx, _prog, nil} ->
        {:ok, acc_map, mctx}

      {pend, acc_map, mctx, true, nil} ->
        resolve_ctor_fields(Enum.reverse(pend), acc_map, args, seed, pc, params, mctx, names, ctx, env, cname)

      {_pend, _amap, _mctx, false, nil} ->
        # A full sweep resolved nothing but fields remain: their types stay under-determined.
        {:error, {:unsolved_field_type, cname}}
    end
  end

  # The de Bruijn frame prefix for the field at position `i`: positions `0..i-1`, each taken from
  # the resolved assembly, else its seed placeholder (an unresolved sibling is a metavariable,
  # which keeps this field deferred until that sibling is resolved).
  defp frame_prefix(_amap, _seed, _pc, 0, _mctx), do: []

  defp frame_prefix(amap, seed, pc, i, mctx) do
    for j <- 0..(i - 1)//1 do
      (Map.get(amap, j) || Enum.at(seed, pc + j)) |> Unify.zonk(mctx)
    end
  end

  # Infer an argument independently and unify its type back into `mctx`, solving a field-type
  # metavariable that only this argument determines (e.g. a recursive call whose result type
  # fixes an intermediate index). Returns `:defer` when the argument cannot be inferred in
  # isolation (e.g. a nullary constructor with its own implicit index) — it is retried once its
  # field type becomes concrete.
  defp try_infer_field(arg, ftype_inst, mctx, names, ctx, env) do
    with {:ok, term, ty} <- elaborate_expr_typed(arg, names, ctx, env),
         ty_term = Quote.reify(ty, Context.length(ctx)),
         {:ok, mctx2} <- Unify.unify(ftype_inst, ty_term, mctx, env) do
      {:ok, term, mctx2}
    else
      _ -> :defer
    end
  end

  # Inference-mode counterpart of `elaborate_ctor_app_bidirectional`, used only as
  # a fallback when up-front inference of a constructor's arguments fails (a nested
  # underdetermined constructor as a bare argument, `Cons(Z(), Nil())`, whose inner
  # `Nil()` no expected type reaches). Elaborates the arguments left to right,
  # solving the family parameters from the ones that infer (`Z() : Nat` fixes `a`)
  # and *checking* those that do not against their now-concrete field type
  # (`Nil()` against `Lst(Nat)`). The resulting argument/type pairs feed the
  # ordinary `elaborate_ctor_app`, which re-derives parameters and result type, so
  # nothing new is trusted. Restricted to all-present constructors.
  defp elaborate_ctor_app_infer_bidirectional(env, cname, arg_asts, names, ctx) do
    ctor = Inductive.get_ctor(env, cname)
    family = Inductive.ctor_family(env, cname)
    param_tele = Inductive.param_telescope(env, family) || []
    pc = length(param_tele)

    cond do
      is_nil(ctor) or is_nil(family) ->
        {:error, {:unknown_constructor, cname}}

      Enum.any?(ctor.quantities, &Grade.erased?/1) ->
        {:error, {:bidirectional_erased_field, cname}}

      length(ctor.args) != length(arg_asts) ->
        {:error, {:constructor_arity_mismatch, cname}}

      true ->
        {mctx, param_metas} =
          Enum.reduce(1..pc//1, {MetaCtx.new(), []}, fn _, {m, acc} ->
            {m, id} = MetaCtx.fresh(m)
            {m, acc ++ [{:meta, id}]}
          end)

        case infer_ctor_args(ctor.args, arg_asts, param_metas, [], mctx, names, ctx, env) do
          {:ok, present} -> elaborate_ctor_app(env, cname, present, ctx)
          {:error, _} = err -> err
        end
    end
  end

  # Elaborate each constructor argument, threading the (scratch) parameter
  # metavariables: instantiate the field type with the parameters and the argument
  # terms chosen so far and zonk it; if it is metavariable-free the argument is
  # *checked* against it, otherwise it is *inferred* and its type unified against
  # the field type to solve parameters. Returns `[{term, type_term}]` for
  # `elaborate_ctor_app`.
  defp infer_ctor_args([], [], _params, acc, _mctx, _names, _ctx, _env),
    do: {:ok, Enum.reverse(acc)}

  defp infer_ctor_args([{_fname, ftype} | fields], [arg | args], params, acc, mctx, names, ctx, env) do
    frame = params ++ (acc |> Enum.reverse() |> Enum.map(&elem(&1, 0)))
    ftype_inst = ftype |> Subst.instantiate(frame) |> Unify.zonk(mctx)

    step =
      if has_meta?(ftype_inst) do
        with {:ok, term, ty} <- elaborate_expr_typed(arg, names, ctx, env),
             ty_term = Quote.reify(ty, Context.length(ctx)),
             {:ok, mctx} <- Unify.unify(ftype_inst, ty_term, mctx, env) do
          {:ok, term, ty_term, mctx}
        end
      else
        with {:ok, term} <- elaborate_expr_checked(arg, ftype_inst, names, ctx, env) do
          {:ok, term, ftype_inst, mctx}
        end
      end

    case step do
      {:ok, term, ty_term, mctx} ->
        infer_ctor_args(fields, args, params, [{term, ty_term} | acc], mctx, names, ctx, env)

      {:error, _} = err ->
        err
    end
  end

  # A saturated call to a global function with implicit (erased) parameters.
  # Peels the function's Π telescope, pairs each domain with its quantity, and
  # runs the shared `solve_arg` loop: erased slots become fresh metavariables,
  # present slots unify against the supplied arguments. Returns the applied term
  # and its result type (the codomain instantiated with the solved arguments).
  defp elaborate_global_app(env, name, present_args, ctx, expected \\ nil) do
    %{type: pi_type, quantities: quantities} = Env.get_def(env, name)
    {domains, codomain} = peel_pi(pi_type, length(quantities))

    telescope = Enum.zip(Enum.map(domains, &{:_, &1}), quantities)
    init = {:ok, MetaCtx.new(), [], present_args}

    # GOAL-DIRECTED solving, for an anonymous-union goal only.
    #
    # `solve_arg` receives arguments already elaborated and merely UNIFIES each domain
    # against the argument's inferred type. So for `Std.Map.put(:a, 1, …)` checked at
    # `Map(Atom, Int | Bool)`, the value slot's domain is the still-unsolved implicit
    # `?v`, and unifying it with the argument's `Int` locks `?v := Int`. The codomain
    # is only unified with the goal afterwards (in `finish_global_app`), by which point
    # `Map(Atom, Int)` no longer matches `Map(Atom, Union<Bool|Int>)` — and there is no
    # container covariance to rescue it. The union never got a chance to inject.
    #
    # Implicit (erased) slots come FIRST in the telescope, so their metavariables exist
    # before any present argument is processed. Solving the codomain against the goal at
    # that point pins `?v := Union<Bool|Int>`, and `solve_arg` can then coerce each value
    # into it (see the union clause there). This is how Idris/Agda elaborate an
    # application: the goal flows in before the arguments.
    #
    # GATED on the goal mentioning a generated union family. Doing it for EVERY checked
    # call is the fully Idris-faithful behaviour and is the natural generalisation, but
    # it reorders solving for every call in the language — a broad regression surface
    # that deserves its own change. Gated, no non-union program's inference can differ.
    {erased, rest} = Enum.split_while(telescope, fn {_d, q} -> q == :erased end)

    init =
      if union_goal?(expected) do
        erased
        |> Enum.reduce_while(init, &solve_arg(&1, &2, env))
        |> solve_codomain_from_goal(codomain, expected, env, rest)
      else
        init
      end

    telescope = if union_goal?(expected), do: rest, else: telescope

    telescope
    |> Enum.reduce_while(init, &solve_arg(&1, &2, env))
    |> finish_global_app(name, codomain, ctx, env, expected)
  end

  @doc """
  True iff `expected` is a Core type mentioning a generated anonymous-union family.

  `Declarations.elaborate_body/6` uses this to route a union-goal body through CHECK
  mode. Its default is infer, which never threads the declared return type into the
  application — so goal-directed solving (see `elaborate_global_app`) would never see a
  goal, and a value destined for a union member would lock the union's implicit to its
  own type instead.
  """
  @spec union_goal?(term()) :: boolean()
  def union_goal?(nil), do: false

  def union_goal?(term) when is_tuple(term) do
    case term do
      {:data, name, _p, _i} ->
        Cure.Elab.Union.union_family?(name) or
          term |> Tuple.to_list() |> Enum.any?(&union_goal?/1)

      _ ->
        term |> Tuple.to_list() |> Enum.any?(&union_goal?/1)
    end
  end

  def union_goal?(list) when is_list(list), do: Enum.any?(list, &union_goal?/1)
  def union_goal?(_other), do: false

  # Unify the codomain against the goal so goal-determined implicits are solved BEFORE
  # the present arguments are matched. A failure is swallowed: the ordinary path then
  # produces the honest error, and the kernel independently re-checks the assembled
  # term, so this can only SOLVE metavariables — never cause an unsound accept.
  #
  # `chosen` holds only the ERASED prefix, but `Subst.instantiate/2` indexes the codomain
  # against the FULL binder stack — instantiating with a short list mis-indexes and the
  # unify then fails silently, leaving the implicit unsolved (which is the whole bug this
  # exists to fix). So pad to full arity with placeholder metas for the not-yet-processed
  # present slots. They are used only to index the substitution and are discarded: the
  # real arguments are unified against their domains by `solve_arg` as usual.
  defp solve_codomain_from_goal({:ok, mctx, chosen, present}, codomain, expected, env, remaining) do
    {mctx_padded, padded} =
      Enum.reduce(remaining, {mctx, chosen}, fn {{_n, ty}, _q}, {m, acc} ->
        {m, id} = MetaCtx.fresh(m, Subst.instantiate(ty, acc))
        {m, acc ++ [{:meta, id}]}
      end)

    case Unify.unify(Subst.instantiate(codomain, padded), expected, mctx_padded, env) do
      {:ok, mctx2} -> {:ok, mctx2, chosen, present}
      {:error, _} -> {:ok, mctx, chosen, present}
    end
  end

  defp solve_codomain_from_goal({:error, _} = err, _codomain, _expected, _env, _remaining), do: err

  defp peel_pi(type, 0), do: {[], type}

  defp peel_pi({:pi, _g, d, c}, n) do
    {ds, co} = peel_pi(c, n - 1)
    {[d | ds], co}
  end

  defp finish_global_app({:error, _} = err, _name, _cod, _ctx, _env, _expected), do: err

  defp finish_global_app({:ok, _mctx, _chosen, [_ | _]}, _name, _cod, _ctx, _env, _expected),
    do: {:error, :too_many_arguments}

  defp finish_global_app({:ok, mctx, chosen, []}, name, codomain, ctx, env, expected) do
    name = Env.resolve_key(env, env.defs, name)

    # When an expected result type is threaded in from checking mode, unify the
    # instantiated codomain against it BEFORE the `has_meta?` rejection below. This
    # lets an implicit determined by NEITHER argument — only by the expected return
    # type (a phantom parameter, `mk : {a} -> {b} -> a -> Const(a, b)` at
    # `-> Const(Nat, Bool)`) — get solved. The instantiated codomain lives in the
    # caller's frame, the same frame as `expected`, so they unify directly (no
    # shift). A unify failure is swallowed (keep the old mctx) so the honest
    # `:unsolved_metavariables` error is still produced below; the caller's kernel
    # re-check independently gates the assembled term, so this only SOLVES
    # metavariables and cannot cause an unsound accept.
    expected_for_unify =
      if expected != nil do
        case Kernel.normalize(ctx, expected) do
          :fuel_exhausted -> expected
          normalized -> normalized
        end
      end

    mctx =
      if expected_for_unify != nil do
        case Unify.unify(Subst.instantiate(codomain, chosen), expected_for_unify, mctx, env) do
          {:ok, mctx2} -> mctx2
          {:error, _} -> mctx
        end
      else
        mctx
      end

    args = Enum.map(chosen, &Unify.zonk(&1, mctx))

    if Enum.any?(args, &has_meta?/1) do
      {:error, {:unsolved_metavariables, name}}
    else
      term = Enum.reduce(args, {:global, name}, fn a, acc -> {:app, acc, a} end)
      # The instantiated codomain lives in the caller's frame; evaluate it under
      # the caller's environment so its context variables get correct de Bruijn
      # levels (evaluating under `[]` would conflate index and level).
      result_type = Eval.eval(Subst.instantiate(codomain, args), Context.env(ctx))
      {:ok, term, result_type}
    end
  end

  defp has_meta?({:meta, _}), do: true
  defp has_meta?({:data, _n, ps, is}), do: Enum.any?(ps ++ is, &has_meta?/1)
  defp has_meta?({:ctor, _n, args}), do: Enum.any?(args, &has_meta?/1)
  defp has_meta?({:app, f, x}), do: has_meta?(f) or has_meta?(x)
  defp has_meta?({:pi, _g, d, c}), do: has_meta?(d) or has_meta?(c)
  defp has_meta?({:lam, _g, d, b}), do: has_meta?(d) or has_meta?(b)
  defp has_meta?({:let, _g, t, v, b}), do: has_meta?(t) or has_meta?(v) or has_meta?(b)

  defp has_meta?({:case, s, m, branches}),
    do: has_meta?(s) or has_meta?(m) or Enum.any?(branches, fn {_ctor, _arity, body} -> has_meta?(body) end)

  defp has_meta?({:effect_type, inner}), do: has_meta?(inner)
  defp has_meta?({:effect_pure, value}), do: has_meta?(value)
  defp has_meta?({:effect_bind, effect, continuation}), do: has_meta?(effect) or has_meta?(continuation)
  defp has_meta?(_), do: false

  # -- parameters / binders ---------------------------------------------------

  defp elaborate_params([], _scope, _env), do: {:ok, []}

  defp elaborate_params([{:param, pmeta, pname} | rest], scope, env) do
    with {:ok, ptype} <- elaborate_type(Keyword.fetch!(pmeta, :type), scope, env),
         {:ok, more} <- elaborate_params(rest, [pname | scope], env) do
      {:ok, [{pname, ptype} | more]}
    end
  end

  # Wrap a Core body in λ's (or Π's) over the parameter telescope, p0 outermost.
  # Same shape as `Declarations.wrap_binders/3`: the binder tuple is assembled
  # from a TAG, invisible to any textual migration. Grade threaded explicitly.
  defp wrap(tag, tele, body) do
    g = Cure.Core.Grade.unrestricted()
    Enum.reduce(Enum.reverse(tele), body, fn {_name, type}, acc -> {tag, g, type, acc} end)
  end

  defp single_body([expr]), do: expr
  defp single_body(expr), do: expr

  # -- expressions ------------------------------------------------------------

  @doc false
  def elaborate_expr({:variable, _meta, "Type"}, _scope, _env), do: {:ok, {:type, 0}}

  def elaborate_expr({:variable, _meta, name}, scope, env) do
    case Enum.find_index(scope, &(&1 == name)) do
      nil -> resolve_free(name, env)
      index -> {:ok, {:var, index}}
    end
  end

  def elaborate_expr({:function_call, meta, args}, scope, env)
      when is_list(meta) do
    if Keyword.get(meta, :record) do
      with {:ok, positional} <- desugar_record_construction(meta, args, env) do
        elaborate_expr(positional, scope, env)
      end
    else
      elaborate_named_call_scoped(meta, args, scope, env)
    end
  end

  def elaborate_expr({:record_update, meta, children}, scope, env) do
    with {:ok, positional} <- desugar_record_update(meta, children, env) do
      elaborate_expr(positional, scope, env)
    end
  end

  # Pair introduction `%[a, b]` in the scope-based term builder (function
  # arguments and other sub-terms). Emits the builtin Sigma ctor `mk_pair`; its Σ
  # type is derived by `Kernel.infer` on the enclosing application, which checks the
  # ctor against the callee's domain (so a dependent Σ parameter is honoured too).
  def elaborate_expr({:tuple, _meta, [a, b]}, scope, env) do
    with {:ok, a_core} <- elaborate_expr(a, scope, env),
         {:ok, b_core} <- elaborate_expr(b, scope, env) do
      {:ok, {:ctor, sigma_ctor_name(env), [a_core, b_core]}}
    end
  end

  def elaborate_expr({:literal, meta, value} = expr, scope, env) do
    case Keyword.get(meta, :subtype) do
      :boolean when is_boolean(value) ->
        {:ok, {:ctor, resolve_ctor_key(env, if(value, do: :True, else: :False)), []}}

      :integer when is_integer(value) ->
        {:ok, {:int_lit, value}}

      :float when is_float(value) ->
        {:ok, {:float_lit, value}}

      # The guard is required, not cosmetic: an unguarded negative `{:bounded_lit,
      # k}` reaching the kernel raises an uncaught `FunctionClauseError`
      # (`Kernel.infer/2` has no catch-all) — see spec §3.4.
      :char when is_integer(value) and value >= 0 and value <= 0x10FFFF ->
        {:ok, {:bounded_lit, value}}

      :char when is_integer(value) ->
        {:error, {:char_literal_out_of_range, value}}

      # A string literal argument IS `List(Char)` — desugar to its char-literal
      # list and re-enter, exactly as the typed/checked paths do (so `f("hi")`
      # and `f(['h','i'])` build the identical Cons spine).
      :string when is_binary(value) ->
        elaborate_expr(desugar_string(value, meta), scope, env)

      # A symbol literal argument `:ok` is an `Atom` value (Core `{:atom_lit, a}`).
      :symbol when is_atom(value) ->
        {:ok, {:atom_lit, value}}

      _ ->
        {:error, {:unsupported_expression, expr}}
    end
  end

  def elaborate_expr({:list, _, _} = node, scope, env),
    do: elaborate_expr(desugar_list(node), scope, env)

  # Quasiquotation (SP5.1): `quote <form>` lowers to the `Std.Syntax` builder
  # expression that constructs the reflected form, with `$(e)` splice holes
  # elaborated in place. Pure surface sugar — the lowered term re-enters the
  # ordinary elaborator (TCB delta 0).
  def elaborate_expr({:quoted_syntax, _meta, [inner]}, scope, env),
    do: elaborate_expr(Cure.Compiler.MacroSyntax.lower_quote(inner), scope, env)

  # A `$(e)` / `$(e ...)` splice reaching the elaborator as a bare node means it
  # sits outside any enclosing `quote` — a category error. Inside a quote,
  # `lower_quote/1` consumes the splice wrapper (only its inner expression
  # survives), so this clause fires only for an orphan splice.
  def elaborate_expr({tag, meta, _}, _scope, _env) when tag in [:splice, :splice_group],
    do: {:error, {:splice_outside_quote, tag, meta}}

  def elaborate_expr(other, _scope, _env), do: {:error, {:unsupported_expression, other}}

  # The registered Sigma constructor name (canonically `:mk_pair`), resolved via the
  # builtin registry (§1.4) rather than hard-coded; defaults to `:mk_pair` when no
  # Sigma family is registered (a raw `Env.empty()` elaboration).
  defp sigma_ctor_name(env) do
    with fam when not is_nil(fam) <- Inductive.builtin(env, :sigma),
         [%{name: n} | _] <- Inductive.ctors_of(env, fam) do
      n
    else
      _ -> :mk_pair
    end
  end

  defp unit_family_name(env), do: Env.resolve_key(env, env.families, :Unit)

  defp unit_ctor_name(env), do: Env.resolve_key(env, env.ctors, :unit)

  defp elaborate_named_call_scoped(meta, args, scope, env) do
    name = Keyword.fetch!(meta, :name)
    atom = String.to_atom(name)

    with {:ok, core_args} <- map_elaborate(args, scope, env, &elaborate_expr/3) do
      cond do
        Inductive.get_ctor(env, atom) ->
          ctor_key = Env.resolve_key(env, env.ctors, atom)

          # A constructor head applied to arguments is a saturated constructor, not
          # a chain of `{:app, …}`. Mirror `elaborate_type/3`'s ctor-aware clause:
          # this saturated-call clause builds the saturated ctor directly, while
          # `resolve_free` eta-expands bare positive-arity ctors (all-present,
          # unindexed) into lambdas and yields the nullary `{:ctor, atom, []}`
          # form otherwise.
          {:ok, {:ctor, ctor_key, core_args}}

        # A type FAMILY applied in EXPRESSION position — a type-level function body
        # such as `fn F(a) -> Type = Option(a)`, or a large-elim selector branch
        # returning a per-kind representation type over the ambient parameters
        # (`FocusShape(k, a, s)`). Split the arguments into the family's parameters
        # (prefix) and indices (suffix) and build the saturated `{:data, …}` node,
        # exactly as the type path does (`declarations.ex` `idx_to_core`). A local
        # binder shadows a family, so only take this branch when the name is NOT in
        # scope (an applied bound variable stays an `{:app, …}` chain below). Without
        # this the head resolved to `{:data, atom, [], []}` and the arguments were
        # `{:app}`-chained OUTSIDE it, so the kernel saw a 0-parameter data node
        # where the family needs parameters → a false `:arg_arity`.
        name not in scope and Inductive.family?(env, atom) ->
          family_key = Env.resolve_key(env, env.families, atom)
          {params, indices} = Enum.split(core_args, Inductive.param_count(env, family_key))
          {:ok, {:data, family_key, params, indices}}

        true ->
          with {:ok, head} <- elaborate_expr({:variable, [], name}, scope, env) do
            {:ok, Enum.reduce(core_args, head, fn arg, acc -> {:app, acc, arg} end)}
          end
      end
    end
  end

  # A free name is a nullary constructor, a global definition, or (fallback) a global ref.
  defp resolve_free(name, env) do
    atom = String.to_atom(name)

    cond do
      Inductive.get_ctor(env, atom) ->
        eta_expand_bare_ctor(env, Env.resolve_key(env, env.ctors, atom))

      Inductive.family?(env, atom) ->
        {:ok, {:data, Env.resolve_key(env, env.families, atom), [], []}}

      # A machine PRIMITIVE base type (Int/Float/Binary/Atom) in value position
      # is a first-class value of type `Type` — the same first-classness families
      # already get above (Idris/Agda/Lean: a type constructor name in term
      # position IS the type value). Primitives are `Env.put_primitive` bindings,
      # not families, so without this they fell through to `{:global, :Int}` →
      # `:unknown_global`. The kernel already types the primitive Core node
      # (`{:int_type}`, …) at `{:vtype, 0}`; this is a pure resolution fix.
      prim = Env.primitive(env, name) ->
        {:ok, prim}

      # Bare VALUE position mirrors the call-position R7 trichotomy: a name
      # provided by ≥2 re-keyed imports with no local/unshadowed winner is
      # ambiguous (E089), same tuple shape as the call site.
      length(Cure.Elab.Resolution.ambiguous_modules(env, atom)) >= 2 ->
        {:error, {:ambiguous_name, atom, Cure.Elab.Resolution.ambiguous_modules(env, atom)}}

      # A bare def key present is the local winner (or a non-colliding import that
      # kept its bare key): keep it. `resolve_bare/2`'s contract requires
      # this bare-absence check before the shadowed-import fallback, otherwise a
      # re-keyed sibling (`Std.Nat#plus`) would override a local `plus`.
      Env.get_def(env, atom) ->
        {:ok, {:global, Env.resolve_key(env, env.defs, atom)}}

      # No local winner, no ambiguity: if exactly one re-keyed import provides
      # the name, resolve to that qualified key; else keep the bare global.
      true ->
        case Cure.Elab.Resolution.resolve_bare(env, atom) do
          {:ok, key} -> {:ok, {:global, key}}
          _ -> {:ok, {:global, atom}}
        end
    end
  end

  # A bare positive-arity constructor reference eta-expands to nested lambdas
  # (`S` becomes `λ n:Nat. S(n)`) so first-class ctor values elaborate instead
  # of dying at the kernel's arity check (:ctor_arity) — the general gap behind
  # spec 2026-07-08-nat-int-erasure rule 4 (Idris allows bare `S` everywhere).
  # Scope: ctors whose args are all explicit/:unrestricted and whose result carries
  # no params/indices. An implicit-carrying or indexed ctor keeps today's
  # nullary resolution (and today's downstream error): a lambda-typed value
  # cannot receive implicit insertion at its call sites, so eta-expanding it
  # would produce an unusable value rather than a working one.
  defp eta_expand_bare_ctor(env, atom) do
    %{args: tele, quantities: qs, result_params: rp, result_indices: ri} =
      Inductive.get_ctor(env, atom)

    k = length(tele)

    if k > 0 and Enum.all?(qs, &Grade.present?/1) and rp == [] and ri == [] do
      body_args = for i <- (k - 1)..0//-1, do: {:var, i}
      body = {:ctor, atom, body_args}

      {:ok,
       Enum.reduce(Enum.reverse(tele), body, fn {_name, dom}, acc ->
         {:lam, Cure.Core.Grade.unrestricted(), dom, acc}
       end)}
    else
      {:ok, {:ctor, atom, []}}
    end
  end

  # -- type expressions -------------------------------------------------------

  # Type→Core lowering has a single source of truth: `Declarations.lower_type/3`
  # (the live signature path's `idx_to_core`). This legacy entry — reached only by
  # `elaborate/2`, a pre-dependent-pipeline signature elaborator — delegates there
  # so both share name resolution, param/index splitting, and numeric-index
  # lowering (`Bounded(5)` → `{:nat_lit, 5}`) rather than reinventing an
  # impoverished copy that turned every unbound name into a phantom `{:data, …}`.
  defp elaborate_type(ast, scope, env), do: Cure.Elab.Declarations.lower_type(ast, scope, env)

  # -- helpers ----------------------------------------------------------------

  defp map_elaborate(asts, scope, env, fun) do
    Enum.reduce_while(asts, {:ok, []}, fn ast, {:ok, acc} ->
      case fun.(ast, scope, env) do
        {:ok, core} -> {:cont, {:ok, acc ++ [core]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end
end
