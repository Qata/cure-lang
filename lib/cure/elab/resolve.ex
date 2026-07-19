defmodule Cure.Elab.Resolve do
  @moduledoc """
  Resolve an interface-method call to a concrete implementation, and supply the
  dictionary a constrained function needs at its concrete call sites.

  When the head-positioned argument has a concrete type constructor (`Int`,
  `Bool`, a user ADT, …), a method inlines to the instance's mangled global
  (static dispatch). When the head is a rigid type variable — inside a
  polymorphic function constrained by `where Iface(a)` — the method projects off
  the implicit dictionary parameter that the constraint introduced (dynamic
  dispatch through a threaded runtime dictionary).

  A call to a constrained function (`same(x, y)` where `same` carries `where
  Eqs(a)`) is intercepted here too: the dictionary the callee expects is resolved
  from the argument that fixes `a` and appended as a trailing argument, so the
  ordinary implicit applicator threads it through.
  """

  alias Cure.Core.{Context, Env, Eval}
  alias Cure.Elab.{Coherence, Elaborator, Interface}

  @doc "Is `atom` the name of a method declared by some in-scope interface?"
  @spec method?(Env.t(), atom()) :: boolean()
  def method?(env, atom), do: Interface.for_method(env, atom) != nil

  @doc "Does `atom` name a global function that carries `where` constraints?"
  @spec constrained?(Env.t(), atom()) :: boolean()
  def constrained?(env, atom), do: Env.constrained(env, atom) != nil

  @doc """
  Elaborate `method(args...)` by resolving the instance from the head-positioned
  argument's type. Returns `{:ok, term, type_value}` or an error (notably
  `{:no_instance, iface, head}`).
  """
  @spec method_call(Env.t(), atom(), [term()], [term()], term()) ::
          {:ok, term(), term()} | {:error, term()}
  def method_call(env, method, args, names, ctx) do
    desc = Interface.for_method(env, method)
    idx = head_param_index(desc, method)
    head_ast = Enum.at(args, idx)

    # Only the head-positioned argument is elaborated here — enough to classify the
    # instance. The remaining arguments (which may be lambdas needing checking mode)
    # are elaborated by the application machinery once the callee is fixed.
    with {:ok, _term, tval} <- Elaborator.elaborate_expr_typed(head_ast, names, ctx, env) do
      case classify(env, tval, MapSet.new()) do
        {:concrete, hc} -> concrete(env, desc, method, hc, args, names, ctx)
        {:rigid, lvl} -> abstract(env, desc, method, args, lvl, names, ctx)
        {:unknown, tval2} -> {:error, {:no_instance, desc.name, tval2}}
      end
    end
  end

  @doc """
  Elaborate a call to a constrained global `name(args...)`, appending the
  dictionary each `where Iface(a)` clause requires. The dictionary is resolved
  from the argument fixing `a` (concrete head → the instance dictionary value;
  rigid head → the in-scope dictionary binder) and threaded as a trailing
  argument through the ordinary implicit applicator.
  """
  @spec constrained_call(Env.t(), atom(), [term()], [term()], term()) ::
          {:ok, term(), term()} | {:error, term()}
  def constrained_call(env, name, args, names, ctx) do
    specs = Env.constrained(env, name)

    with {:ok, dict_asts} <- dict_arguments(specs, args, names, ctx, env) do
      Elaborator.elaborate_implicit_global_app(env, name, args ++ dict_asts, names, ctx)
    end
  end

  @doc """
  Build the dictionary value for interface `iface` at concrete head `head`:
  the single-constructor record `Iface{ m1 = impl₁, … }` over the instance's
  mangled method globals. Its type is `Iface(head)`. Used by the elaborator when
  it reaches a `{:dict_value, iface, head}` synthetic argument.
  """
  @spec dict_value(Env.t(), atom(), atom(), term()) :: {:ok, term(), term()} | {:error, term()}
  def dict_value(env, iface, head, ctx) do
    with {:ok, term} <- dict_term(env, iface, head) do
      iface_key = Env.resolve_key(env, env.families, iface)
      type = Eval.eval({:data, iface_key, [head_type_core(head)], []}, Context.env(ctx))
      {:ok, term, type}
    end
  end

  @doc "Resolve an interface dictionary directly from an already inferred type value."
  @spec dictionary_for_type_value(Env.t(), atom(), term(), term()) ::
          {:ok, term(), term()} | {:error, term()}
  def dictionary_for_type_value(env, iface, type_value, ctx) do
    case classify(env, type_value, MapSet.new()) do
      {:concrete, head} -> dict_value(env, iface, head, ctx)
      {:rigid, level} -> {:error, {:no_instance, iface, {:rigid, level}}}
      {:unknown, value} -> {:error, {:no_instance, iface, value}}
    end
  end

  # -- head classification ----------------------------------------------------

  # The head-positioned parameter is the one whose interface-signature type mentions
  # the head variable. A first-order interface mentions it BARE (`x : a`); a
  # higher-kinded one mentions it APPLIED (`container : f(a)`) and never bare — its
  # inferred type (`List(Int)`) still names the instance's type constructor, so that
  # parameter is the dispatch head just the same.
  #
  # Both forms are located explicitly. Defaulting the higher-kinded case to parameter
  # 0 only worked while the applied-head parameter happened to be declared first;
  # reordering to `fmap(g: (a) -> b, container: f(a))` — legal, and nothing in the
  # parser or `Cure.Elab.Interface` forbids it — classified `g` as the head and
  # reported `{:no_instance, ...}` for a correctly registered instance.
  #
  # `Interface.collect_head_uses/3` classifies the same two shapes; keep them aligned.
  defp head_param_index(desc, method) do
    info = Map.fetch!(desc.methods, method)
    hv = desc.head_var

    bare =
      Enum.find_index(info.params, fn {:param, pm, _} ->
        match?({:variable, _, ^hv}, Keyword.fetch!(pm, :type))
      end)

    applied =
      Enum.find_index(info.params, fn {:param, pm, _} ->
        applied_head?(Keyword.fetch!(pm, :type), hv)
      end)

    # `|| 0` is unreachable for any interface `Interface.infer_head_kind/3` accepted
    # (it requires at least one bare or applied use somewhere in the interface), but a
    # method that mentions the head only in its RETURN type has no head parameter.
    bare || applied || 0
  end

  # `f(a)` — the head variable in applied (higher-kinded) position. A function type
  # parses as `{:function_call, [name: "Function", function_type: true], _}`, so it
  # only matches when the interface's head variable is literally named `Function`.
  defp applied_head?({:function_call, fmeta, _args}, hv), do: Keyword.get(fmeta, :name) == hv
  defp applied_head?(_type, _hv), do: false

  # NOTE(int-facade): kept for totality on a legacy/deserialized `{:vint_type}`
  # value; fresh elaboration never produces one (spec 2026-07-18 §3a) — `Int`
  # normally reaches classification as `{:vdata, int_fid, []}`.
  defp classify(_env, {:vint_type}, _seen), do: {:concrete, :Int}
  defp classify(_env, {:vfloat_type}, _seen), do: {:concrete, :Float}
  # String has no primitive value former: `String = List(Char)` (the landed
  # value-surface design), so it reaches dispatch as the `nglobal` alias `String`
  # and is unfolded to `List(Char)` by the neutral-global clause below — it never
  # arrives as a `{:vstring_type}`. (`{:string_type}` is only an E-layer head-atom
  # sentinel in `head_type_core`; it is never evaluated.)
  defp classify(_env, {:vdata, name, _vs}, _seen), do: {:concrete, name}
  defp classify(_env, {:vneutral, {:nvar, lvl}}, _seen), do: {:rigid, lvl}

  # A transparent type synonym in head position (`String = List(Char)`) reaches
  # dispatch as a neutral global, because delta-reduction is on-demand. Unfold it
  # to its normal form and re-classify, so `combine` on a `String` finds the
  # `List` instance — the same alias-normalisation the coherence *registration*
  # side does (`Implementation.head_key`, which whnf's the elaborated head). Only
  # nullary type-level defs unfold; `seen` guards a cyclic alias chain.
  defp classify(env, {:vneutral, {:nglobal, name}} = v, seen) do
    if MapSet.member?(seen, name) do
      {:unknown, v}
    else
      case Env.get_def(env, name) do
        %{type: {:type, _}, body: body} when not is_nil(body) ->
          classify(env, Eval.eval(body, []), MapSet.put(seen, name))

        _ ->
          {:unknown, v}
      end
    end
  end

  defp classify(_env, other, _seen), do: {:unknown, other}

  # -- concrete (static) dispatch ---------------------------------------------
  # Inline the instance's mangled method global and elaborate the call through the
  # ordinary implicit-aware application machinery (so a lambda argument like
  # `fmap`'s `g` is checked against its domain, and any method-level implicits are
  # solved).
  defp concrete(env, desc, method, head, args, names, ctx) do
    case Coherence.lookup_anon(Env.coherence(env), desc.name, head) do
      {:ok, ref} ->
        mangled = Map.fetch!(ref.methods, method)
        Elaborator.elaborate_implicit_global_app(env, mangled, args, names, ctx)

      {:error, _} ->
        {:error, {:no_instance, desc.name, head}}
    end
  end

  # -- abstract (dynamic) dispatch --------------------------------------------
  # The head is a rigid type variable `a` at de Bruijn level `lvl`; the enclosing
  # `where Iface(a)` constraint put a dictionary binder of type `Iface(a)` in
  # scope. Find it by type (the only binder whose type is `Iface(<that rigid a>)`),
  # project the method field off it, and apply to the arguments (checking each so a
  # lambda argument is honoured).
  defp abstract(env, desc, method, args, lvl, names, ctx) do
    case find_dict_binder(ctx, names, desc.name, lvl, env) do
      {:ok, dict_name} ->
        with {:ok, proj, ptype} <-
               Elaborator.project_record_field(
                 {:variable, [], dict_name},
                 Atom.to_string(method),
                 names,
                 ctx,
                 env
               ) do
          Elaborator.apply_checked_args(proj, ptype, args, names, ctx, env)
        end

      :error ->
        {:error, {:no_instance, desc.name, {:rigid, lvl}}}
    end
  end

  # The surface name of the in-scope binder whose type value is exactly
  # `Iface(<rigid var at level lvl>)`, or `:error` if none.
  defp find_dict_binder(ctx, names, iface, lvl, env) do
    iface = Env.resolve_key(env, env.families, iface)
    target = {:vdata, iface, [{:vneutral, {:nvar, lvl}}]}
    n = Context.length(ctx)

    if n == 0 do
      :error
    else
      Enum.reduce_while(0..(n - 1), :error, fn k, _acc ->
        name = Enum.at(names, k)

        if is_binary(name) and Context.lookup(ctx, k) == target do
          {:halt, {:ok, name}}
        else
          {:cont, :error}
        end
      end)
    end
  end

  # -- dictionary arguments for a constrained call ----------------------------

  # One dictionary argument AST per constraint, in order. A concrete head yields
  # a `{:dict_value, iface, head}` synthetic node (the elaborator builds the
  # instance dictionary); a rigid head yields a reference to the in-scope
  # dictionary binder (re-threading the caller's own dictionary).
  defp dict_arguments(specs, args, names, ctx, env) do
    Enum.reduce_while(specs, {:ok, []}, fn spec, {:ok, acc} ->
      head_ast = Enum.at(args, spec.head_arg_index)

      case Elaborator.elaborate_expr_typed(head_ast, names, ctx, env) do
        {:ok, _term, tval} ->
          case classify(env, tval, MapSet.new()) do
            {:concrete, head} ->
              {:cont, {:ok, acc ++ [{:dict_value, spec.iface, head}]}}

            {:rigid, lvl} ->
              case find_dict_binder(ctx, names, spec.iface, lvl, env) do
                {:ok, dname} -> {:cont, {:ok, acc ++ [{:variable, [], dname}]}}
                :error -> {:halt, {:error, {:no_instance, spec.iface, {:rigid, lvl}}}}
              end

            {:unknown, tval2} ->
              {:halt, {:error, {:no_instance, spec.iface, tval2}}}
          end

        {:error, _} = err ->
          {:halt, err}
      end
    end)
  end

  # The single-constructor record value `Iface{ m1 = impl₁, … }`: the interface's
  # constructor applied to the instance's mangled method globals, in method order.
  # The erased head parameter is NOT a `:ctor` argument (it is recovered from the
  # value's type), so only the method fields appear.
  #
  # Each method is eta-expanded to its full arity — `λx.λy. impl(x, y)` rather than
  # a bare `{:global, impl}`. A dictionary method is projected and then applied one
  # argument at a time (the curried function-value ABI), but a multi-argument global
  # emits as a fixed-arity `fun name/n`, which a 1-argument apply would mis-call. The
  # eta-expansion lowers to curried 1-argument funs whose inner *saturated* spine is
  # a direct `impl(x, y)` call — ABI-correct at both the projection and the call.
  defp dict_term(env, iface, head) do
    case Coherence.lookup_anon(Env.coherence(env), iface, head) do
      {:ok, ref} -> {:ok, dict_term_from_ref(env, iface, ref)}
      {:error, _} -> {:error, {:no_instance, iface, head}}
    end
  end

  @doc """
  The dictionary value for an instance `ref`, independent of how the instance is registered.
  `dict_term/3` reaches this through the anonymous registry; `Cure.Elab.Implementation` uses it
  directly for a NAMED implementation, whose ref lives in the coherence table's `named` map and
  is invisible to `lookup_anon/3`.
  """
  @spec dict_term_from_ref(Env.t(), atom(), map()) :: term()
  def dict_term_from_ref(env, iface, ref) do
    desc = Env.get_interface(env, iface)

    fields =
      Enum.map(desc.method_order, fn m ->
        arity = length(Map.fetch!(desc.methods, m).params)
        eta_expand(env, Map.fetch!(ref.methods, m), arity)
      end)

    {:ctor, Env.resolve_key(env, env.ctors, iface), fields}
  end

  @doc "The Core type `Iface(head)` of a dictionary value for `iface` at `head`."
  @spec dict_type_term(Env.t(), atom(), atom()) :: term()
  def dict_type_term(env, iface, head),
    do: {:data, Env.resolve_key(env, env.families, iface), [head_type_core(head)], []}

  # `λ(d0).…λ(d_{n-1}). gname(v0, …, v_{n-1})` — the global eta-expanded to arity
  # `n`, taking each binder domain from the global's own Π type (closed for a
  # non-dependent method signature). A bare global (`n = 0`, or the value is used
  # unapplied) needs no wrapper.
  defp eta_expand(_env, gname, 0), do: {:global, gname}

  defp eta_expand(env, gname, arity) do
    %{type: pi} = Env.get_def(env, gname)
    domains = peel_domains(pi, arity)

    body =
      Enum.reduce(0..(arity - 1), {:global, gname}, fn i, acc ->
        {:app, acc, {:var, arity - 1 - i}}
      end)

    Enum.reduce(Enum.reverse(domains), body, fn dom, acc -> {:lam, Cure.Core.Grade.unrestricted(), dom, acc} end)
  end

  defp peel_domains(_pi, 0), do: []
  defp peel_domains({:pi, _g, dom, cod}, n), do: [dom | peel_domains(cod, n - 1)]
  defp peel_domains(_other, _n), do: []

  # `Int` is no longer a primitive: surface `Int` resolves to the inductive family
  # `Std.Int#Int` via the generic data clause below (spec 2026-07-18 surface flip),
  # exactly as `Nat` does. Float/String remain primitive base types.
  defp head_type_core(:Float), do: {:float_type}
  defp head_type_core(:String), do: {:string_type}
  defp head_type_core(name), do: {:data, name, [], []}
end
