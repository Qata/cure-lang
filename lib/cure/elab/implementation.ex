defmodule Cure.Elab.Implementation do
  @moduledoc """
  Elaborate a compile-time `implementation` (typeclass instance).

  Each method of the instance is lowered to an ordinary global definition with a
  mangled, collision-proof name (`__impl_<Iface>_<Head>_<method>`) and routed
  through the normal function pipeline — so it is type-checked, certified, and
  code-generated with no bespoke machinery. The coherence registry then records
  `(iface, head) → %{method => mangled_atom}`; `Cure.Elab.Resolve` reads that map
  to inline a method at a concrete call site or thread a runtime dictionary at an
  abstract one.

  A method the instance omits is filled from the interface's default body, with
  the interface head variable substituted by this instance's head type (so the
  default's `a`-typed signature becomes concrete). A method with neither an
  instance clause nor a default is a `:missing_method` error.
  """

  alias Cure.Core.{Env, Inductive}
  alias Cure.Elab.{Coherence, Declarations, Resolve}

  @doc """
  Register an implementation: build its mangled method defs, record the instance
  in the coherence registry, and register the method *signatures* in `env` (so
  forward references resolve). Returns the mangled `{:function_def, …}` decls for
  the caller to body-elaborate in the second pass, exactly like ordinary
  functions.
  """
  @spec register(tuple(), Env.t()) :: {:ok, Env.t(), [tuple()]} | {:error, term()}
  def register({:implementation, meta, body}, env) do
    iface = meta |> Keyword.fetch!(:interface) |> String.to_atom()
    head = meta |> Keyword.fetch!(:for) |> String.to_atom() |> normalize_head(env)
    for_type = Keyword.fetch!(meta, :for_type)
    as_name = Keyword.get(meta, :as)

    case Env.get_interface(env, iface) do
      nil ->
        {:error, {:no_such_interface, iface}}

      desc ->
        with :ok <- check_no_stray_clauses(desc, iface, body),
             {:ok, method_map, mangled_fns} <-
               build_methods(desc, iface, head, for_type, body),
             ref = %{iface: iface, head: head, methods: method_map, as: as_name},
             {:ok, env1} <- register_instance(env, iface, head, as_name, ref),
             {:ok, env2} <- register_signatures(mangled_fns, env1),
             {:ok, env3} <- bind_named_instance(env2, desc, iface, head, as_name, ref) do
          {:ok, env3, mangled_fns}
        end
    end
  end

  # The coherence key's head, resolved through transparent type synonyms.
  #
  # The parser sets `meta[:for]` to the RAW SURFACE NAME of the `for` clause, with no semantic
  # unfolding. `typealias MyInt = Int` is a transparent synonym at the type-checking level — the
  # two names denote definitionally the same type — but keying coherence on the spelling filed
  # `for Int` and `for MyInt` under two different atoms, so both anonymous instances registered.
  # Two live dictionaries for one type means `eqs(x, y)` can compute two different answers
  # depending on which spelling of the type the call site happened to use. Idris, Agda, Lean and
  # Rust all resolve an instance head to its normal form before comparing, precisely to rule
  # this out.
  #
  # A typealias elaborates to a nullary def `Name : Type := RHS`, so the unfolding is a def
  # lookup. `seen` guards a cyclic chain of aliases rather than trusting none exists.
  defp normalize_head(head, env), do: normalize_head(head, env, MapSet.new())

  defp normalize_head(head, env, seen) do
    if MapSet.member?(seen, head) do
      head
    else
      case Env.get_def(env, head) do
        %{type: {:type, _}, body: body} when not is_nil(body) ->
          head_atom(body, env, MapSet.put(seen, head), head)

        _ ->
          if Inductive.family?(env, head), do: Env.resolve_key(env, env.families, head), else: head
      end
    end
  end

  defp head_atom({:int_type}, _env, _seen, _fallback), do: :Int
  defp head_atom({:float_type}, _env, _seen, _fallback), do: :Float
  defp head_atom({:string_type}, _env, _seen, _fallback), do: :String
  defp head_atom({:data, name, _params, _indices}, _env, _seen, _fallback), do: name
  defp head_atom({:global, g}, env, seen, _fallback), do: normalize_head(g, env, seen)
  defp head_atom(_other, _env, _seen, fallback), do: fallback

  # Every clause in the implementation body must name one of the interface's methods.
  # `build_methods/5` iterates the INTERFACE's `method_order` and searches the body by
  # exact name, so a clause naming nothing (a typo: `eqz` for `eqs`) was never looked
  # at — it contributed nothing and produced no diagnostic. If the method the author
  # meant to override had an interface default, the implementation registered anyway,
  # silently using the default and discarding the author's clause. Idris 2 rejects a
  # stray clause; so do we.
  defp check_no_stray_clauses(desc, iface, body) do
    declared = MapSet.new(desc.method_order, &Atom.to_string/1)

    body
    |> Enum.flat_map(fn
      {:function_def, m, _b} -> [Keyword.fetch!(m, :name)]
      _ -> []
    end)
    |> Enum.find(&(not MapSet.member?(declared, &1)))
    |> case do
      nil -> :ok
      stray -> {:error, {:unknown_interface_method, iface, String.to_atom(stray)}}
    end
  end

  # -- methods ----------------------------------------------------------------

  # For each interface method (in declaration order) produce a mangled global
  # function_def — either the instance's own clause renamed, or the interface
  # default specialised to this head type. Returns the `method => mangled_atom`
  # map alongside the decls.
  defp build_methods(desc, iface, head, for_type, body) do
    Enum.reduce_while(desc.method_order, {:ok, %{}, []}, fn method, {:ok, mm, fns} ->
      mangled = mangled_name(iface, head, method)

      with {:ok, fn_decl, origin} <- method_def(desc, method, for_type, body),
           :ok <- check_method_signature(desc, iface, method, for_type, fn_decl, origin) do
        renamed = rename_fn(fn_decl, mangled)
        {:cont, {:ok, Map.put(mm, method, mangled), fns ++ [renamed]}}
      else
        :missing -> {:halt, {:error, {:missing_method, iface, method}}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # An instance clause for `method`, or the interface default specialised to the
  # instance's head type, or `:missing`. The tag says which — a default is synthesised
  # FROM the interface signature and so conforms by construction.
  defp method_def(desc, method, for_type, body) do
    mstr = Atom.to_string(method)

    case Enum.find(body, &function_def_named?(&1, mstr)) do
      {:function_def, _m, _b} = fd ->
        {:ok, fd, :instance}

      nil ->
        case Map.fetch(desc.defaults, mstr) do
          {:ok, default_body} ->
            {:ok, default_fn_def(desc, method, default_body, for_type), :default}

          :error ->
            :missing
        end
    end
  end

  # An implementation is a record literal, checked field-by-field against the record's
  # declared field types (Idris 2, Lean 4). Cure took the instance clause VERBATIM and
  # derived the mangled global's Pi type from the clause's OWN params/return_type, never
  # from the interface's. Nothing reconciled the two, so
  #
  #     interface Eqs(a)
  #       fn eqs(x: a, y: a) -> Bool
  #     implementation Eqs for Int
  #       fn eqs(x: Int, y: Int) -> Int = 42
  #
  # registered happily. Every USE site then failed with a bare
  # `{:conversion_failure, {:int_type}, {:data, :Bool, [], []}}` pointing at the caller
  # rather than at the implementation that broke its contract.
  #
  # The clause must declare the interface's signature with the head variable replaced by
  # this instance's head type, up to renaming of the method's other type variables
  # (`fmap`'s `a`/`b`). Lowercase-initial names are type variables and alpha-renamable;
  # uppercase names are type constructors and must match on the nose — the convention the
  # rest of the compiler already assumes.
  defp check_method_signature(_desc, _iface, _method, _for_type, _fn_decl, :default), do: :ok

  defp check_method_signature(desc, iface, method, for_type, {:function_def, m, _b}, :instance) do
    info = Map.fetch!(desc.methods, method)
    hv = desc.head_var

    expected = Enum.map(info.params, &param_type/1) ++ [info.return_type]
    expected = Enum.map(expected, &subst_head(&1, hv, for_type))
    actual = Enum.map(Keyword.get(m, :params, []), &param_type/1) ++ [Keyword.get(m, :return_type)]

    if length(expected) == length(actual) and alpha_equal?(expected, actual) do
      :ok
    else
      {:error, {:method_signature_mismatch, iface, method}}
    end
  end

  defp param_type({:param, pm, _pname}), do: Keyword.fetch!(pm, :type)

  # Structural equality of two surface type ASTs, modulo a consistent bijective renaming
  # of type variables (lowercase-initial names).
  defp alpha_equal?(expected, actual), do: match?({:ok, _}, alpha(expected, actual, %{}))

  defp alpha(xs, ys, sub) when is_list(xs) and is_list(ys) do
    if length(xs) == length(ys) do
      Enum.zip(xs, ys)
      |> Enum.reduce_while({:ok, sub}, fn {x, y}, {:ok, s} ->
        case alpha(x, y, s) do
          {:ok, s2} -> {:cont, {:ok, s2}}
          :error -> {:halt, :error}
        end
      end)
    else
      :error
    end
  end

  defp alpha({:variable, _, x}, {:variable, _, y}, sub), do: alpha_name(x, y, sub)

  defp alpha({:function_call, m1, a1}, {:function_call, m2, a2}, sub) do
    with true <- Keyword.get(m1, :function_type, false) == Keyword.get(m2, :function_type, false),
         {:ok, sub} <- alpha_name(Keyword.get(m1, :name), Keyword.get(m2, :name), sub) do
      alpha(a1, a2, sub)
    else
      _ -> :error
    end
  end

  defp alpha(same, same, sub), do: {:ok, sub}
  defp alpha(_x, _y, _sub), do: :error

  defp alpha_name(nil, nil, sub), do: {:ok, sub}

  defp alpha_name(x, y, sub) when is_binary(x) and is_binary(y) do
    cond do
      not (type_var?(x) and type_var?(y)) ->
        if x == y, do: {:ok, sub}, else: :error

      Map.has_key?(sub, x) ->
        if Map.fetch!(sub, x) == y, do: {:ok, sub}, else: :error

      y in Map.values(sub) ->
        # `y` is already the image of a different variable: not a bijection.
        :error

      true ->
        {:ok, Map.put(sub, x, y)}
    end
  end

  defp alpha_name(_x, _y, _sub), do: :error

  # Cure's convention (and the stdlib's): a lowercase-initial name in type position is a
  # type variable, an uppercase-initial one is a type constructor.
  defp type_var?(<<c::utf8, _::binary>>), do: c in ?a..?z
  defp type_var?(_), do: false

  defp function_def_named?({:function_def, m, _body}, name), do: Keyword.get(m, :name) == name
  defp function_def_named?(_other, _name), do: false

  # Synthesise a concrete function_def from the interface method's signature and
  # the default body, substituting the head variable with the instance's head
  # type in every parameter/return type.
  defp default_fn_def(desc, method, default_body, for_type) do
    info = Map.fetch!(desc.methods, method)
    head_var = desc.head_var

    params =
      Enum.map(info.params, fn {:param, pm, pname} ->
        {:param, Keyword.put(pm, :type, subst_head(Keyword.fetch!(pm, :type), head_var, for_type)), pname}
      end)

    return_type = subst_head(info.return_type, head_var, for_type)

    meta = [
      name: info.name,
      params: params,
      return_type: return_type,
      visibility: :public,
      arity: length(params)
    ]

    {:function_def, meta, [default_body]}
  end

  # Replace every occurrence of the head variable in a type AST with `for_type`, in BOTH
  # positions it can occupy: bare (`x : a`, first-order interface) and applied
  # (`container : f(a)`, higher-kinded — where the head name lives in the node's meta,
  # not among its children). Missing the applied case left `f(a)` unsubstituted, which
  # both mis-specialised a higher-kinded interface DEFAULT and made signature checking
  # impossible.
  defp subst_head({:variable, _m, name}, head_var, for_type) when name == head_var, do: for_type
  defp subst_head({:variable, _m, _} = v, _head_var, _for_type), do: v

  defp subst_head({:function_call, m, args}, head_var, for_type) do
    args = Enum.map(args, &subst_head(&1, head_var, for_type))

    case {Keyword.get(m, :name), type_ctor_name(for_type)} do
      {^head_var, ctor} when is_binary(ctor) and is_binary(head_var) ->
        {:function_call, Keyword.put(m, :name, ctor), args}

      _ ->
        {:function_call, m, args}
    end
  end

  defp subst_head(other, _head_var, _for_type), do: other

  defp type_ctor_name({:variable, _m, name}), do: name
  defp type_ctor_name(_other), do: nil

  defp rename_fn({:function_def, m, b}, mangled),
    do: {:function_def, Keyword.put(m, :name, Atom.to_string(mangled)), b}

  defp mangled_name(iface, head, method),
    do: :"__impl_#{iface}_#{head}_#{method}"

  # -- registration -----------------------------------------------------------

  defp register_instance(env, iface, head, as_name, ref) do
    coherence = Env.coherence(env) || Coherence.new()

    result =
      case as_name do
        nil -> Coherence.register_anon(coherence, iface, head, ref)
        name -> Coherence.register_named(coherence, String.to_atom(name), {iface, head}, ref)
      end

    case result do
      {:ok, coherence1} -> {:ok, Env.put_coherence(env, coherence1)}
      {:error, _} = err -> err
    end
  end

  # Cure's coherence policy is global uniqueness plus NAMED implementations as the escape hatch:
  # `implementation Eqs for Int as strictInt` registers under `:strictInt` "as an ordinary
  # dictionary-valued binding… A caller selects it explicitly with plain record projection,
  # `strictInt.eqs(x, y)` … no new call syntax is needed".
  #
  # `register_instance/5` only wrote the ref into `Coherence.named`. Nothing ever bound the atom
  # `:strictInt` to a value, and `Coherence.lookup_named/2` had zero callers in lib/ — so there
  # was no path by which any reference to `strictInt` could resolve. The escape hatch the policy
  # depends on to let a second, overlapping instance coexist was accepted at register time and
  # then permanently unreachable. Binding it as an ordinary global of type `Iface(head)` is what
  # makes record projection find it.
  #
  # A higher-kinded interface has no Core dictionary record family to be a value of
  # (`Interface.declare_dictionary_former/2` builds one only for a `:type` head kind), so there
  # is nothing to bind; that gap is tracked with the abstract-dispatch gap it belongs to.
  defp bind_named_instance(env, _desc, _iface, _head, nil, _ref), do: {:ok, env}

  defp bind_named_instance(env, %{head_kind: :type}, iface, head, name, ref) do
    term = Resolve.dict_term_from_ref(env, iface, ref)
    {:ok, Env.add_def(env, String.to_atom(name), Resolve.dict_type_term(env, iface, head), term)}
  end

  defp bind_named_instance(env, _desc, _iface, _head, _name, _ref), do: {:ok, env}

  defp register_signatures(fn_decls, env) do
    Enum.reduce_while(fn_decls, {:ok, env}, fn fd, {:ok, acc} ->
      case Declarations.register_signature(fd, acc) do
        {:ok, acc2} -> {:cont, {:ok, acc2}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end
end
