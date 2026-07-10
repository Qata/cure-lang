defmodule Cure.Elab.Deriving do
  @moduledoc """
  Generate a structural typeclass instance for a `type … deriving Iface` clause.

  Deriving is defined for the canonical interfaces `Equatable` (method `eq`),
  `Ord` (method `lt`), and `Show` (method `show`). For a derivable interface this
  module synthesises an `{:implementation, …}` AST whose method matches the type's
  constructors and compares/orders each field **through that field's own instance
  method**, called by name — so a recursive field resolves to the in-progress
  instance (registered in the first pass, before any body elaborates) and a
  primitive field resolves to its primitive instance. The synthesised
  implementation is routed through `Cure.Elab.Implementation.register/2`, exactly
  like a hand-written instance, so there is no bespoke registration path.

  The generated bodies use no boolean connective and no tuple: conjunction and
  the lexicographic order fold are expressed as nested `match` on `Bool`, which is
  self-contained in any module (the retired `&&`/`||` connectives and the still-open
  flat-tuple value surface are both avoided).

  `Show` renders to `String`, but the dependent pipeline has no string
  concatenation or `Int → String` primitive yet (that arrives with the String
  value surface, roadmap #27/#29). Rather than emit a `Show` instance that cannot
  elaborate, `generate/3` returns `{:error, {:deriving_needs_strings, :Show}}`; a
  `Show` clause is added here once those primitives land.
  """

  alias Cure.Core.Env

  @doc """
  Build the `{:implementation, …}` AST deriving `iface` for the ADT described by
  `container`. Refuses, rather than emit an instance that cannot elaborate, with:

    * `{:deriving_needs_strings, :Show}` — `Show` (no string primitives yet)
    * `{:cannot_derive, iface}` — a non-derivable interface
    * `{:no_such_interface, iface}` — the interface is not in scope
    * `{:cannot_derive_shape, iface, type}` — the container has no variants
    * `{:deriving_needs_constraints, iface, type}` — a constructor field has the
      bound type parameter's own type, so the instance would need a dictionary
      the derivation cannot thread
  """
  @spec generate(atom(), tuple(), Env.t()) :: {:ok, tuple()} | {:error, term()}
  def generate(:Show, _container, _env), do: {:error, {:deriving_needs_strings, :Show}}

  def generate(iface, {:container, meta, body}, env) when iface in [:Equatable, :Ord] do
    case Env.get_interface(env, iface) do
      nil ->
        {:error, {:no_such_interface, iface}}

      desc ->
        type_name = Keyword.fetch!(meta, :name)
        type_params = Keyword.get(meta, :type_params, [])
        ctors = constructors(body)
        for_type = for_type_ast(type_name, type_params)

        with :ok <- check_derivable_shape(iface, type_name, ctors),
             :ok <- check_no_constrained_field(iface, type_name, type_params, body),
             {:ok, method_defs} <- method_defs(iface, desc, type_name, for_type, ctors, env) do
          impl_meta = [interface: Atom.to_string(iface), for: type_name, for_type: for_type, as: nil]
          {:ok, {:implementation, impl_meta, method_defs}}
        end
    end
  end

  def generate(iface, _container, _env), do: {:error, {:cannot_derive, iface}}

  # `constructors/1` recognises only `variant: true`-tagged entries, and falls through to
  # `[]` for anything else — a `rec`'s named-field list, say. With no constructors the
  # derived method's body is `match(x, [])`: a scrutinee and zero arms, unsatisfiable for
  # every input. `generate/3` is public and its contract says nothing about enum shapes, so
  # refuse here rather than emit a vacuous instance. Deriving is defined over variant types
  # in Haskell and Idris 2 alike; asking for anything else is an error at the derivation
  # site.
  defp check_derivable_shape(iface, type_name, []),
    do: {:error, {:cannot_derive_shape, iface, String.to_atom(type_name)}}

  defp check_derivable_shape(_iface, _type_name, _ctors), do: :ok

  # Deriving for a parameterized type works only while no constructor field has the bound
  # type parameter's own type. `type Box(a) = Empty | Full` and `type Tree(a) = Leaf |
  # Node(Tree(a), Tree(a))` are fine — a field of the recursive family resolves to the
  # in-progress instance. `type Lst(a) = Nil | Cons(a, Lst(a))` is not: the derived body
  # calls `eq(a0, b0)` on the `a`-typed field, `a` auto-generalizes to a RIGID type
  # variable, and the instance genuinely needs a `where Equatable(a)` dictionary the
  # derivation does not thread.
  #
  # Threading it would not be sufficient either: a concrete call `eq(l1, l2)` with
  # `l1 : Lst(Int)` must then solve `a := Int` from the argument's type to select
  # `Equatable(Int)`, and `Resolve.dict_arguments/5` matches only a parameter typed by the
  # bare head variable — it would resolve `Equatable(Lst)`, the in-progress instance
  # itself. That is a feature (dictionary passing under a type constructor), not a missing
  # keyword.
  #
  # Until it lands, refuse with a specific error rather than emit an instance whose body
  # cannot elaborate — the same discipline `generate(:Show, …)` already follows. It used to
  # emit one, and the author saw `{:no_instance, :Equatable, {:rigid, 0}}` pointing at
  # nothing they wrote. Silently resolving the wrong dictionary would be worse still.
  defp check_no_constrained_field(_iface, _type_name, [], _body), do: :ok

  defp check_no_constrained_field(iface, type_name, type_params, body) do
    if Enum.any?(field_types(body), &bare_type_param?(&1, type_params)) do
      {:error, {:deriving_needs_constraints, iface, String.to_atom(type_name)}}
    else
      :ok
    end
  end

  defp field_types(body) do
    Enum.flat_map(body, fn
      {:function_def, m, _} ->
        if Keyword.get(m, :variant, false), do: Keyword.get(m, :params, []), else: []

      _ ->
        []
    end)
  end

  defp bare_type_param?({:variable, _m, name}, type_params) when is_binary(name),
    do: name in type_params

  defp bare_type_param?(_ast, _type_params), do: false

  # -- constructor extraction -------------------------------------------------

  # `[{name_string, field_arity}]` in declaration order (the order that defines
  # the `Ord` constructor ranking). A field-bearing ctor is a `variant: true`
  # function_def; a nullary ctor is a `variant: true` variable.
  defp constructors(body) do
    Enum.flat_map(body, fn
      {:function_def, m, _} ->
        if Keyword.get(m, :variant, false),
          do: [{Keyword.fetch!(m, :name), length(Keyword.get(m, :params, []))}],
          else: []

      {:variable, m, name} ->
        if Keyword.get(m, :variant, false), do: [{name, 0}], else: []

      _ ->
        []
    end)
  end

  # -- method synthesis -------------------------------------------------------

  defp method_defs(iface, desc, type_name, for_type, ctors, env) do
    Enum.reduce_while(desc.method_order, {:ok, []}, fn m, {:ok, acc} ->
      case method_def(iface, desc, m, type_name, for_type, ctors, env) do
        {:ok, fn_def} -> {:cont, {:ok, acc ++ [fn_def]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # One mangled-nothing-yet `{:function_def, …}` for interface method `m`: its
  # signature is the interface method's signature with the head variable replaced
  # by this concrete type, its body is the structural comparator for `iface`.
  #
  # The body must scrutinise the parameters the SIGNATURE actually binds. It used to
  # hardcode `x` and `y` while the signature took its names from `info.params`, so any
  # `Equatable`/`Ord` interface not spelled with parameters literally named `x` and `y`
  # — `a1`/`a2`, `l`/`r`, `this`/`that` are all equally valid surface syntax — derived a
  # body referencing two free variables its own signature never bound. Every derived
  # instance under that interface failed to elaborate, fields or no fields. GHC's derived
  # `Eq`/`Ord` and Idris 2's `Deriving.Eq`/`Ord` cannot disagree this way: header and body
  # come from the same generation step. Now so do Cure's.
  defp method_def(iface, desc, m, _type_name, for_type, ctors, env) do
    info = Map.fetch!(desc.methods, m)

    params =
      Enum.map(info.params, fn {:param, pm, pname} ->
        {:param, Keyword.put(pm, :type, subst(Keyword.fetch!(pm, :type), desc.head_var, for_type)), pname}
      end)

    return_type = subst(info.return_type, desc.head_var, for_type)

    meta = [
      name: info.name,
      params: params,
      return_type: return_type,
      visibility: :public,
      arity: length(params)
    ]

    case Enum.map(params, fn {:param, _pm, pname} -> pname end) do
      [left, right] ->
        {:ok, {:function_def, meta, [body(iface, info.name, left, right, ctors, env)]}}

      other ->
        # `Equatable.eq` and `Ord.lt` are binary comparators. A structural body cannot be
        # synthesised for any other shape.
        {:error, {:cannot_derive_method, iface, m, {:expected_two_parameters, length(other)}}}
    end
  end

  # `Equatable.eq` — for each constructor, both sides must be that same
  # constructor and every field pair must be equal (nested-match conjunction);
  # any other pairing is `false`.
  defp body(:Equatable, eq_name, left, right, ctors, _env) do
    single = length(ctors) == 1

    arms =
      Enum.map(ctors, fn {cname, arity} ->
        inner =
          [arm(ctor_pat(cname, bs("b", arity)), eq_conj(eq_name, pairs(arity)))] ++
            if single, do: [], else: [arm(wildcard(), bool(false))]

        arm(ctor_pat(cname, bs("a", arity)), match(var(right), inner))
      end)

    match(var(left), arms)
  end

  # `Ord.lt` — `x < y` iff `x`'s constructor ranks before `y`'s; on the same
  # constructor, compare fields lexicographically (`lt` on the first differing
  # field, `eq` to advance). Cross-constructor arms fold to the constant decided
  # by declaration order.
  defp body(:Ord, lt_name, left, right, ctors, env) do
    eq_name = equatable_method(env)
    indexed = Enum.with_index(ctors)

    arms =
      Enum.map(indexed, fn {{cname, arity}, i} ->
        inner =
          Enum.map(indexed, fn {{cname2, arity2}, j} ->
            cond do
              j > i -> arm(ctor_pat(cname2, ignore(arity2)), bool(true))
              j < i -> arm(ctor_pat(cname2, ignore(arity2)), bool(false))
              true -> arm(ctor_pat(cname2, bs("r", arity2)), lt_lex(lt_name, eq_name, lex_pairs(arity)))
            end
          end)

        arm(ctor_pat(cname, bs("l", arity)), match(var(right), inner))
      end)

    match(var(left), arms)
  end

  # The equality method name to call from a derived `Ord` (its lexicographic
  # fold advances on equal fields). Read from the in-scope `Equatable` interface;
  # defaults to the canonical `"eq"` if none is registered.
  defp equatable_method(env) do
    case Env.get_interface(env, :Equatable) do
      %{method_order: [m | _], methods: methods} -> Map.fetch!(methods, m).name
      _ -> "eq"
    end
  end

  # Right-folded conjunction of `eq(l_i, r_i)` as nested `Bool` matches.
  defp eq_conj(_eq, []), do: bool(true)
  defp eq_conj(eq, [{l, r}]), do: call(eq, [var(l), var(r)])

  defp eq_conj(eq, [{l, r} | rest]) do
    match(call(eq, [var(l), var(r)]), [
      arm(bool(true), eq_conj(eq, rest)),
      arm(bool(false), bool(false))
    ])
  end

  # Lexicographic `<` over same-constructor fields: `lt` on the first field; if
  # equal, recurse; the empty (all-equal) tail is `false` (not strictly less).
  defp lt_lex(_lt, _eq, []), do: bool(false)
  defp lt_lex(lt, _eq, [{l, r}]), do: call(lt, [var(l), var(r)])

  defp lt_lex(lt, eq, [{l, r} | rest]) do
    match(call(lt, [var(l), var(r)]), [
      arm(bool(true), bool(true)),
      arm(
        bool(false),
        match(call(eq, [var(l), var(r)]), [
          arm(bool(true), lt_lex(lt, eq, rest)),
          arm(bool(false), bool(false))
        ])
      )
    ])
  end

  # -- field-name plumbing ----------------------------------------------------

  # `["<p>0", "<p>1", …]` — fresh binder names for a constructor's fields.
  defp bs(prefix, arity), do: for(i <- 0..(arity - 1)//1, do: "#{prefix}#{i}")

  # `arity` wildcards, for a constructor whose fields the arm ignores.
  defp ignore(arity), do: List.duplicate("_", arity)

  # Field-binder pairs `{"a_i", "b_i"}` for `Equatable`'s two matched scrutinees.
  defp pairs(arity), do: for(i <- 0..(arity - 1)//1, do: {"a#{i}", "b#{i}"})

  # Field-binder pairs `{"l_i", "r_i"}` for `Ord`'s two matched scrutinees.
  defp lex_pairs(arity), do: for(i <- 0..(arity - 1)//1, do: {"l#{i}", "r#{i}"})

  # -- AST constructors -------------------------------------------------------

  defp var(name), do: {:variable, [scope: :local], name}
  defp wildcard(), do: {:variable, [scope: :local], "_"}
  defp bool(b), do: {:literal, [subtype: :boolean], b}
  defp call(name, args), do: {:function_call, [name: name], args}
  defp match(scrut, arms), do: {:pattern_match, [], [scrut | arms]}
  defp arm(pattern, body), do: {:match_arm, [pattern: pattern], [body]}

  # A constructor pattern is always a `{:function_call, …}` — even nullary, whose
  # empty arg list distinguishes it from a bare-variable *catch-all* arm (which
  # `partition_arms` would treat as a default that swallows every constructor).
  defp ctor_pat(name, binders), do: {:function_call, [name: name], Enum.map(binders, &var/1)}

  # -- head substitution ------------------------------------------------------

  defp subst({:variable, _m, name}, head_var, for_type) when name == head_var, do: for_type
  defp subst({:variable, _m, _} = v, _head_var, _for_type), do: v

  defp subst({:function_call, m, args}, head_var, for_type),
    do: {:function_call, m, Enum.map(args, &subst(&1, head_var, for_type))}

  defp subst(other, _head_var, _for_type), do: other

  # -- for-type AST -----------------------------------------------------------

  defp for_type_ast(type_name, []), do: var(type_name)

  defp for_type_ast(type_name, params),
    do: {:function_call, [name: type_name], Enum.map(params, &var/1)}
end
