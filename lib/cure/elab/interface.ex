defmodule Cure.Elab.Interface do
  @moduledoc """
  Elaborate a compile-time `interface` (typeclass) declaration.

  An interface `interface Eqs(a)` with methods `eqs : a -> a -> Bool` is the
  successor to the runtime `proto`. Conceptually it denotes a dependent record
  type former `Eqs : Π(h : K). Type` — `Eqs(h) ≙ record{ eqs : h -> h -> Bool }`
  — whose head kind `K` is inferred from how the head variable is used across the
  method signatures (`:type` when it appears bare, `{:arrow, :type, :type}` when
  it appears applied, e.g. `Functor`'s `f(a)`).

  This module registers the *descriptor* (elaborator-level metadata: head var,
  head kind, per-method surface signatures, default bodies) in the env under the
  interface's name atom. The Core record type former and the dictionary values
  that inhabit it are built by `Cure.Elab.Implementation` (Task 3) and consumed by
  `Cure.Elab.Resolve` (Tasks 4/5) — an interface with no implementations needs no
  Core type, so building the former lazily keeps a bare `interface` cheap and
  side-steps method-level generics until an instance actually forces the issue.
  """

  alias Cure.Core.Env
  alias Cure.MetaAST.Metadata

  @doc """
  Register the interface descriptor for `{:interface, meta, methods}` in `env`.
  Returns `{:error, {:inconsistent_head_kind, name}}` if the head variable is
  used both bare and applied across the method signatures.
  """
  @spec elaborate(tuple(), Env.t()) :: {:ok, Env.t()} | {:error, term()}
  def elaborate({:interface, meta, methods}, env) do
    name = Keyword.fetch!(meta, :name)
    name_atom = String.to_atom(name)
    head_var = meta |> Keyword.get(:params, []) |> List.first()
    defaults = Keyword.get(meta, :defaults, %{})
    # Superinterface names from the `requires` clause, normalized to atoms. An
    # interface with no `requires` clause gets `super: []`, so the obligation
    # check at instance registration is a no-op for it.
    super_interfaces =
      meta |> Keyword.get(:requires, []) |> Enum.map(&String.to_atom/1)

    with {:ok, head_kind} <- infer_head_kind(name_atom, head_var, methods) do
      desc =
        Metadata.strip_diagnostics(%{
          name: name_atom,
          head_var: head_var,
          head_kind: head_kind,
          methods: build_method_map(methods),
          method_order: method_order(methods),
          defaults: defaults,
          super: super_interfaces
        })

      with :ok <- check_method_names_free(desc, env),
           {:ok, env1} <- declare_dictionary_former(desc, env) do
        {:ok, Env.put_interface(env1, name_atom, desc)}
      end
    end
  end

  # `for_method/2` is the SOLE lookup `Resolve.method_call` uses to find the interface owning an
  # unqualified call like `size(x)`, and it is `Enum.find_value/2` over the whole `env.interfaces`
  # map — the FIRST interface, in unspecified map-iteration order, whose method table holds the
  # name. Nothing anywhere checked whether a method name is unique across in-scope interfaces, so
  # two interfaces both declaring `size` left every unqualified call bound to whichever descriptor
  # the map happened to yield first, with no diagnostic at the declaration or the call.
  #
  # Idris2 and Lean 4 both require disambiguation when two in-scope interfaces/classes declare a
  # same-named method: an unqualified reference that cannot be disambiguated is a compile error,
  # never an arbitrary pick. Cure has no qualified method-call syntax, so the ambiguity can only
  # be reported where it is created.
  defp check_method_names_free(desc, %Env{interfaces: ifaces}) do
    desc.method_order
    |> Enum.find_value(fn m ->
      Enum.find_value(ifaces, fn {other, other_desc} ->
        if other != desc.name and Map.has_key?(other_desc.methods, m), do: {m, other}
      end)
    end)
    |> case do
      nil -> :ok
      {method, other} -> {:error, {:ambiguous_method, method, Enum.sort([desc.name, other])}}
    end
  end

  # The interface's dictionary type former: a single-constructor record family
  # `Iface(head) ≙ Iface{ method : field-type, … }`. For a kind-`Type` interface
  # this is a plain parameterized record; the higher-kinded former (a `f : Type ->
  # Type` parameter) is built by the HKT resolution step and skipped here.
  defp declare_dictionary_former(%{head_kind: :type} = desc, env) do
    fields =
      Enum.map(desc.method_order, fn m ->
        info = Map.fetch!(desc.methods, m)
        {:param, [type: info.type_ast], info.name}
      end)

    Cure.Elab.Declarations.declare_record(desc.name, [desc.head_var], fields, env)
  end

  defp declare_dictionary_former(_desc, env), do: {:ok, env}

  @doc "The interface descriptor whose method set contains `method`, or nil."
  @spec for_method(Env.t(), atom()) :: map() | nil
  def for_method(%Env{interfaces: ifaces}, method) do
    Enum.find_value(ifaces, fn {_name, desc} ->
      if Map.has_key?(desc.methods, method), do: desc, else: nil
    end)
  end

  # -- descriptor construction ------------------------------------------------

  # method_map: %{method_atom => %{name, params, return_type, type_ast}} where
  # `type_ast` is the synthesized surface function-type `T1 -> ... -> Tn -> R`
  # (the interface record's field type for this method).
  defp build_method_map(methods) do
    methods
    |> Enum.flat_map(fn
      {:function_def, m, _body} ->
        mname = Keyword.fetch!(m, :name)
        params = Keyword.get(m, :params, [])
        return_type = Keyword.get(m, :return_type)

        [
          {String.to_atom(mname),
           %{
             name: mname,
             params: params,
             return_type: return_type,
             type_ast: method_type_ast(params, return_type)
           }}
        ]

      _ ->
        []
    end)
    |> Map.new()
  end

  defp method_order(methods) do
    methods
    |> Enum.flat_map(fn
      {:function_def, m, _body} -> [String.to_atom(Keyword.fetch!(m, :name))]
      _ -> []
    end)
  end

  # Fold a method's parameter types + return type into a surface function-type
  # AST `T1 -> ... -> Tn -> R`, the shape `idx_to_core` lowers to a Pi chain
  # (`{:function_call, [function_type: true], [doms..., result]}`).
  defp method_type_ast(params, return_type) do
    dom_asts = Enum.map(params, fn {:param, pm, _pname} -> Keyword.fetch!(pm, :type) end)
    {:function_call, [function_type: true], dom_asts ++ [return_type]}
  end

  # -- head-kind inference ----------------------------------------------------

  # Scan every method signature (param types + return type) for uses of the head
  # variable. A bare occurrence (`a`) contributes `:type`; an applied occurrence
  # (`a(...)`, i.e. `f(x)`) contributes `:arrow`. Both present ⇒ inconsistent.
  defp infer_head_kind(_name, nil, _methods), do: {:ok, :type}

  defp infer_head_kind(name, head_var, methods) do
    uses =
      methods
      |> Enum.flat_map(&method_type_asts/1)
      |> Enum.reduce(MapSet.new(), fn ast, acc -> collect_head_uses(ast, head_var, acc) end)

    cond do
      MapSet.member?(uses, :bare) and MapSet.member?(uses, :applied) ->
        {:error, {:inconsistent_head_kind, name}}

      MapSet.member?(uses, :applied) ->
        {:ok, {:arrow, :type, :type}}

      true ->
        {:ok, :type}
    end
  end

  defp method_type_asts({:function_def, m, _body}) do
    param_types = m |> Keyword.get(:params, []) |> Enum.map(fn {:param, pm, _} -> Keyword.fetch!(pm, :type) end)

    case Keyword.get(m, :return_type) do
      nil -> param_types
      rt -> param_types ++ [rt]
    end
  end

  defp method_type_asts(_), do: []

  # Walk a type AST accumulating {:bare, :applied} head-var uses.
  defp collect_head_uses({:variable, _meta, name}, head_var, acc) do
    if name == head_var, do: MapSet.put(acc, :bare), else: acc
  end

  defp collect_head_uses({:function_call, fmeta, args}, head_var, acc) do
    acc =
      cond do
        Keyword.get(fmeta, :function_type) -> acc
        Keyword.get(fmeta, :name) == head_var -> MapSet.put(acc, :applied)
        true -> acc
      end

    Enum.reduce(args, acc, fn a, inner -> collect_head_uses(a, head_var, inner) end)
  end

  defp collect_head_uses(_other, _head_var, acc), do: acc
end
