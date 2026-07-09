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

  alias Cure.Core.Env
  alias Cure.Elab.{Coherence, Declarations}

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
    head = meta |> Keyword.fetch!(:for) |> String.to_atom()
    for_type = Keyword.fetch!(meta, :for_type)
    as_name = Keyword.get(meta, :as)

    case Env.get_interface(env, iface) do
      nil ->
        {:error, {:no_such_interface, iface}}

      desc ->
        with {:ok, method_map, mangled_fns} <-
               build_methods(desc, iface, head, for_type, body),
             ref = %{iface: iface, head: head, methods: method_map, as: as_name},
             {:ok, env1} <- register_instance(env, iface, head, as_name, ref),
             {:ok, env2} <- register_signatures(mangled_fns, env1) do
          {:ok, env2, mangled_fns}
        end
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

      case method_def(desc, method, for_type, body) do
        {:ok, fn_decl} ->
          renamed = rename_fn(fn_decl, mangled)
          {:cont, {:ok, Map.put(mm, method, mangled), fns ++ [renamed]}}

        :missing ->
          {:halt, {:error, {:missing_method, iface, method}}}
      end
    end)
  end

  # An instance clause for `method`, or the interface default specialised to the
  # instance's head type, or `:missing`.
  defp method_def(desc, method, for_type, body) do
    mstr = Atom.to_string(method)

    case Enum.find(body, &function_def_named?(&1, mstr)) do
      {:function_def, _m, _b} = fd ->
        {:ok, fd}

      nil ->
        case Map.fetch(desc.defaults, mstr) do
          {:ok, default_body} -> {:ok, default_fn_def(desc, method, default_body, for_type)}
          :error -> :missing
        end
    end
  end

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

  # Replace every `{:variable, _, head_var}` in a type AST with `for_type`.
  defp subst_head({:variable, _m, name}, head_var, for_type) when name == head_var, do: for_type
  defp subst_head({:variable, _m, _} = v, _head_var, _for_type), do: v

  defp subst_head({:function_call, m, args}, head_var, for_type),
    do: {:function_call, m, Enum.map(args, &subst_head(&1, head_var, for_type))}

  defp subst_head(other, _head_var, _for_type), do: other

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

  defp register_signatures(fn_decls, env) do
    Enum.reduce_while(fn_decls, {:ok, env}, fn fd, {:ok, acc} ->
      case Declarations.register_signature(fd, acc) do
        {:ok, acc2} -> {:cont, {:ok, acc2}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end
end
