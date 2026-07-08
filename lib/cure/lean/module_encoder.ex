defmodule Cure.Lean.ModuleEncoder do
  @moduledoc """
  JSON-able encoding of the Cure Core fragment admitted by the Lean bridge.

  This is intentionally narrower than `Cure.Core.Term`: Cure-specific
  convenience nodes must be rejected here until they have a principled Lean
  translation. The bridge should receive only the terms it is prepared to submit
  to Lean's own checker.
  """

  alias Cure.Core.{Env, Term}

  @format "cure-core-v1"
  @supported_nodes ~w(type var pi lam app global eq refl rewrite)

  @spec from_env(Env.t(), keyword()) :: {:ok, map()} | {:error, term()}
  def from_env(%Env{} = env, opts \\ []) do
    with {:ok, defs} <- encode_defs(env, Keyword.get(opts, :only_defs)) do
      {:ok,
       %{
         "format" => @format,
         "families" => [],
         "defs" => defs,
         "certified" => [],
         "builtins" => []
       }}
    end
  end

  defp encode_defs(%Env{defs: defs}, only_defs) do
    only =
      case only_defs do
        nil -> nil
        names -> MapSet.new(names)
      end

    defs
    |> Enum.filter(fn {name, _def} -> is_nil(only) or MapSet.member?(only, name) end)
    |> Enum.sort_by(fn {name, _def} -> Atom.to_string(name) end)
    |> Enum.reduce_while({:ok, []}, fn {_name, defn}, {:ok, acc} ->
      type = canonicalize_term(defn.type)
      body = canonicalize_term(defn.body)

      with :ok <- validate_term(type, [:def, defn.name, :type]),
           :ok <- validate_term(body, [:def, defn.name, :body]) do
        encoded = %{
          "name" => Atom.to_string(defn.name),
          "type" => Term.to_external(type),
          "body" => Term.to_external(body),
          "quantities" => encode_quantities(Map.get(defn, :quantities))
        }

        {:cont, {:ok, acc ++ [encoded]}}
      else
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp canonicalize_term({:data, :Equivalent, [type], [lhs, rhs]}) do
    {:eq, canonicalize_term(type), canonicalize_term(lhs), canonicalize_term(rhs)}
  end

  defp canonicalize_term({:ctor, :reflexive, [value]}), do: {:refl, canonicalize_term(value)}
  defp canonicalize_term({:type, _} = term), do: term
  defp canonicalize_term({:var, _} = term), do: term
  defp canonicalize_term({:global, _} = term), do: term
  defp canonicalize_term({:absurd} = term), do: term
  defp canonicalize_term({:int_type} = term), do: term
  defp canonicalize_term({:float_type} = term), do: term

  defp canonicalize_term(tuple) when is_tuple(tuple) do
    tuple
    |> Tuple.to_list()
    |> Enum.map(&canonicalize_term/1)
    |> List.to_tuple()
  end

  defp canonicalize_term(list) when is_list(list), do: Enum.map(list, &canonicalize_term/1)
  defp canonicalize_term(other), do: other

  defp validate_term({:type, level}, _path) when is_integer(level) and level >= 0, do: :ok
  defp validate_term({:var, index}, _path) when is_integer(index) and index >= 0, do: :ok

  defp validate_term({:pi, dom, cod}, path) do
    with :ok <- validate_term(dom, path ++ [:dom]),
         do: validate_term(cod, path ++ [:cod])
  end

  defp validate_term({:lam, dom, body}, path) do
    with :ok <- validate_term(dom, path ++ [:dom]),
         do: validate_term(body, path ++ [:body])
  end

  defp validate_term({:app, fun, arg}, path) do
    with :ok <- validate_term(fun, path ++ [:fun]),
         do: validate_term(arg, path ++ [:arg])
  end

  defp validate_term({:global, name}, path) when is_atom(name) do
    if safe_name?(name),
      do: :ok,
      else: {:error, {:lean_core_rejected, %{path: path, node: :global, reason: :unsafe_name, name: name}}}
  end

  defp validate_term({:eq, type, lhs, rhs}, path) do
    with :ok <- validate_term(type, path ++ [:type]),
         :ok <- validate_term(lhs, path ++ [:lhs]) do
      validate_term(rhs, path ++ [:rhs])
    end
  end

  defp validate_term({:refl, value}, path), do: validate_term(value, path ++ [:value])

  defp validate_term({:rewrite, proof, motive, body}, path) do
    with :ok <- validate_term(proof, path ++ [:proof]),
         :ok <- validate_term(motive, path ++ [:motive]) do
      validate_term(body, path ++ [:body])
    end
  end

  defp validate_term({tag, _, _}, path) when tag in [:sigma, :pair],
    do: unsupported(tag, path)

  defp validate_term({tag, _}, path) when tag in [:fst, :snd, :hole, :int_lit, :float_lit],
    do: unsupported(tag, path)

  defp validate_term({tag}, path) when tag in [:absurd, :int_type, :float_type],
    do: unsupported(tag, path)

  defp validate_term({tag, _, _, _}, path) when tag in [:data, :case],
    do: unsupported(tag, path)

  defp validate_term({tag, _, _}, path) when tag in [:ctor, :prim],
    do: unsupported(tag, path)

  defp validate_term(other, path),
    do: {:error, {:lean_core_rejected, %{path: path, node: node_name(other), reason: :unknown_core_node}}}

  defp unsupported(tag, path),
    do: {:error, {:lean_core_rejected, %{path: path, node: tag, reason: :unsupported_cure_core_node}}}

  defp node_name(tuple) when is_tuple(tuple), do: elem(tuple, 0)
  defp node_name(other), do: other

  defp safe_name?(name), do: Atom.to_string(name) =~ ~r/^[A-Za-z_][A-Za-z0-9_]*$/

  defp encode_quantities(nil), do: nil
  defp encode_quantities(quantities), do: Enum.map(quantities, &Atom.to_string/1)

  @doc false
  def supported_nodes, do: @supported_nodes
end
