defmodule Cure.Elab.Declarations do
  @moduledoc """
  Elaborate surface type declarations into `Cure.Core` inductive families
  (design spec §5; mirrors Idris `TTImp/ProcessData.idr`).

  Untrusted: it builds candidate `Inductive.family`/`Inductive.ctor` signatures
  and submits them to the kernel (`check_family`/`check_ctor` + strict
  positivity), so only well-formed families are registered.

  Handles the surface ADT form the parser produces today —
  `type X = A(T) | B | …` (`{:container, [container_type: :enum, …], variants}`).
  The family's universe level is inferred as the least level (0..ceiling) at
  which every constructor field type fits (the two-universe rule, §2): a field of
  type `Type` pushes the family to level 1. Indexed-GADT surface syntax
  (`indexed type … where`) is a separate parser extension (not yet in the
  grammar); the kernel-side indexed-family machinery it targets is complete (M3).
  """

  alias Cure.Core.{Context, Env, Inductive, Kernel, Quote}
  alias Cure.Elab.Elaborator

  @ceiling 2

  @doc "Elaborate one declaration AST, returning the augmented signature."
  @spec elaborate(tuple(), Env.t()) :: {:ok, Env.t()} | {:error, term()}
  def elaborate({:function_def, meta, _body} = ast, env) do
    name = meta |> Keyword.fetch!(:name) |> String.to_atom()

    with {:ok, lambda, type_value} <- Elaborator.elaborate(ast, env),
         :ok <- Kernel.check(Context.empty(env), lambda, type_value) do
      type_term = Quote.reify(type_value)
      {:ok, Env.add_def(env, name, type_term, lambda)}
    end
  end

  def elaborate({:container, meta, variants}, env) do
    case Keyword.get(meta, :container_type) do
      :enum ->
        name = meta |> Keyword.fetch!(:name) |> String.to_atom()

        case build_ctors(variants) do
          {:ok, ctors} -> declare_at_min_level(env, name, ctors, 0)
          {:error, _} = err -> err
        end

      other ->
        {:error, {:unsupported_container, other}}
    end
  end

  def elaborate(other, _env), do: {:error, {:unsupported_declaration, elem(other, 0)}}

  # -- constructors -----------------------------------------------------------

  defp build_ctors(variants) do
    Enum.reduce_while(variants, {:ok, []}, fn variant, {:ok, acc} ->
      case variant_to_ctor(variant) do
        {:ok, ctor} -> {:cont, {:ok, acc ++ [ctor]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # Nullary constructor: `None`
  defp variant_to_ctor({:variable, _meta, vname}),
    do: {:ok, Inductive.ctor(String.to_atom(vname), [], [])}

  # Constructor with fields: `Some(T)` / `SVCons(Sig, SVDesc)`
  defp variant_to_ctor({:function_def, meta, _body}) do
    vname = meta |> Keyword.fetch!(:name) |> String.to_atom()
    field_asts = Keyword.fetch!(meta, :params)

    case fields_to_telescope(field_asts) do
      {:ok, tele} -> {:ok, Inductive.ctor(vname, tele, [])}
      {:error, _} = err -> err
    end
  end

  defp variant_to_ctor(other), do: {:error, {:unsupported_variant, other}}

  defp fields_to_telescope(field_asts) do
    field_asts
    |> Enum.with_index()
    |> Enum.reduce_while({:ok, []}, fn {ast, i}, {:ok, acc} ->
      case type_to_core(ast) do
        {:ok, core} -> {:cont, {:ok, acc ++ [{:"f#{i}", core}]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # -- surface type expr → Core type term -------------------------------------

  defp type_to_core({:variable, _meta, "Type"}), do: {:ok, {:type, 0}}
  defp type_to_core({:variable, _meta, name}), do: {:ok, {:data, String.to_atom(name), [], []}}

  defp type_to_core({:function_call, meta, params}) do
    cond do
      Keyword.get(meta, :function_type) ->
        {:error, {:unsupported_field_type, :function}}

      true ->
        name = meta |> Keyword.fetch!(:name) |> String.to_atom()

        with {:ok, core_params} <- map_type_to_core(params) do
          # A saturated family application becomes a `:data` with index args.
          {:ok, {:data, name, [], core_params}}
        end
    end
  end

  defp type_to_core(other), do: {:error, {:unsupported_field_type, other}}

  defp map_type_to_core(asts) do
    Enum.reduce_while(asts, {:ok, []}, fn ast, {:ok, acc} ->
      case type_to_core(ast) do
        {:ok, core} -> {:cont, {:ok, acc ++ [core]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # -- declaration at the least well-formed universe level --------------------

  defp declare_at_min_level(env, name, ctors, level) when level <= @ceiling do
    family = Inductive.family(name, [], [], level)
    env2 = Inductive.declare(env, family, ctors)
    family2 = Inductive.get_family(env2, name)

    with :ok <- Kernel.check_family(env2, family2),
         :ok <- check_all_ctors(env2, family2, ctors),
         :ok <- Inductive.positive?(env2, family2) do
      {:ok, env2}
    else
      {:error, :universe_level} -> declare_at_min_level(env, name, ctors, level + 1)
      {:error, _} = err -> err
    end
  end

  defp declare_at_min_level(_env, _name, _ctors, _level), do: {:error, :universe_ceiling}

  defp check_all_ctors(env, family, ctors) do
    Enum.reduce_while(ctors, :ok, fn ctor, :ok ->
      case Kernel.check_ctor(env, family, ctor) do
        :ok -> {:cont, :ok}
        err -> {:halt, err}
      end
    end)
  end
end
