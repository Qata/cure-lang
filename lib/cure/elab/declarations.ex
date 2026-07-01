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

  alias Cure.Core.{Context, Env, Eval, Inductive, Kernel}
  alias Cure.Elab.Elaborator

  @ceiling 2

  @doc "Elaborate one declaration AST, returning the augmented signature."
  @spec elaborate(tuple(), Env.t()) :: {:ok, Env.t()} | {:error, term()}
  def elaborate({:function_def, meta, body}, env) do
    name = meta |> Keyword.fetch!(:name) |> String.to_atom()
    params = Keyword.get(meta, :params, [])
    return_expr = Keyword.fetch!(meta, :return_type)
    body_expr = single_body(body)

    with {:ok, telescope, quantities, scope} <- elaborate_param_telescope(params, env),
         ctx = build_context(env, telescope),
         {:ok, return_core} <- idx_to_core(return_expr, scope, nil, env),
         return_value = Eval.eval(return_core, Context.env(ctx)),
         {:ok, body_term, _body_type} <-
           Elaborator.elaborate_expr_typed(body_expr, scope, ctx, env),
         :ok <- Kernel.check(ctx, body_term, return_value) do
      lambda = wrap_binders(:lam, telescope, body_term)
      pi = wrap_binders(:pi, telescope, return_core)
      {:ok, Env.add_def(env, name, pi, lambda, quantities)}
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

  # Indexed (GADT) family: `indexed type SF(as: SVDesc, …) where <ctor sigs>`.
  # Each constructor signature is an `{:arrow_chain, [dom…, result]}`; the
  # implicit index-variable telescope is inferred from the signature (§5.2).
  def elaborate({:indexed_type, meta, ctor_sigs}, env) do
    name = meta |> Keyword.fetch!(:name) |> String.to_atom()
    index_params = Keyword.get(meta, :index_params, [])

    with {:ok, index_tele} <- elaborate_index_telescope(index_params, name, env),
         {:ok, ctors} <- elaborate_gadt_ctors(ctor_sigs, name, index_tele, env) do
      declare_indexed_at_min_level(env, name, index_tele, ctors, 0)
    end
  end

  def elaborate(other, _env), do: {:error, {:unsupported_declaration, elem(other, 0)}}

  # -- function elaboration ---------------------------------------------------

  defp single_body([expr]), do: expr
  defp single_body(expr), do: expr

  # Convert the parameter list into a Core telescope + {0,ω} quantities, with each
  # parameter type elaborated in the scope of the preceding parameters. Implicit
  # (`{name}`) parameters are erased. Returns the scope (names, most-recent first).
  defp elaborate_param_telescope(params, env) do
    params
    |> Enum.reduce_while({:ok, [], [], []}, fn {:param, pmeta, pname}, {:ok, tele, quants, scope} ->
      case Keyword.get(pmeta, :type) do
        nil ->
          {:halt, {:error, {:untyped_parameter, pname}}}

        type_expr ->
          case idx_to_core(type_expr, scope, nil, env) do
            {:ok, core} ->
              q = if Keyword.get(pmeta, :implicit), do: :erased, else: :present
              {:cont,
               {:ok, tele ++ [{String.to_atom(pname), core}], quants ++ [q], [pname | scope]}}

            {:error, _} = err ->
              {:halt, err}
          end
      end
    end)
    |> case do
      {:ok, tele, quants, scope} -> {:ok, tele, quants, scope}
      {:error, _} = err -> err
    end
  end

  defp build_context(env, telescope) do
    Enum.reduce(telescope, Context.empty(env), fn {_name, type_core}, ctx ->
      type_value = Eval.eval(type_core, Context.env(ctx))
      Context.extend(ctx, type_value)
    end)
  end

  defp wrap_binders(tag, telescope, inner) do
    Enum.reduce(Enum.reverse(telescope), inner, fn {_name, type}, acc -> {tag, type, acc} end)
  end

  # -- indexed families -------------------------------------------------------

  # The family's index telescope, converting each `i: T` in the scope of the
  # preceding index binders (most-recently-bound first).
  defp elaborate_index_telescope(params, fam, env) do
    params
    |> Enum.reduce_while({:ok, [], []}, fn {:param, pmeta, pname}, {:ok, tele, scope} ->
      case idx_to_core(Keyword.fetch!(pmeta, :type), scope, fam, env) do
        {:ok, core} ->
          {:cont, {:ok, tele ++ [{String.to_atom(pname), core}], [pname | scope]}}

        {:error, _} = err ->
          {:halt, err}
      end
    end)
    |> case do
      {:ok, tele, _scope} -> {:ok, tele}
      {:error, _} = err -> err
    end
  end

  defp elaborate_gadt_ctors(sigs, fam, index_tele, env) do
    Enum.reduce_while(sigs, {:ok, []}, fn sig, {:ok, acc} ->
      case elaborate_gadt_ctor(sig, fam, index_tele, env) do
        {:ok, ctor} -> {:cont, {:ok, acc ++ [ctor]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp elaborate_gadt_ctor({:gadt_ctor, cmeta, {:arrow_chain, atoms}}, fam, index_tele, env) do
    cname = cmeta |> Keyword.fetch!(:name) |> String.to_atom()
    {dom_exprs, result_expr} = split_last(atoms)

    with {:ok, index_exprs} <- family_index_args(result_expr, fam) do
      # Implicit index variables are inferred from every family application in
      # the signature (domains + the result), positionally typed by the family's
      # index telescope. Ordered by first appearance → the leading telescope.
      implicits = infer_implicits(dom_exprs ++ [result_expr], fam, index_tele, env)
      impl_names = Enum.map(implicits, &elem(&1, 0))

      case build_explicit_tele(dom_exprs, impl_names, fam, env) do
        {:ok, expl_tele, expl_names} ->
          full_scope = Enum.reverse(impl_names ++ expl_names)

          with {:ok, result_indices} <- map_idx_to_core(index_exprs, full_scope, fam, env) do
            impl_tele = Enum.map(implicits, fn {n, ty} -> {String.to_atom(n), ty} end)
            # Inferred index variables are erased (quantity 0); the explicit
            # arguments are runtime-relevant (quantity ω). See M8.3 / M9.
            quantities =
              List.duplicate(:erased, length(impl_tele)) ++
                List.duplicate(:present, length(expl_tele))

            {:ok, Inductive.ctor(cname, impl_tele ++ expl_tele, result_indices, quantities)}
          end

        {:error, _} = err ->
          err
      end
    end
  end

  defp split_last(list), do: {Enum.slice(list, 0..-2//1), List.last(list)}

  defp family_index_args({:function_call, fmeta, args}, fam) do
    if String.to_atom(Keyword.fetch!(fmeta, :name)) == fam,
      do: {:ok, args},
      else: {:error, {:result_type_not_family, fam}}
  end

  defp family_index_args({:variable, _, name}, fam) do
    if String.to_atom(name) == fam,
      do: {:ok, []},
      else: {:error, {:result_type_not_family, fam}}
  end

  defp family_index_args(other, _fam), do: {:error, {:bad_result_type, other}}

  # Explicit-argument telescope: convert each domain in the scope of all
  # preceding binders (implicits, then earlier explicits). Anonymous names.
  defp build_explicit_tele(dom_exprs, impl_names, fam, env) do
    dom_exprs
    |> Enum.with_index()
    |> Enum.reduce_while({:ok, [], Enum.reverse(impl_names), []}, fn {dom, i},
                                                                     {:ok, tele, scope, names} ->
      case idx_to_core(dom, scope, fam, env) do
        {:ok, core} ->
          argname = "_a#{i}"
          {:cont, {:ok, tele ++ [{String.to_atom(argname), core}], [argname | scope], names ++ [argname]}}

        {:error, _} = err ->
          {:halt, err}
      end
    end)
    |> case do
      {:ok, tele, _scope, names} -> {:ok, tele, names}
      {:error, _} = err -> err
    end
  end

  # -- implicit index-variable inference --------------------------------------

  defp infer_implicits(exprs, fam, index_tele, env) do
    {ordered, _seen} =
      Enum.reduce(exprs, {[], MapSet.new()}, fn e, acc ->
        collect_implicit_vars(e, fam, index_tele, env, acc)
      end)

    ordered
  end

  defp collect_implicit_vars({:function_call, fmeta, args}, fam, index_tele, env, acc) do
    name = String.to_atom(Keyword.fetch!(fmeta, :name))
    index_types = family_index_types(name, fam, index_tele, env)

    acc =
      if index_types do
        args
        |> Enum.with_index()
        |> Enum.reduce(acc, fn {arg, pos}, a ->
          case arg do
            {:variable, _, vname} -> maybe_add_implicit(a, vname, Enum.at(index_types, pos), fam, env)
            _ -> a
          end
        end)
      else
        acc
      end

    Enum.reduce(args, acc, fn a, ac -> collect_implicit_vars(a, fam, index_tele, env, ac) end)
  end

  defp collect_implicit_vars(_other, _fam, _index_tele, _env, acc), do: acc

  # The positional index types of family `name` (self or already registered).
  defp family_index_types(name, fam, index_tele, env) do
    cond do
      name == fam -> Enum.map(index_tele, &elem(&1, 1))
      Inductive.family?(env, name) -> Enum.map(Inductive.index_telescope(env, name) || [], &elem(&1, 1))
      true -> nil
    end
  end

  defp maybe_add_implicit({ordered, seen} = acc, vname, type, fam, env) do
    atom = String.to_atom(vname)

    cond do
      type == nil -> acc
      MapSet.member?(seen, vname) -> acc
      vname == "Type" -> acc
      atom == fam -> acc
      Inductive.get_ctor(env, atom) -> acc
      Inductive.family?(env, atom) -> acc
      Env.get_def(env, atom) -> acc
      true -> {ordered ++ [{vname, type}], MapSet.put(seen, vname)}
    end
  end

  # -- surface index/type expr → Core, with a de Bruijn scope -----------------

  defp idx_to_core({:variable, _meta, "Type"}, _scope, _fam, _env), do: {:ok, {:type, 0}}

  defp idx_to_core({:variable, _meta, name}, scope, _fam, env) do
    case Enum.find_index(scope, &(&1 == name)) do
      nil -> {:ok, resolve_index_name(name, env)}
      index -> {:ok, {:var, index}}
    end
  end

  defp idx_to_core({:function_call, fmeta, args}, scope, fam, env) do
    atom = fmeta |> Keyword.fetch!(:name) |> String.to_atom()

    with {:ok, core_args} <- map_idx_to_core(args, scope, fam, env) do
      cond do
        atom == fam or Inductive.family?(env, atom) ->
          {:ok, {:data, atom, [], core_args}}

        Inductive.get_ctor(env, atom) ->
          {:ok, {:ctor, atom, core_args}}

        true ->
          {:ok, Enum.reduce(core_args, {:global, atom}, fn a, acc -> {:app, acc, a} end)}
      end
    end
  end

  defp idx_to_core(other, _scope, _fam, _env), do: {:error, {:unsupported_index_expr, other}}

  defp resolve_index_name(name, env) do
    atom = String.to_atom(name)

    cond do
      Inductive.get_ctor(env, atom) -> {:ctor, atom, []}
      Inductive.family?(env, atom) -> {:data, atom, [], []}
      true -> {:global, atom}
    end
  end

  defp map_idx_to_core(exprs, scope, fam, env) do
    Enum.reduce_while(exprs, {:ok, []}, fn e, {:ok, acc} ->
      case idx_to_core(e, scope, fam, env) do
        {:ok, core} -> {:cont, {:ok, acc ++ [core]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp declare_indexed_at_min_level(env, name, index_tele, ctors, level) when level <= @ceiling do
    family = Inductive.family(name, [], index_tele, level)
    env2 = Inductive.declare(env, family, ctors)
    family2 = Inductive.get_family(env2, name)

    with :ok <- Kernel.check_family(env2, family2),
         :ok <- check_all_ctors(env2, family2, ctors),
         :ok <- Inductive.positive?(env2, family2) do
      {:ok, env2}
    else
      {:error, :universe_level} -> declare_indexed_at_min_level(env, name, index_tele, ctors, level + 1)
      {:error, _} = err -> err
    end
  end

  defp declare_indexed_at_min_level(_env, _name, _index_tele, _ctors, _level),
    do: {:error, :universe_ceiling}

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
