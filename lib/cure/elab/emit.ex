defmodule Cure.Elab.Emit do
  @moduledoc """
  BEAM emission for the erased Core (design spec §8, M9.3).

  The final leg of the pipeline: an elaborated, totality-certified definition is
  erased (its `:erased` index arguments dropped, M9.1) and lowered to Erlang
  abstract forms, which `:compile.forms/2` turns into real bytecode.

  The supported runtime fragment is the non-dependent residue of a checked
  program — exactly what survives erasure:

    * a nullary constructor becomes its atom (`Causal` → `:Causal`, `prim` → `:prim`);
    * an n-ary constructor becomes a tagged tuple of its *present* fields
      (`seq(l, r)` → `{:seq, L, R}`);
    * a dependent `case` becomes an Erlang `case` whose patterns bind only the
      present fields; erased fields carry no runtime slot;
    * a Sigma pair becomes a 2-tuple, `fst`/`snd` become `element/2`.

  A definition whose erased body still contains a hole is refused (§6 negative #5):
  it typechecks but must not be emitted.
  """

  alias Cure.Compiler.BeamWriter
  alias Cure.Core.{Env, Inductive}
  alias Cure.Elab.Erase

  @line 1

  @doc """
  Emit `functions` from `env` as a module named `module`, compile, and load it.

  Returns `{:ok, module}` on success, `{:error, {:unfilled_hole, name}}` when a
  requested function still contains a hole, or `{:error, reason}` if the Erlang
  compiler rejects the forms.
  """
  @spec compile_and_load(Env.t(), keyword()) :: {:ok, module()} | {:error, term()}
  def compile_and_load(%Env{} = env, opts) do
    module = Keyword.fetch!(opts, :module)
    names = Keyword.fetch!(opts, :functions)

    with :ok <- reject_holes(env, names) do
      BeamWriter.compile_and_load(module_forms(env, module, names))
    end
  end

  @doc """
  Erlang abstract forms for *every* definition in `env`, as module `module`.

  This is the codegen entry the real compiler pipeline calls for a dependent
  module. Refuses the whole module if any definition still contains a hole
  (§6 negative #5) and reports a definition the runtime fragment cannot express
  rather than crashing the pipeline.
  """
  @spec compile_forms(Env.t(), module()) :: {:ok, [tuple()]} | {:error, term()}
  def compile_forms(%Env{defs: defs} = env, module) do
    names = Map.keys(defs)

    compile_forms(env, module, names)
  end

  @doc """
  Erlang abstract forms for a selected set of definitions in `env`.

  Imported definitions may be present in the Core env so conversion can unfold
  them, but an importing module should emit only its own local definitions.
  """
  @spec compile_forms(Env.t(), module(), [atom()]) :: {:ok, [tuple()]} | {:error, term()}
  def compile_forms(%Env{} = env, module, names) do
    with :ok <- reject_holes(env, names) do
      try do
        {:ok, module_forms(env, module, names)}
      rescue
        e in ArgumentError -> {:error, {:cannot_emit, Exception.message(e)}}
      end
    end
  end

  @doc "The Erlang abstract forms for `functions` in `env`, as module `module`."
  @spec module_forms(Env.t(), module(), [atom()]) :: [tuple()]
  def module_forms(%Env{} = env, module, names) do
    fn_forms = Enum.map(names, &function_form(env, &1))
    exports = Enum.map(fn_forms, fn {:function, _l, name, arity, _cls} -> {name, arity} end)

    [
      {:attribute, @line, :module, module},
      {:attribute, @line, :export, exports}
      | fn_forms
    ]
  end

  # -- functions --------------------------------------------------------------

  defp reject_holes(env, names) do
    Enum.reduce_while(names, :ok, fn name, :ok ->
      body = Erase.erase(env, def_body(env, name))
      if Erase.has_hole?(body), do: {:halt, {:error, {:unfilled_hole, name}}}, else: {:cont, :ok}
    end)
  end

  defp def_body(env, name) do
    case Env.get_def(env, name) do
      %{body: body} -> body
      nil -> raise ArgumentError, "no such definition: #{inspect(name)}"
    end
  end

  defp function_form(env, name) do
    %{body: body, quantities: quantities} = Env.get_def(env, name)
    qs = quantities || []
    {param_names, inner} = peel_params(Erase.erase(env, body), qs, 0, [])

    ctx = Enum.reverse(param_names)
    params = for {n, :present} <- Enum.zip(param_names, qs), do: {:var, @line, n}
    clause = {:clause, @line, params, [], [lower(env, inner, ctx)]}
    {:function, @line, name, length(params), [clause]}
  end

  # Peel one binder per declared parameter, naming present binders `V<pos>` (bound
  # as Erlang params) and erased binders `_e<pos>` (dead after erasure).
  defp peel_params(term, [], _pos, acc), do: {Enum.reverse(acc), term}

  defp peel_params({:lam, _dom, body}, [q | qs], pos, acc) do
    name = if q == :present, do: :"V#{pos}", else: :"_e#{pos}"
    peel_params(body, qs, pos + 1, [name | acc])
  end

  defp peel_params(term, _qs, _pos, acc), do: {Enum.reverse(acc), term}

  # -- expressions ------------------------------------------------------------

  # `ctx` lists the in-scope Erlang variable atoms with de Bruijn index 0 first.
  defp lower(_env, {:var, k}, ctx) do
    case Enum.at(ctx, k) do
      nil -> raise ArgumentError, "de Bruijn index #{k} out of range"
      name -> {:var, @line, name}
    end
  end

  defp lower(env, {:ctor, name, args}, ctx) do
    case Enum.map(args, &lower(env, &1, ctx)) do
      [] -> {:atom, @line, name}
      forms -> {:tuple, @line, [{:atom, @line, name} | forms]}
    end
  end

  defp lower(env, {:case, scrut, _motive, branches}, ctx) do
    {:case, @line, lower(env, scrut, ctx), Enum.map(branches, &branch_clause(env, &1, ctx))}
  end

  defp lower(env, {:pair, a, b}, ctx) do
    {:tuple, @line, [lower(env, a, ctx), lower(env, b, ctx)]}
  end

  defp lower(env, {:fst, p}, ctx), do: element(1, lower(env, p, ctx))
  defp lower(env, {:snd, p}, ctx), do: element(2, lower(env, p, ctx))

  # A first-class lambda erases to a curried 1-argument BEAM fun; its parameter
  # takes de Bruijn index 0 in the body's frame.
  defp lower(env, {:lam, _dom, body}, ctx) do
    var = :"Fn#{length(ctx)}"
    clause = {:clause, @line, [{:var, @line, var}], [], [lower(env, body, [var | ctx])]}
    {:fun, @line, {:clauses, [clause]}}
  end

  defp lower(env, {:app, _, _} = app, ctx) do
    {head, args} = spine(app, [])

    case head do
      # A saturated named function is one multi-argument BEAM call.
      {:global, name} ->
        {:call, @line, {:atom, @line, name}, Enum.map(args, &lower(env, &1, ctx))}

      # Applying a closure value (a lambda or a function-typed binder) is curried:
      # apply one argument at a time to the BEAM fun.
      _ ->
        Enum.reduce(args, lower(env, head, ctx), fn arg, acc ->
          {:call, @line, acc, [lower(env, arg, ctx)]}
        end)
    end
  end

  # A bare global: a nullary definition is called (`name()`); a definition with
  # present parameters used as a *value* (passed to a higher-order function)
  # becomes a function reference `fun name/arity`.
  defp lower(env, {:global, name}, _ctx) do
    case present_arity(env, name) do
      0 -> {:call, @line, {:atom, @line, name}, []}
      n -> {:fun, @line, {:function, name, n}}
    end
  end

  defp present_arity(env, name) do
    case Env.get_def(env, name) do
      %{quantities: qs} when is_list(qs) -> Enum.count(qs, &(&1 == :present))
      _ -> 0
    end
  end

  # A discharged (impossible) case branch. Never executed at runtime; emit an
  # unreachable stub so codegen doesn't hit the raising catch-all (spec §5).
  defp lower(_env, {:absurd}, _ctx),
    do: {:call, @line, {:atom, @line, :error}, [{:atom, @line, :absurd}]}

  defp lower(_env, term, _ctx), do: raise(ArgumentError, "cannot emit #{inspect(term)}")

  defp element(n, tuple_form) do
    {:call, @line, {:atom, @line, :element}, [{:integer, @line, n}, tuple_form]}
  end

  defp spine({:app, f, x}, acc), do: spine(f, [x | acc])
  defp spine(head, acc), do: {head, acc}

  # A dependent-`case` branch. The scrutinee at runtime is the *erased* value, so
  # the pattern binds only present fields; the body's de Bruijn frame still counts
  # every field (index 0 = last field), so erased fields keep a (dead) context slot.
  defp branch_clause(env, {cname, arity, body}, ctx) do
    quantities = Inductive.ctor_quantities(env, cname) || List.duplicate(:present, arity)
    base = length(ctx)

    fields =
      for i <- indices(arity) do
        q = Enum.at(quantities, i, :present)
        if q == :present, do: {:present, :"V#{base + i}"}, else: {:erased, :"_f#{base + i}"}
      end

    present = for {:present, n} <- fields, do: {:var, @line, n}

    pattern =
      case present do
        [] -> {:atom, @line, cname}
        _ -> {:tuple, @line, [{:atom, @line, cname} | present]}
      end

    field_names = Enum.map(fields, fn {_q, n} -> n end)
    new_ctx = Enum.reverse(field_names) ++ ctx
    {:clause, @line, [pattern], [], [lower(env, body, new_ctx)]}
  end

  defp indices(0), do: []
  defp indices(arity), do: Enum.to_list(0..(arity - 1))
end
