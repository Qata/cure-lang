defmodule Cure.Compiler.ModulePipeline.Emission do
  @moduledoc """
  BEAM bytecode for the modules a checked run holds.

  A checked run already owns everything emission needs: `body_envs` is the
  elaborated Core env per module, and the module's AST names which definitions
  that module OWNS. Emission is therefore a projection of a finished check, not
  a second compile — nothing here re-elaborates, re-resolves, or re-reads
  source, so a beam cannot disagree with the interface published beside it.

  Modules are emitted in a deterministic order and the first failure stops the
  run, carrying the module it belongs to. A run that cannot emit one of its own
  modules has not produced a generation, so failing here means nothing is
  published at all.
  """

  alias Cure.Compiler.BeamWriter
  alias Cure.Core.Env
  alias Cure.Elab.{Emit, Program}

  @doc """
  Bytecode for every module in `asts`, keyed by the BEAM module atom.

  `body_envs` must hold a checked env for each identity in `asts`; a missing
  one is a broken run rather than a module with nothing to emit, so it is an
  error and not an empty beam.
  """
  @spec run(%{term() => term()}, %{term() => Env.t()}) ::
          {:ok, %{module() => binary()}} | {:error, term()}
  def run(asts, body_envs) when is_map(asts) and is_map(body_envs) do
    asts
    |> Enum.sort_by(fn {identity, _ast} -> identity end)
    |> Enum.reduce_while({:ok, %{}}, fn {identity, ast}, {:ok, emitted} ->
      case emit_module(identity, ast, body_envs) do
        {:ok, module, binary} -> {:cont, {:ok, Map.put(emitted, module, binary)}}
        {:error, _reason} = error -> {:halt, error}
      end
    end)
  end

  defp emit_module({_package, module_name} = identity, ast, body_envs) do
    case Map.fetch(body_envs, identity) do
      {:ok, env} ->
        case emit(ast, env) do
          {:ok, _module, _binary} = ok -> ok
          {:error, reason} -> {:error, {:beam_emission_failed, module_name, reason}}
        end

      :error ->
        {:error, {:beam_emission_env_missing, module_name}}
    end
  end

  defp emit(ast, env) do
    module = Program.module_atom(ast)

    case Emit.compile_forms(env, module, Program.local_defs(ast, env)) do
      {:ok, forms} -> assemble(module, forms)
      {:error, reason} -> {:error, reason}
    end
  end

  # `:compile.forms/2` derives the module name from the forms themselves. It
  # agreeing with the identity the manifest assigned is what makes a published
  # beam addressable by module atom, so it is checked rather than assumed.
  defp assemble(module, forms) do
    case BeamWriter.compile_forms(forms) do
      {:ok, ^module, binary, _warnings} -> {:ok, module, binary}
      {:ok, other, _binary, _warnings} -> {:error, {:beam_module_mismatch, module, other}}
      {:error, errors, warnings} -> {:error, {:beam_compilation_failed, errors, warnings}}
    end
  end
end
