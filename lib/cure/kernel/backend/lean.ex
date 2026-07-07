defmodule Cure.Kernel.Backend.Lean do
  @moduledoc """
  Lean-backed dependent checker backend.

  This path elaborates the currently admitted dependent subset without using
  `Cure.Core.Kernel` as the final admission gate, encodes the resulting Core
  fragment, and asks the Lean bridge to check it. Cure-specific convenience
  nodes are rejected by the encoder until they have a principled Lean
  translation.
  """

  @behaviour Cure.Kernel.Backend

  @impl true
  def check_ast(ast, opts) do
    with {:ok, env} <- Cure.Elab.Program.check_ast_for_lean_backend(ast),
         {:ok, payload} <-
           Cure.Lean.ModuleEncoder.from_env(env, only_defs: Cure.Elab.Program.local_def_names(ast)),
         {:ok, _response} <- Cure.Lean.Bridge.check_module(payload, opts) do
      {:ok, env}
    end
  end
end
