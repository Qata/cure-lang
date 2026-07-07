defmodule Cure.Kernel.Backend.ElixirCore do
  @moduledoc """
  Existing in-process dependent checker backend.
  """

  @behaviour Cure.Kernel.Backend

  @impl true
  def check_ast(ast, _opts) do
    Cure.Elab.Program.check_ast_elixir_core(ast)
  end
end
