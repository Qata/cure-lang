defmodule Cure.Compiler.ModulePipeline.Result do
  @moduledoc false

  @enforce_keys [:request, :manifest]
  defstruct request: nil,
            manifest: nil,
            skeletons: %{},
            interfaces: %{},
            semantic_graph: nil,
            diagnostics: []

  @type t :: %__MODULE__{}
end
