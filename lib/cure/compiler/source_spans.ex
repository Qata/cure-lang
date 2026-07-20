defmodule Cure.Compiler.SourceSpans do
  @moduledoc "Semantic metadata helpers retained for parser compatibility."

  alias Cure.MetaAST.Metadata

  @doc "Remove source/provenance metadata before a semantic comparison."
  @spec strip_diagnostic_meta(term()) :: term()
  def strip_diagnostic_meta(ast), do: Metadata.strip_diagnostics(ast)
end
