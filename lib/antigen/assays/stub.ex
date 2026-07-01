defmodule Antigen.Assays.Stub do
  @moduledoc "Fake assay: {:global, :boom} is the planted infection (Phase 1 only)."
  alias Antigen.Challenge
  def run(%Challenge{payload: %{term: {:global, :boom}}}), do: {:violation, :boom}
  def run(%Challenge{}), do: :ok
end
