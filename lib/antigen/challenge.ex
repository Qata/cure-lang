defmodule Antigen.Challenge do
  @moduledoc "A generated challenge injected into the kernel (umbrella §3)."
  @enforce_keys [:kind, :assay, :label, :payload]
  defstruct [:kind, :assay, :label, :payload, :seed, :note]

  @type kind :: :stub | :def_group | :family | :forcing_pair
  @type label :: :terminating | :diverging | :positive | :negative | :none
  @type t :: %__MODULE__{
          kind: kind(),
          assay: String.t(),
          label: label(),
          payload: map(),
          seed: integer() | nil,
          note: String.t() | nil
        }

  @spec new(keyword()) :: t()
  def new(fields), do: struct!(__MODULE__, Keyword.merge([label: :none, seed: nil, note: nil], fields))

  @spec stub(Cure.Core.Term.t()) :: t()
  def stub(term), do: new(kind: :stub, assay: "stub", label: :none, payload: %{term: term})
end
