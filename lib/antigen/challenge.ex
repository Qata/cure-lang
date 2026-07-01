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

  @doc """
  Split a challenge into its non-`Term` scaffold metadata and its list of
  named `Term` pieces — the bridge the corpus serializes over (Task 5).
  Phase 2 adds `:def_group` / `:family` / `:forcing_pair` clauses (Tasks 9–11).
  """
  @spec to_pieces(t()) :: {map(), [{String.t(), Cure.Core.Term.t()}]}
  def to_pieces(%__MODULE__{kind: :stub, payload: %{term: t}}), do: {%{}, [{"term", t}]}

  @doc "Rebuild a challenge from a decoded record's fields, scaffold, and term pieces."
  @spec from_pieces(atom(), String.t(), atom(), integer() | nil, String.t() | nil, map(), [{String.t(), Cure.Core.Term.t()}]) :: t()
  def from_pieces(:stub, assay, label, seed, note, _scaffold, [{"term", t}]),
    do: new(kind: :stub, assay: assay, label: label, payload: %{term: t}, seed: seed, note: note)
end
