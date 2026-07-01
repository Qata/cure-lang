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

  def to_pieces(%__MODULE__{kind: :def_group, payload: %{defs: defs, focus: focus}}) do
    scaffold = %{
      "names" => Enum.map(defs, &Atom.to_string(&1.name)),
      "focus" => Enum.map(focus, &Atom.to_string/1)
    }

    pieces =
      Enum.flat_map(defs, fn d ->
        n = Atom.to_string(d.name)
        [{"type:" <> n, d.type}, {"body:" <> n, d.body}]
      end)

    {scaffold, pieces}
  end

  @doc "Rebuild a challenge from a decoded record's fields, scaffold, and term pieces."
  @spec from_pieces(atom(), String.t(), atom(), integer() | nil, String.t() | nil, map(), [{String.t(), Cure.Core.Term.t()}]) :: t()
  def from_pieces(:stub, assay, label, seed, note, _scaffold, [{"term", t}]),
    do: new(kind: :stub, assay: assay, label: label, payload: %{term: t}, seed: seed, note: note)

  def from_pieces(:def_group, assay, label, seed, note, scaffold, pieces) do
    pmap = Map.new(pieces)

    defs =
      Enum.map(scaffold["names"], fn n ->
        %{
          name: String.to_existing_atom(n),
          type: Map.fetch!(pmap, "type:" <> n),
          body: Map.fetch!(pmap, "body:" <> n)
        }
      end)

    focus = Enum.map(scaffold["focus"], &String.to_existing_atom/1)
    new(kind: :def_group, assay: assay, label: label, payload: %{defs: defs, focus: focus}, seed: seed, note: note)
  end
end
