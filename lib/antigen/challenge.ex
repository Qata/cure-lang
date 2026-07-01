defmodule Antigen.Challenge do
  @moduledoc "A generated challenge injected into the kernel (umbrella §3)."
  alias Cure.Core.Inductive
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

  def to_pieces(%__MODULE__{kind: :family, payload: %{family: fam, ctors: ctors}}) do
    param_pieces = fam.params |> Enum.with_index() |> Enum.map(fn {{_n, t}, i} -> {"fam_param:#{i}", t} end)
    index_pieces = fam.indices |> Enum.with_index() |> Enum.map(fn {{_n, t}, i} -> {"fam_index:#{i}", t} end)

    ctor_pieces =
      ctors
      |> Enum.with_index()
      |> Enum.flat_map(fn {ct, j} ->
        arg_pieces = ct.args |> Enum.with_index() |> Enum.map(fn {{_n, t}, k} -> {"ctor:#{j}:arg:#{k}", t} end)
        ridx_pieces = ct.result_indices |> Enum.with_index() |> Enum.map(fn {t, k} -> {"ctor:#{j}:ridx:#{k}", t} end)
        arg_pieces ++ ridx_pieces
      end)

    ctor_scaffold =
      Enum.map(ctors, fn ct ->
        %{
          "name" => Atom.to_string(ct.name),
          "arg_names" => Enum.map(ct.args, fn {n, _t} -> Atom.to_string(n) end),
          "ridx_count" => length(ct.result_indices),
          "quantities" => Enum.map(ct.quantities, &Atom.to_string/1)
        }
      end)

    scaffold = %{
      "fam_name" => Atom.to_string(fam.name),
      "fam_level" => fam.level,
      "fam_param_names" => Enum.map(fam.params, fn {n, _t} -> Atom.to_string(n) end),
      "fam_index_names" => Enum.map(fam.indices, fn {n, _t} -> Atom.to_string(n) end),
      "ctors" => ctor_scaffold
    }

    {scaffold, param_pieces ++ index_pieces ++ ctor_pieces}
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

  def from_pieces(:family, assay, label, seed, note, scaffold, pieces) do
    pmap = Map.new(pieces)
    params = rebuild_telescope(scaffold["fam_param_names"], "fam_param", pmap)
    indices = rebuild_telescope(scaffold["fam_index_names"], "fam_index", pmap)
    fam = Inductive.family(String.to_existing_atom(scaffold["fam_name"]), params, indices, scaffold["fam_level"])

    ctors =
      scaffold["ctors"]
      |> Enum.with_index()
      |> Enum.map(fn {cs, j} ->
        args =
          cs["arg_names"]
          |> Enum.with_index()
          |> Enum.map(fn {n, k} -> {String.to_existing_atom(n), Map.fetch!(pmap, "ctor:#{j}:arg:#{k}")} end)

        ridx = for k <- 0..(cs["ridx_count"] - 1)//1, do: Map.fetch!(pmap, "ctor:#{j}:ridx:#{k}")
        quantities = Enum.map(cs["quantities"], &String.to_existing_atom/1)
        Inductive.ctor(String.to_existing_atom(cs["name"]), args, ridx, quantities)
      end)

    new(kind: :family, assay: assay, label: label, payload: %{family: fam, ctors: ctors}, seed: seed, note: note)
  end

  defp rebuild_telescope(names, prefix, pmap) do
    names
    |> Enum.with_index()
    |> Enum.map(fn {n, i} -> {String.to_existing_atom(n), Map.fetch!(pmap, "#{prefix}:#{i}")} end)
  end
end
