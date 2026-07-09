defmodule Antigen.CoverManifest do
  @moduledoc """
  Shape-coverage manifest for the Antigen assays (design
  `docs/superpowers/specs/2026-07-10-antigen-coverage-manifest-design.md`).

  Kernel *line* coverage (`Antigen.Cover`) and the plateauing dedup key
  (`Antigen.Coverage`) both went green while four soundness findings were live,
  because the vulnerable clause was executed / the shape was collapsed into an
  existing cell. This manifest tracks something finer: each participating generator
  declares the set of soundness-relevant *shape cells* it is responsible for
  producing (`cover_cells/0 :: [{assay_id, cell}]`), and stamps each challenge with a
  `cover_tag`. The coverage-manifest gate samples every participant and fails when a
  declared cell is never produced — the level at which the four findings would have
  been caught (each was a declared-cell-with-zero-hits waiting to happen).

  A generator is a **participant** iff it declares `cover_cells/0` and exposes a
  sampleable `gen/0`. Cell-completeness is checked only for participants; assay-level
  firing is checked for every registered assay by the gate (`Antigen.Runner.registered_assays/0`).
  """
  alias Antigen.Backend.StreamData, as: B
  alias Antigen.Generators.{Positivity, Totality, BranchUnify, Universes}

  # Generator modules under the shape-coverage manifest — the four assays whose gap
  # the second-pass findings exposed. Expand incrementally; do NOT retrofit every
  # assay at once (a fake-full manifest is worse than an honest partial one).
  @participants [Positivity, Totality, BranchUnify, Universes]

  @doc "The generator modules under the shape-coverage manifest."
  @spec participants() :: [module()]
  def participants, do: @participants

  @doc "Every `{assay_id, cell}` point the participants declare they must cover."
  @spec expected() :: MapSet.t({String.t(), atom()})
  def expected do
    @participants |> Enum.flat_map(& &1.cover_cells()) |> MapSet.new()
  end

  @doc """
  Sample each participant's `gen/0` (`draws` draws apiece) and collect the
  `{assay_id, cover_tag}` points actually produced (tagged challenges only).
  """
  @spec hit_points(pos_integer()) :: MapSet.t({String.t(), atom()})
  def hit_points(draws \\ 600) do
    for mod <- @participants,
        c <- B.interp(mod.gen()) |> Enum.take(draws),
        not is_nil(c.cover_tag),
        into: MapSet.new(),
        do: {c.assay, c.cover_tag}
  end

  @doc "Declared points that no draw produced — empty iff the manifest is fully covered."
  @spec missing(pos_integer()) :: MapSet.t({String.t(), atom()})
  def missing(draws \\ 600), do: MapSet.difference(expected(), hit_points(draws))
end
