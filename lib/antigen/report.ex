defmodule Antigen.Report do
  @moduledoc "Ephemeral full failure reports; never lose a failure to a filtered pipe (spec §10, umbrella §8.1)."
  alias Antigen.{Challenge, Corpus}

  @spec write_infection(String.t(), Challenge.t(), term(), map()) :: {:ok, String.t()}
  def write_infection(dir, %Challenge{} = c, detail, health) do
    File.mkdir_p!(dir)
    slug = slug(c.assay)
    n = next_index(dir, c.seed, slug)
    path = Path.join(dir, "failure-#{c.seed}-#{slug}-#{n}.txt")
    File.write!(path, render(c, detail, health))
    File.write!(Path.join(dir, "latest.txt"), Path.basename(path))
    {:ok, path}
  end

  @spec breadcrumb(Challenge.t(), String.t()) :: String.t()
  def breadcrumb(%Challenge{} = c, path),
    do: "ANTIGEN INFECTION [#{c.assay}] seed=#{c.seed} → #{path}"

  defp render(c, detail, health) do
    """
    ANTIGEN INFECTION
    assay:      #{c.assay}
    label:      #{c.label}  (ground truth)
    seed:       #{c.seed}
    detail:     #{inspect(detail)}
    health:     #{inspect(health)}
    note:       #{c.note}

    -- antigen (C2 record, generator-independent repro) --
    #{Corpus.encode_record(c)}

    -- repro --
    decode the record above and run Antigen.Runner.replay_one/1
    """
  end

  defp slug(assay), do: String.replace(assay, ~r/[^a-zA-Z0-9]+/, "_")

  defp next_index(dir, seed, slug) do
    existing = Path.wildcard(Path.join(dir, "failure-#{seed}-#{slug}-*.txt"))
    length(existing) + 1
  end
end
