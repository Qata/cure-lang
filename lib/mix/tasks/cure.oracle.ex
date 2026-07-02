defmodule Mix.Tasks.Cure.Oracle do
  @shortdoc "Regenerate differential-oracle fixtures (live mode; needs idris2)"
  @moduledoc """
  Live mode of the differential oracle (design spec §7). For every cluster under
  `test/oracle/`, run each `.cure` through Cure and each `.idr` through
  `idris2 --check`, then rewrite that cluster's `verdicts.json`.

  Binary: `$IDRIS2_BIN`, else `~/Develop/Idris2/build/exec/idris2`.

  Regeneration PRESERVES prior `relation`/`reason` fields. A brand-new pair gets
  `relation: "same"` deliberately, so if its verdicts diverge, `replay` fails
  loudly and forces a human to triage (never hand-edit a verdict).

  Usage:
      mix cure.oracle            # all clusters
      mix cure.oracle rewrite    # one cluster
  """
  use Mix.Task
  alias Cure.Oracle

  @impl Mix.Task
  def run(argv) do
    Mix.Task.run("app.start")
    bin = Oracle.default_idris_bin()

    unless File.exists?(bin) do
      Mix.raise("idris2 not found at #{bin} — build it (plan Task 2) or set $IDRIS2_BIN")
    end

    clusters = if argv == [], do: Oracle.clusters(), else: argv

    for cluster <- clusters do
      prior = Oracle.read_fixture(cluster)

      fixture =
        for %{name: name, cure_path: cp, idr_path: ip} <- Oracle.pairs(cluster), into: %{} do
          base = Map.get(prior, name, %{"relation" => "same", "reason" => ""})

          entry = %{
            "cure" => Atom.to_string(Oracle.cure_verdict(cp)),
            "idris" => Atom.to_string(Oracle.idris_verdict(bin, ip)),
            "relation" => Map.get(base, "relation", "same"),
            "reason" => Map.get(base, "reason", "")
          }

          Mix.shell().info(
            "#{cluster}/#{name}: cure=#{entry["cure"]} idris=#{entry["idris"]} " <>
              "rel=#{entry["relation"]}#{if Oracle.consistent(entry) == :ok, do: "", else: "  <-- TRIAGE"}"
          )

          {name, entry}
        end

      Oracle.write_fixture(cluster, fixture)
      Mix.shell().info("wrote #{Path.join(["test/oracle", cluster, "verdicts.json"])}")
    end
  end
end
