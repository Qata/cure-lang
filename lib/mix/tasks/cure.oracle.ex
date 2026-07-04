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

      # Fan out: one task per probe, and inside each the Cure and Idris checks
      # run concurrently. Every check is bound by a timeout, so a non-terminating
      # elaboration surfaces as `timeout` (with its wall-clock) instead of
      # wedging the run. Join all probes at the end.
      results =
        Oracle.pairs(cluster)
        |> Enum.map(fn %{name: name, cure_path: cp, idr_path: ip} ->
          task =
            Task.async(fn ->
              cure = Task.async(fn -> Oracle.cure_verdict_timed(cp) end)
              idris = Task.async(fn -> Oracle.idris_verdict_timed(bin, ip) end)
              {Task.await(cure, :infinity), Task.await(idris, :infinity)}
            end)

          {name, task}
        end)
        |> Enum.map(fn {name, task} -> {name, Task.await(task, :infinity)} end)

      fixture =
        for {name, {{cure_v, cure_ms}, {idris_v, idris_ms}}} <- results, into: %{} do
          base = Map.get(prior, name, %{"relation" => "same", "reason" => ""})

          entry = %{
            "cure" => Atom.to_string(cure_v),
            "idris" => Atom.to_string(idris_v),
            "relation" => Map.get(base, "relation", "same"),
            "reason" => Map.get(base, "reason", "")
          }

          Mix.shell().info(
            "#{cluster}/#{name}: cure=#{entry["cure"]} (#{cure_ms}ms) " <>
              "idris=#{entry["idris"]} (#{idris_ms}ms) rel=#{entry["relation"]}" <>
              if(Oracle.consistent(entry) == :ok, do: "", else: "  <-- TRIAGE")
          )

          {name, entry}
        end

      Oracle.write_fixture(cluster, fixture)
      Mix.shell().info("wrote #{Path.join(["test/oracle", cluster, "verdicts.json"])}")
    end
  end
end
