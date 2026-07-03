defmodule Mix.Tasks.Antigen do
  @moduledoc """
  Run the Antigen property-based metatheory engine (spec §8).

      mix antigen [--count N | --budget Nm] [--bias] [--corpus PATH] [--seeds PATH] [--report-dir DIR]
      mix antigen generate [--count N | --budget Nm] [--seeds PATH] [--report-dir DIR]

  `mix antigen` is the **explorer**: generate → assay → bank; it self-terminates
  after a bounded number of generation rounds (`--count`, default #{20_000},
  a full run of ~30 seconds) or a wall-budget (`--budget 3m`, converted at a
  fixed `@rounds_per_minute`).

  `--bias` enables health-adaptive round-based generation (spec §4): the mix
  reweights toward the weakest vertical between rounds. It only has an observable
  effect when `--count` exceeds the 200 round size (otherwise the single round has
  no "next round" to reweight and it behaves like an unbiased run).

  `mix antigen generate` is **harvest-only**: it produces well-formed antigens,
  coverage-dedups, appends them to the seed store, and skips the assays entirely.

  ## Signals

  Every banked record is written with a single, atomic, synchronous append
  (`Antigen.Corpus.append/3`), so it is durable on disk the instant it lands.
  An untrapped **SIGINT** (Ctrl+C) therefore loses at most the in-flight record,
  never a previously-appended one. SIGINT is *not* application-interceptable and
  is deliberately **not** trapped here. A `:sigterm` handler is installed (outside
  the test env) only so an operator's `kill -TERM` prints a clean final line
  before the VM stops — it is not a durability mechanism.
  """
  use Mix.Task

  @shortdoc "Run the Antigen metatheory engine (explore | generate)"

  @default_count 20_000
  @rounds_per_minute 2000

  @switches [count: :integer, budget: :string, bias: :boolean, corpus: :string, seeds: :string,
             report_dir: :string, out: :string, guided: :boolean, precise: :boolean,
             edge_corpus: :string]

  @impl Mix.Task
  def run(argv) do
    {opts, rest, _} = OptionParser.parse(argv, strict: @switches)

    mode =
      cond do
        match?(["cover" | _], rest) -> :cover
        match?(["generate" | _], rest) -> :generate
        true -> :explore
      end
    count = resolve_count(opts)

    seeds_path = opts[:seeds] || "test/antigen/seeds.sexp"

    runner_opts = [
      # The three schema-directed generators; explore dispatches each challenge to
      # its assay via the runner's registry (no fixed `:assay` module).
      gen: default_gen(),
      corpus_path: opts[:corpus] || "test/antigen/corpus.sexp",
      seeds_path: seeds_path,
      report_dir: opts[:report_dir] || "tmp/antigen",
      count: count,
      bias: opts[:bias]
    ]

    # Install the corpus-backed filler pool (spec §3) once, before dispatch, so both
    # explore and generate share the pooled `gnat`. Inert if the seeds file is absent.
    Process.put(:antigen_seed_pool, Antigen.Generators.SeedPool.load(seeds_path))

    case mode do
      :explore ->
        r = Antigen.Runner.explore(runner_opts)
        IO.puts("antigen: #{r.infections} infection(s), #{r.seeds_banked} seed(s) banked")

      :generate ->
        install_sigterm_trap()
        r = Antigen.Runner.generate(runner_opts)
        IO.puts("antigen generate: #{r.seeds_banked} seed(s) banked")

      :cover ->
        {coverage, _report} = Antigen.Cover.run_report(Keyword.put(runner_opts, :out, opts[:out]))
        covered = coverage |> Map.values() |> Enum.map(&length(&1.covered)) |> Enum.sum()
        total = coverage |> Map.values() |> Enum.map(& &1.total) |> Enum.sum()
        pct = if total > 0, do: Float.round(covered * 100 / total, 1), else: 0.0
        dest = if opts[:out], do: " → #{opts[:out]}", else: ""
        IO.puts("antigen cover: #{covered}/#{total} kernel lines (#{pct}%)#{dest}")
    end
  end

  @doc "Convert a `\"Nm\"` wall-budget to a round count via the fixed `@rounds_per_minute`."
  @spec budget_to_count(String.t()) :: pos_integer()
  def budget_to_count(budget) do
    {minutes, _rest} = Integer.parse(budget)
    max(minutes, 1) * @rounds_per_minute
  end

  # Explorer default: Tier-A's three known-label generators + Tier-B's three
  # typed-term/assay-id branches + the mutation corpus + conversion-at-depth (both
  # polarities), weight 1 each. Public so tests can sample the wired distribution.
  def default_gen do
    Antigen.Gen.frequency([
      {1, Antigen.Generators.Totality.gen()},
      {1, Antigen.Generators.Positivity.gen()},
      {1, Antigen.Generators.Forcing.gen()},
      {1, Antigen.Generators.Term.typed_term("term/infer_check")},
      {1, Antigen.Generators.Term.typed_term("term/subject_reduction")},
      {1, Antigen.Generators.Term.typed_term("term/normalization")},
      {1, Antigen.Generators.Mutation.mutant()},
      {1, Antigen.Generators.Conversion.conv_reject()},
      {1, Antigen.Generators.Conversion.conv_accept("term/infer_check")},
      {1, Antigen.Generators.Conversion.conv_accept("term/subject_reduction")},
      {1, Antigen.Generators.Conversion.conv_accept("term/normalization")},
      {1, Antigen.Generators.Term.typed_term("kernel/shift_subst")},
      {1, Antigen.Generators.Term.typed_term("kernel/weakening")},
      {1, Antigen.Generators.Term.typed_term("kernel/confluence")}
    ])
  end

  defp resolve_count(opts) do
    cond do
      opts[:count] -> opts[:count]
      opts[:budget] -> budget_to_count(opts[:budget])
      true -> @default_count
    end
  end

  # Trap SIGTERM only, and never during `mix test` (a lingering handler would
  # outlive the test). SIGINT is intentionally left untrapped — see moduledoc.
  defp install_sigterm_trap do
    if Mix.env() != :test do
      try do
        System.trap_signal(:sigterm, fn ->
          IO.puts("antigen: SIGTERM — every banked record is already durable; stopping.")
          System.halt(0)
        end)
      rescue
        _ -> :ok
      end
    end

    :ok
  end
end
