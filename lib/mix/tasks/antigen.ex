defmodule Mix.Tasks.Antigen do
  @moduledoc """
  Run the Antigen property-based metatheory engine (spec §8).

      mix antigen [--count N | --budget Nm] [--corpus PATH] [--seeds PATH] [--report-dir DIR]
      mix antigen generate [--count N | --budget Nm] [--seeds PATH] [--report-dir DIR]

  `mix antigen` is the **explorer**: generate → assay → bank; it self-terminates
  after a bounded number of generation rounds (`--count`, default #{200}) or a
  wall-budget (`--budget 3m`, converted at a fixed `@rounds_per_minute`).

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

  @default_count 200
  @rounds_per_minute 2000

  @switches [count: :integer, budget: :string, corpus: :string, seeds: :string, report_dir: :string]

  @impl Mix.Task
  def run(argv) do
    {opts, rest, _} = OptionParser.parse(argv, strict: @switches)

    mode = if match?(["generate" | _], rest), do: :generate, else: :explore
    count = resolve_count(opts)

    runner_opts = [
      # The three schema-directed generators; explore dispatches each challenge to
      # its assay via the runner's registry (no fixed `:assay` module).
      gen: default_gen(),
      corpus_path: opts[:corpus] || "test/antigen/corpus.sexp",
      seeds_path: opts[:seeds] || "test/antigen/seeds.sexp",
      report_dir: opts[:report_dir] || "tmp/antigen",
      count: count
    ]

    case mode do
      :explore ->
        r = Antigen.Runner.explore(runner_opts)
        IO.puts("antigen: #{r.infections} infection(s), #{r.seeds_banked} seed(s) banked")

      :generate ->
        install_sigterm_trap()
        r = Antigen.Runner.generate(runner_opts)
        IO.puts("antigen generate: #{r.seeds_banked} seed(s) banked")
    end
  end

  @doc "Convert a `\"Nm\"` wall-budget to a round count via the fixed `@rounds_per_minute`."
  @spec budget_to_count(String.t()) :: pos_integer()
  def budget_to_count(budget) do
    {minutes, _rest} = Integer.parse(budget)
    max(minutes, 1) * @rounds_per_minute
  end

  # Explorer default: Tier-A's three known-label generators + Tier-B's three
  # typed-term/assay-id branches, weight 1 each (six branches).
  defp default_gen do
    Antigen.Gen.frequency([
      {1, Antigen.Generators.Totality.gen()},
      {1, Antigen.Generators.Positivity.gen()},
      {1, Antigen.Generators.Forcing.gen()},
      {1, Antigen.Generators.Term.typed_term("term/infer_check")},
      {1, Antigen.Generators.Term.typed_term("term/subject_reduction")},
      {1, Antigen.Generators.Term.typed_term("term/normalization")}
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
