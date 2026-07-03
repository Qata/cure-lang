defmodule Antigen.Cover do
  @moduledoc "Erlang :cover harness for kernel code coverage (Antigen tooling; no TCB changes)."

  @cover_modules [Cure.Core.Kernel, Cure.Core.Normalise, Cure.Core.Conv,
                  Cure.Core.Eval, Cure.Core.Quote, Cure.Core.Inductive,
                  Cure.Core.Serialize, Cure.Core.Certificate]
  def cover_modules, do: @cover_modules

  @doc """
  True if `module`'s beam carries real abstract_code (required by both
  :cover.compile_beam AND Task 3's function_index; :cover.analyse needs the
  former, cold-line→function mapping needs the latter — same underlying chunk).

  MUST inspect the chunk's inner VALUE, not just that :beam_lib.chunks/2
  returned :ok — confirmed against OTP: :beam_lib.chunks(beam, [:abstract_code])
  ALWAYS returns {:ok, {Mod, [...]}} for any valid .beam, even when abstract
  code is absent; absence is signalled by the sentinel atom
  `:no_abstract_code` as the chunk's VALUE, not by an outer :error. A guard
  that only pattern-matches the outer {:ok, _} is vacuously always true and
  never rejects anything — the negative test exists specifically to catch that.
  """
  def cover_compilable?(module) do
    case :code.which(module) do
      beam when is_list(beam) ->
        match?(
          {:ok, {^module, [{:abstract_code, {:raw_abstract_v1, _forms}}]}},
          :beam_lib.chunks(beam, [:abstract_code])
        )

      _ ->
        false
    end
  end

  @doc "Run `fun` with `modules` cover-compiled; always :cover.stop afterward."
  def with_cover(modules, fun) do
    # :cover.start/0 returns {:ok, pid} the first time and
    # {:error, {:already_started, pid}} if a cover session already exists on the
    # node — both mean "the cover server is available"; only a genuinely
    # different error should surface.
    case :cover.start() do
      {:ok, _} -> :ok
      {:error, {:already_started, _}} -> :ok
    end

    try do
      Enum.each(modules, fn m ->
        {:ok, ^m} = normalize_compile({:cover.compile_beam(m), m}, m)
      end)

      fun.()
    after
      :cover.stop()
    end
  end

  defp normalize_compile({{:ok, m}, _}, m), do: {:ok, m}

  defp normalize_compile({{:error, reason}, m}, m),
    do: raise("cover.compile_beam failed for #{inspect(m)}: #{inspect(reason)}")

  @doc """
  Line-level coverage for a cover-compiled `module`. MUST be called inside a
  `with_cover/2` block (before `:cover.stop`). Returns
  `%{covered: [line], cold: [line], total: n}`, excluding the `{{Mod, 0}, {0, 1}}`
  module-level pseudo-entry that `:cover.analyse` always emits.
  """
  def line_coverage(module) do
    {:ok, pairs} = :cover.analyse(module, :coverage, :line)

    {cov, cold} =
      pairs
      |> Enum.reject(fn {{_m, line}, _} -> line == 0 end)
      |> Enum.reduce({[], []}, fn {{_m, line}, {c, _n}}, {yes, no} ->
        if c > 0, do: {[line | yes], no}, else: {yes, [line | no]}
      end)

    %{covered: Enum.sort(cov), cold: Enum.sort(cold), total: length(cov) + length(cold)}
  end

  @doc """
  Runs an Antigen campaign (`Runner.explore/1` with `opts`) with all
  `@cover_modules` cover-compiled, then returns `{coverage_map, report}` where
  `coverage_map` is `%{module => line_coverage/1}` and `report` is the rendered
  markdown (also written to `opts[:out]` if given). The campaign runs inside
  `with_cover/2`, so instrumentation is always torn down afterward.
  """
  def run_report(opts) do
    coverage =
      with_cover(@cover_modules, fn ->
        _ = Antigen.Runner.explore(opts)
        Map.new(@cover_modules, fn m -> {m, line_coverage(m)} end)
      end)

    fn_indexes = Map.new(@cover_modules, fn m -> {m, Antigen.CoverReport.function_index(m)} end)
    report = Antigen.CoverReport.render(coverage, fn_indexes)
    if out = opts[:out], do: File.write!(out, report)
    {coverage, report}
  end

  # -- Phase 2: coverage-guided feedback --------------------------------------

  @doc """
  The set of currently-covered `{module, line}` pairs across `modules`, read
  from live cover state. MUST be called inside a `with_cover/2` block. Cover
  accumulates, so this set grows monotonically until `:cover.reset/0`.
  """
  def covered_set(modules) do
    Enum.reduce(modules, MapSet.new(), fn m, acc ->
      Enum.reduce(line_coverage(m).covered, acc, fn line, a -> MapSet.put(a, {m, line}) end)
    end)
  end

  @doc """
  Batch-gate: `{module, line}` pairs covered now but not in `prev_set`. One
  `:cover.analyse` per module — cheap enough to run every round to decide
  whether a round is interesting before paying for precise attribution.
  """
  def delta(prev_set, modules) do
    MapSet.difference(covered_set(modules), prev_set)
  end

  @doc """
  Precise re-attribution: for each challenge, `:cover.reset/0` then `run_fun.(ch)`
  and measure the `{module, line}` pairs it covers beyond `prev_set`. Returns
  `[{challenge, novel_set}]`.

  `:cover.reset/0` clears counters node-wide, so this is only valid inside a
  `with_cover/2` block and destroys the accumulated coverage — the caller must
  re-establish its baseline afterward. Reserve it for rounds the batch-gate
  already flagged as interesting.
  """
  def attribute(prev_set, challenges, run_fun, modules) do
    Enum.map(challenges, fn ch ->
      :cover.reset()
      run_fun.(ch)
      {ch, MapSet.difference(covered_set(modules), prev_set)}
    end)
  end
end
