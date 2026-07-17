# Ensure the Cure standard library is compiled to BEAM before the suite
# runs.
#
# Several test files (notably `test/cure/stdlib/iter_test.exs`,
# `test/cure/stdlib/pbt_test.exs`, and anything else that relies on
# `Cure.Stdlib.Preload.preload/1`) expect
# `_build/cure/ebin/Cure.Std.*.beam` to exist at startup. Locally we
# usually have the beams lying around from a previous `mix cure.compile_stdlib`
# invocation, so everything works. In CI (and on any truly fresh
# checkout) there is no `_build/cure/ebin` yet, so the preload helper
# silently does nothing and the tests above fail with
# `UndefinedFunctionError: function :"Cure.Std.Iter".from_list/1 is undefined`.
#
# Running the compile task here pays the cost once per suite, guarantees
# the beams are present, and keeps the dependency explicit.
#
# We compile UNCONDITIONALLY rather than gating on the presence of a single
# sentinel beam. A presence check cannot notice that a stdlib source changed
# since its beam was built, so an edited module (e.g. `lib/std/vector.cure`)
# would leave a stale `_build/cure/ebin/*.beam` in place and produce ordering-
# dependent test flakes. A full recompile once per suite is a few seconds and
# is always correct.
IO.puts("test_helper: compiling Cure stdlib")
Mix.Task.run("cure.compile_stdlib")

# --- C1: load + stick the canonical stdlib -------------------------------------
#
# The BEAM has one global code-table slot per module name. `cure.compile_stdlib`
# has just written the canonical `_build/cure/ebin/Cure.*.beam`. Load every one of
# them and mark it STICKY (`:code.stick_mod/1`): a sticky module refuses
# `:code.load_binary`/`load_file` with `{:error, :sticky_directory}`, so no later
# producer test can overwrite the canonical surface consumers depend on. Any
# producer still emitting a bare canonical name now fails loudly and
# deterministically (a worklist item) instead of silently clobbering.
(fn ->
   ebin = "_build/cure/ebin"

   # Scope strictly to the stdlib namespace `Cure.Std.*`. `_build/cure/ebin` is the
   # stdlib compile output, but tests that `Cure.Compiler.compile_and_load` an
   # ad-hoc `mod Hello` / `mod M` also drop a `Cure.<Name>.beam` here as a side
   # effect. Those are NOT stdlib and must not be stuck (nor counted "extra" below):
   # every module declared in `lib/std/*.cure` is `Std.*`, so the canonical surface
   # is exactly `Cure.Std.*`.
   loaded =
     ebin
     |> Path.join("Cure.Std.*.beam")
     |> Path.wildcard()
     |> Enum.map(fn path ->
       mod = path |> Path.basename(".beam") |> String.to_atom()
       {:module, ^mod} = :code.ensure_loaded(mod)
       # `:code.stick_mod/1` returns `true` (not `:ok`).
       true = :code.stick_mod(mod)
       mod
     end)
     |> MapSet.new()

   if MapSet.size(loaded) == 0 do
     raise """
     test_helper: no canonical stdlib beams found in #{ebin}.
     Expected `mix cure.compile_stdlib` to have written Cure.*.beam there.
     """
   end

   # Completeness: every module DECLARED in lib/std/*.cure must be resident, or a
   # consumer could hit a not-loaded module the sticky set never covered.
   mod_regex = ~r/^\s*(?:mod|proof|actor|fsm|sup|app)\s+([A-Za-z_][\w\.]*)/m

   declared =
     "lib/std/*.cure"
     |> Path.wildcard()
     |> Enum.flat_map(fn path ->
       case File.read(path) do
         {:ok, src} ->
           mod_regex
           |> Regex.scan(src)
           |> Enum.map(fn [_, name] -> String.to_atom("Cure." <> name) end)

         {:error, _} ->
           []
       end
     end)
     |> MapSet.new()

   # Spec C1 requires catching a mismatch in EITHER direction: a declared module
   # not compiled (missing) OR a compiled module not declared (extra) — the latter
   # signals a stale beam or a rename that left an orphan, which would be stuck
   # under a name no source backs.
   missing = MapSet.difference(declared, loaded)
   extra = MapSet.difference(loaded, declared)

   unless MapSet.size(missing) == 0 do
     raise """
     test_helper: these stdlib modules are declared in lib/std/*.cure but were not
     compiled to #{ebin} (so they cannot be made sticky and consumers may flake):
     #{missing |> MapSet.to_list() |> Enum.sort() |> Enum.map_join(", ", &inspect/1)}

     Run `mix cure.compile_stdlib` and check its output for compile errors.
     """
   end

   unless MapSet.size(extra) == 0 do
     raise """
     test_helper: these modules were compiled to #{ebin} but are NOT declared in
     any lib/std/*.cure (a stale beam or an orphaned rename — sticking one would
     freeze a name no current source produces):
     #{extra |> MapSet.to_list() |> Enum.sort() |> Enum.map_join(", ", &inspect/1)}

     Delete the stale beam(s) or run a clean `mix cure.compile_stdlib`.
     """
   end

   # A hard sanity floor in case both scans somehow degrade to empty.
   for sentinel <- [:"Cure.Std.String", :"Cure.Std.Core", :"Cure.Std.List"] do
     unless MapSet.member?(loaded, sentinel) and :code.is_sticky(sentinel) do
       raise "test_helper: sentinel #{inspect(sentinel)} is not loaded+sticky; stdlib compile is incomplete."
     end
   end

   IO.puts("test_helper: stuck #{MapSet.size(loaded)} canonical stdlib modules")
 end).()

# A tail-friendly failure formatter.
#
# ExUnit prints each failure inline, in the moment it happens — buried among
# thousands of progress dots, compile warnings, and Antigen breadcrumbs. On a
# ~25-minute suite piped through `tail`, the "Result: N failed" summary survives
# but the actual failure blocks scroll away, so `tail` of the log shows THAT
# something failed but never WHAT. This formatter captures every failure's fully
# formatted block (assertion, diff, stacktrace — exactly what the CLI prints) and
# the `after_suite` hook below re-prints them as the final lines of output. A
# `tail` of a piped run then always ends with precisely what failed and why.
:ets.new(:cure_failure_tail, [:named_table, :public, :ordered_set])

defmodule Cure.FailureTailFormatter do
  @moduledoc false
  use GenServer

  @impl true
  def init(opts), do: {:ok, %{width: Keyword.get(opts, :width, 80)}}

  @impl true
  def handle_cast({:test_finished, %ExUnit.Test{state: {:failed, failures}} = test}, state) do
    counter = :ets.info(:cure_failure_tail, :size) + 1
    text = ExUnit.Formatter.format_test_failure(test, failures, counter, state.width, &plain/2)
    :ets.insert(:cure_failure_tail, {counter, text})
    {:noreply, state}
  end

  # setup_all / module-level failures arrive here, not as individual tests.
  def handle_cast({:module_finished, %ExUnit.TestModule{state: {:failed, failures}} = mod}, state) do
    counter = :ets.info(:cure_failure_tail, :size) + 1
    text = ExUnit.Formatter.format_test_all_failure(mod, failures, counter, state.width, &plain/2)
    :ets.insert(:cure_failure_tail, {counter, text})
    {:noreply, state}
  end

  def handle_cast(_event, state), do: {:noreply, state}

  # This text lands in a piped log, not a TTY — emit it without ANSI coloring.
  defp plain(_kind, content), do: content
end

ExUnit.start(formatters: [ExUnit.CLIFormatter, Cure.FailureTailFormatter])

# Antigen deliberately injects "immune response" violations (test scaffolding
# exercising the detection machinery). Rather than flood stdout with one calm
# breadcrumb per occurrence — which buries a genuine `ANTIGEN INFECTION` — the
# Runner tallies them; report the total once, after the suite.
ExUnit.after_suite(fn _result ->
  case Antigen.Report.immune_response_count() do
    0 -> :ok
    n -> IO.puts("\n#{n} immune responses successfully triggered (expected, deliberately injected).")
  end

  # Shape-coverage summary: any manifest assay whose declared cells were not all
  # produced this run is surfaced here (see Antigen.CoverManifest.report/0). Silent
  # when the coverage-manifest gate did not run this invocation (nothing stashed).
  case Antigen.CoverManifest.report() do
    nil -> :ok
    line -> IO.puts("\n" <> line)
  end

  # Last of all: re-print every failure block, so a `tail` of the piped run
  # ends with exactly what failed and why (see Cure.FailureTailFormatter above).
  case :ets.tab2list(:cure_failure_tail) do
    [] ->
      :ok

    entries ->
      bar = String.duplicate("=", 72)
      IO.puts("\n" <> bar)
      IO.puts("FAILURES (#{length(entries)}) — re-printed below so a tail of the log catches them:")
      IO.puts(bar)

      entries
      |> Enum.sort_by(&elem(&1, 0))
      |> Enum.each(fn {_counter, text} -> IO.puts(text) end)
  end
end)
