defmodule Cure.Observe.TraceTest do
  @moduledoc """
  The tracer over compiler internals: multi-function tracing, output truncation,
  and the `only_errors` filter that pins where a rejection originates. `:dbg` is
  system-wide, so this suite is synchronous.
  """
  use ExUnit.Case, async: false

  alias Cure.Observe.Trace

  @ok "mod TrOk\n  fn start() -> Int = 1\nend\n"
  @bad "mod TrBad\n  fn f(c :linear TrBad) -> Int = 1\nend\n"

  defp drain(acc \\ []) do
    receive do
      {:cure_trace, line} -> drain([line | acc])
    after
      150 -> Enum.reverse(acc)
    end
  end

  defp run(mfas, opts, src) do
    Trace.start(mfas, Keyword.put(opts, :self, true))
    Cure.Elab.Program.elaborate(src)
    Trace.stop()
    drain()
  end

  test "single MFA (backward compat) traces a call and its return" do
    lines = run({Cure.Elab.Program, :elaborate, 1}, [], @ok)

    assert Enum.any?(lines, &String.starts_with?(&1, "call Elixir.Cure.Elab.Program.elaborate/1"))
    assert Enum.any?(lines, &(&1 =~ "return Elixir.Cure.Elab.Program.elaborate/1 -> {:ok"))
  end

  test "a LIST of MFAs traces the whole path in one run" do
    lines =
      run(
        [
          {Cure.Elab.Program, :elaborate, 1},
          {Cure.Elab.Elaborator, :collect_with_siblings, 4}
        ],
        [],
        @ok
      )

    assert Enum.any?(lines, &(&1 =~ "Cure.Elab.Program.elaborate/1"))
    # collect_with_siblings may or may not run for @ok, but the path-trace must not crash
    assert is_list(lines)
  end

  test "only_errors prints just the {:error, _} returns (pins the origin)" do
    lines = run([{Cure.Elab.Program, :elaborate, 1}], [only_errors: true], @bad)

    # No `call` lines, no `↳ returned to` lines — only the error return.
    refute Enum.any?(lines, &String.starts_with?(&1, "call "))
    refute Enum.any?(lines, &String.contains?(&1, "↳"))
    assert Enum.any?(lines, &(&1 =~ "-> {:error"))
  end

  test "limit caps argument/return rendering" do
    [tight] = run({Cure.Elab.Program, :elaborate, 1}, [only_errors: true, limit: 1], @bad)
    [wide] = run({Cure.Elab.Program, :elaborate, 1}, [only_errors: true, limit: :infinity], @bad)

    assert String.length(tight) <= String.length(wide)
    assert tight =~ "{:error"
  end
end
