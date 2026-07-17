defmodule Cure.RegressionTest do
  use ExUnit.Case, async: false

  @moduledoc """
  End-to-end regression coverage. These tests invoke the same logic as
  `mix cure.check` so a plain `mix test` run catches stdlib or example
  regressions too.
  """

  alias Mix.Tasks.Cure.Check

  # :slow — compiles all 81 stdlib modules (~22s). CI covers this both here
  # (`mix test --include slow`) and via its dedicated `mix cure.check.stdlib` step.
  @tag :regression
  @tag :slow
  test "every Std.* module compiles without warnings" do
    result =
      ExUnit.CaptureIO.capture_io(fn ->
        try do
          Check.Stdlib.run([])
        catch
          :exit, {:shutdown, 1} -> flunk("stdlib regression failed")
        end
      end)

    assert result =~ ~r/stdlib: \d+ passed, 0 failed/
  end

  @tag :regression
  test "every supported example compiles and produces the expected output" do
    preload_stdlib()

    result =
      ExUnit.CaptureIO.capture_io(fn ->
        try do
          Check.Examples.run([])
        catch
          :exit, {:shutdown, 1} -> flunk("examples regression failed")
        end
      end)

    refute result =~ "FAIL"
    assert result =~ ~r/examples: \d+ passed, \d+ skipped, 0 failed/
  end

  defp preload_stdlib do
    # Use the shared helper: loading beams by name instead of adding the
    # build dirs to the code path prevents stale lowercase leftovers from
    # shadowing OTP modules (notably `:math`) mid-suite. Explicit
    # `kind: :all` preserves the historical "load everything" behaviour
    # now that `Preload.preload/1` defaults to `:none`.
    Cure.Stdlib.Preload.preload(examples: true, kind: :all)
  end
end
