defmodule Cure.Stdlib.AtomSurfaceTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  test "closed system-time vocabulary rejects a raw atom" do
    assert {:error, _} =
             Program.elaborate("""
             mod BadTimeUnit
               use Std.System
               fn now() -> Int = system_time(:millisecond)
             """)
  end

  test "closed system-time vocabulary accepts TimeUnit" do
    assert {:ok, _} =
             Program.elaborate("""
             mod GoodTimeUnit
               use Std.System
               fn now() -> Int = system_time(Millisecond())
             """)
  end

  test "process exit requires ExitReason rather than a raw atom" do
    assert {:ok, _} =
             Program.elaborate("""
             mod GoodExitReason
               use Std.Process
               fn stop(pid: Pid) -> Unit = exit(pid, Shutdown())
             """)

    assert {:error, _} =
             Program.elaborate("""
             mod BadExitReason
               use Std.Process
               fn stop(pid: Pid) -> Unit = exit(pid, :shutdown)
             """)
  end

  test "safe atom lookup preserves existing atoms without interning input" do
    assert :ok = :"Cure.Std.String".to_existing_atom(~c"ok")

    unknown = "cure_atom_surface_#{System.unique_integer([:positive])}"
    assert_raise ArgumentError, fn ->
      apply(:"Cure.Std.String", :to_existing_atom, [String.to_charlist(unknown)])
    end

    assert_raise ArgumentError, fn -> String.to_existing_atom(unknown) end
  end

  test "effect-only convenience operations discard BEAM success atoms as Unit" do
    assert :unit = :"Cure.Std.Process".link(self())
    assert :unit = :"Cure.Std.Process".unlink(self())
  end

  test "timestamp wrappers still call BEAM with the correct atom encoding" do
    now = :"Cure.Std.System".timestamp_ms()
    assert is_integer(now)
    assert now > 0
  end
end
