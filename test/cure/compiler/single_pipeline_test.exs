defmodule Cure.Compiler.SinglePipelineTest do
  @moduledoc """
  Post-rip-out pins: (1) a plain, previously-classic-routed module compiles
  through the sole (dependent) pipeline and runs; (2) legacy container
  declarations are rejected at elaboration, not silently classic-compiled.
  """
  use ExUnit.Case, async: false

  test "a plain non-dependent module compiles via the sole pipeline and runs" do
    src = """
    mod Plain
      fn add3(x: Int) -> Int = x + 3
    end
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(mod, :add3, [4]) == 7
  end

  test "an fsm container is lowered by the auto-preluded macro" do
    src = """
    mod F
      fsm Cure.Light
    end
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert module == :"Cure.F"
    assert match?({:ok, _pid}, apply(:"Cure.Light", :start_link, [0]))
  end
end
