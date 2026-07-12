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

  # END-STATE pin for #18 (the classic-pathway rip-out): the classic
  # `Codegen.dispatch_container/6` `:fsm`/`:actor`/`:supervisor`/`:app` cases are
  # gone, so a legacy `fsm` container now falls to the dependent pipeline's
  # `unsupported_container` catch-all instead of being silently classic-compiled.
  test "an fsm container is rejected with unsupported_container" do
    src = """
    mod F
      fsm Light
        Red --go--> Green
        Green --stop--> Red
      end
    end
    """

    assert {:error, reason} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert inspect(reason) =~ "unsupported_container"
  end
end
