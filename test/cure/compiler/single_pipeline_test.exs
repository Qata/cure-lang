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

  # Anticipatory pin for the END-STATE of #18 (the classic-pathway rip-out): once
  # the `:fsm`/`:actor`/`:supervisor`/`:app` cases are deleted from
  # `Codegen.dispatch_container/6`, a legacy `fsm` container falls to the
  # `unsupported_container` catch-all. Skipped until that rip-out runs — today
  # those four cases are still live AND still exercised by ~25 tests + the whole
  # `test/cure/{fsm,actor,sup,app}/` tree (all through this same `compile_and_load`
  # path), so rejecting `fsm` here would turn that surface red. Un-skip as the
  # first green step of the #18 teardown.
  @tag :skip
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
