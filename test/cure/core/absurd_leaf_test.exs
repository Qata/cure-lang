defmodule Cure.Core.AbsurdLeafTest do
  @moduledoc """
  The {:absurd} leaf (spec §5): it only ever sits in a discharged branch. It has
  NO positive typing rule — inferring it in a reachable position must return a
  clean {:error, _}, never crash the kernel — and it must serialize round-trip.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Env, Kernel, Serialize}

  test "infer/2 rejects {:absurd} cleanly instead of raising" do
    ctx = Context.empty(Env.empty())
    assert {:error, :absurd_in_reachable_position} = Kernel.infer(ctx, {:absurd})
  end

  test "{:absurd} serializes and parses back to itself" do
    assert {:ok, {:absurd}} = Serialize.decode(Serialize.encode({:absurd}))
  end
end
