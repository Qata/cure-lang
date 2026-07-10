defmodule Cure.Elab.PrimitiveDeclTest do
  @moduledoc """
  `@builtin(:tag) primitive Name` elaborates by confirming the surface name maps
  to its Core node via the marker (spec 2026-07-10-primitive-type-declarations).
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program
  alias Cure.Core.Env

  test "a well-formed primitive declaration confirms its binding" do
    {:ok, env} = Program.elaborate("mod M\n  @builtin(:float) primitive Float\nend\n")
    assert Env.primitive(env, "Float") == {:float_type}
  end

  test "a primitive with no @builtin marker is rejected" do
    assert {:error, _} = Program.elaborate("mod M\n  primitive Widget\nend\n")
  end

  test "a primitive with an unknown @builtin tag is rejected" do
    assert {:error, _} = Program.elaborate("mod M\n  @builtin(:sparkle) primitive Sparkle\nend\n")
  end

  test "a primitive whose tag disagrees with the name's floor is rejected" do
    # Int's floor is {:int_type}; tagging it :float contradicts the floor.
    assert {:error, _} = Program.elaborate("mod M\n  @builtin(:float) primitive Int\nend\n")
  end
end
