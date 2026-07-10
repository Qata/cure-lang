defmodule Cure.Stdlib.PrimitiveModulesTest do
  @moduledoc """
  The machine base types have visible, inspectable Std homes (spec 2026-07-10-
  primitive-type-declarations): Std.Int, Std.Float, and Std.Binary each declare
  their `@builtin(:tag) primitive Name` and elaborate cleanly.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program
  alias Cure.Core.Env

  test "Std.Int declares Int and elaborates cleanly" do
    {:ok, env} = Program.elaborate(File.read!("lib/std/int.cure"))
    assert Env.primitive(env, "Int") == {:int_type}
  end

  test "Std.Float declares Float and elaborates cleanly" do
    {:ok, env} = Program.elaborate(File.read!("lib/std/float.cure"))
    assert Env.primitive(env, "Float") == {:float_type}
  end

  test "Std.Binary still elaborates with the primitive Binary declaration" do
    assert {:ok, _env} = Program.elaborate(File.read!("lib/std/binary.cure"))
  end
end
