defmodule Cure.Elab.BoolConnectiveLoweringTest do
  @moduledoc """
  Phase 2 of retiring the Boolean-connective primitives: the surface operators
  `and`/`or`/`not` and Bool-typed `==`/`!=` now elaborate to APPLICATIONS of the
  `Std.Bool` prelude defs instead of `{:prim, :and/:or/:not/:eq/:ne}` nodes.

  `==`/`!=` are operand-type-directed: numeric (Int/Float) operands keep lowering
  to the native `{:prim, :eq/:ne}` compare; Bool operands lower to `eq`/`ne`.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  # Body of a nullary top-level fn `name` (no lambda wrapper).
  defp body(src, name) do
    {:ok, env} = Program.elaborate("mod M\n  use Std.Bool\n" <> src <> "end\n")
    env.defs[name].body
  end

  @tt {:ctor, :True, []}
  @ff {:ctor, :False, []}

  test "`and` lowers to an `and` application, not a :and prim" do
    assert body("  fn t() -> Bool = true and false\n", :t) ==
             {:app, {:app, {:global, :and}, @tt}, @ff}
  end

  test "`or` lowers to an `or` application" do
    assert body("  fn t() -> Bool = true or false\n", :t) ==
             {:app, {:app, {:global, :or}, @tt}, @ff}
  end

  test "`not` lowers to a `not` application" do
    assert body("  fn t() -> Bool = not true\n", :t) ==
             {:app, {:global, :not}, @tt}
  end

  test "Int `==` stays a native :eq prim" do
    assert body("  fn t() -> Bool = 1 == 2\n", :t) ==
             {:prim, :eq, [{:int_lit, 1}, {:int_lit, 2}]}
  end

  test "Float `==` stays a native :eq prim" do
    assert body("  fn t() -> Bool = 1.0 == 2.0\n", :t) ==
             {:prim, :eq, [{:float_lit, 1.0}, {:float_lit, 2.0}]}
  end

  test "Int `!=` stays a native :ne prim" do
    assert body("  fn t() -> Bool = 1 != 2\n", :t) ==
             {:prim, :ne, [{:int_lit, 1}, {:int_lit, 2}]}
  end

  test "Bool `==` lowers to an `eq` application" do
    assert body("  fn t() -> Bool = true == false\n", :t) ==
             {:app, {:app, {:global, :eq}, @tt}, @ff}
  end

  test "Bool `!=` lowers to a `ne` application" do
    assert body("  fn t() -> Bool = true != false\n", :t) ==
             {:app, {:app, {:global, :ne}, @tt}, @ff}
  end

  test "a mixed Int/Bool `==` is rejected" do
    assert {:error, _} =
             Program.elaborate("mod M\n  use Std.Bool\n  fn t() -> Bool = 1 == true\nend\n")
  end
end
