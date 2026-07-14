defmodule Cure.Elab.NameTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Name

  test "qualifies atom and string components with one canonical spelling" do
    assert Name.qualify("Std.List", :map) == :"Std.List#map"
    assert Name.qualify(:Client, "answer") == :"Client#answer"
  end

  test "decomposes a canonical identity without changing bare names" do
    assert Name.owner(:"Std.List#map") == "Std.List"
    assert Name.base(:"Std.List#map") == "map"
    assert Name.owner(:map) == nil
    assert Name.base(:map) == "map"
  end

  test "qualified detection is independent of the atom representation" do
    assert Name.qualified?("Std.List#map")
    refute Name.qualified?(:map)
  end
end
