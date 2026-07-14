defmodule Cure.Elab.NameTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Name

  test "preserves content-derived identities containing hash characters" do
    name = :"Union<Int|Std.Bool#Bool>"

    assert Name.owner(name) == nil
    assert Name.base(name) == "Union<Int|Std.Bool#Bool>"
  end

  test "splits canonical owner-qualified names only at their owner separator" do
    name = :"Std.Functor#__impl_Functor_Std.List#List_fmap"

    assert Name.owner(name) == "Std.Functor"
    assert Name.base(name) == "__impl_Functor_Std.List#List_fmap"
  end
end
