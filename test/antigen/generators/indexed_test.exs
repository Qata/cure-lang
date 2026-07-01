defmodule Antigen.Generators.IndexedTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.Indexed
  alias Cure.Core.Inductive

  test "4.1 branch_family :ill_typed genuinely contains a foreign-family branch" do
    c = Indexed.branch_family(:ill_typed)
    env = Indexed.env_of(c)
    {:case, _scrut, _motive, branches} = c.payload.def_body
    branch_ctors = Enum.map(branches, fn {cn, _ar, _b} -> cn end)

    # MkFoo is present as a branch, and it really belongs to Foo, not Dec.
    assert :MkFoo in branch_ctors
    assert Inductive.ctor_family(env, :MkFoo) == :Foo
    assert Inductive.ctor_family(env, :Causal) == :Dec
    # ...and every Dec ctor is still covered (so coverage passes; the additive form).
    assert :Dcoupled in branch_ctors and :Causal in branch_ctors
  end

  test "4.1 branch_family :well_typed draws all branches from Dec" do
    c = Indexed.branch_family(:well_typed)
    env = Indexed.env_of(c)
    {:case, _s, _m, branches} = c.payload.def_body
    assert Enum.all?(branches, fn {cn, _ar, _b} -> Inductive.ctor_family(env, cn) == :Dec end)
  end
end
