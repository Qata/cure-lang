defmodule Cure.Core.NoGradualAnyTest do
  @moduledoc """
  K14 pin — no gradual `Any`/top-type in the dependent Core mode.

  The gradual `Any` (a top type with universal subtyping, everything `<: Any`) is
  a semantic escape that lives ONLY in the old non-dependent `Cure.Types` checker
  (Tier-2, out of scope here). It cannot be expressed in the dependent Core: the
  Core term grammar has no `Any` node, the builtin-inductive registry knows only
  genuine inductives (bool/nat/eq), and the surface→Core index bridge fails closed
  on anything outside the index grammar. So K14's Core-mode policy is enforced by
  construction — no production change is warranted (banning a type merely *named*
  `Any` would be wrong; Idris/Agda/Lean all permit that name — the ban is on the
  gradual top-type *semantics*, which Core simply cannot represent). These pins
  make the invariant executable so reintroducing a gradual `Any` trips a guard.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.Builtins
  alias Cure.Types.CoreBridge

  test "the dependent builtin registry has no gradual Any/top-type — only genuine inductives" do
    # The whole builtin surface is real inductives with real constructors.
    assert Builtins.schema(:bool) == [{:False, 0}, {:True, 0}]
    assert Builtins.schema(:nat) == [{:Z, 0}, {:S, 1}]
    assert Builtins.schema(:eq) == [{:reflexive, 1}]
    # No top-type builtin under any of its usual gradual spellings.
    for key <- [:any, :Any, :top, :dynamic, :unknown] do
      assert_raise KeyError, fn -> Builtins.schema(key) end
    end
  end

  test "the surface→Core index bridge fails closed on a gradual-Any node (cannot cross into a dependent index)" do
    # Anything outside the index grammar yields :error, never a permissive Core
    # term — so a gradual-Any-typed thing cannot be admitted into a dependent index.
    assert :error = CoreBridge.to_core({:any, [], []})
    assert :error = CoreBridge.to_core({:type_any, [], "Any"})
  end
end
