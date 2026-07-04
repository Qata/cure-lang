defmodule Cure.Elab.ResolutionTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Resolution

  describe "rekey_term/2" do
    setup do
      %{map: %{Nat: :"Std.Nat#Nat", Z: :"Std.Nat#Z", S: :"Std.Nat#S"}}
    end

    test "rewrites a :data head", %{map: m} do
      assert Resolution.rekey_term({:data, :Nat, [], []}, m) == {:data, :"Std.Nat#Nat", [], []}
    end

    test "rewrites a :ctor head and recurses into args", %{map: m} do
      assert Resolution.rekey_term({:ctor, :S, [{:ctor, :Z, []}]}, m) ==
               {:ctor, :"Std.Nat#S", [{:ctor, :"Std.Nat#Z", []}]}
    end

    test "rewrites a :case branch TAG (the position distinct from {:ctor,…})", %{map: m} do
      term = {:case, {:var, 0}, {:lam, {:data, :Nat, [], []}, {:type, 0}},
              [{:Z, 0, {:var, 0}}, {:S, 1, {:ctor, :Z, []}}]}
      assert Resolution.rekey_term(term, m) ==
               {:case, {:var, 0}, {:lam, {:data, :"Std.Nat#Nat", [], []}, {:type, 0}},
                [{:"Std.Nat#Z", 0, {:var, 0}}, {:"Std.Nat#S", 1, {:ctor, :"Std.Nat#Z", []}}]}
    end

    test "leaves a :global untouched (functions keep bare names)", %{map: m} do
      assert Resolution.rekey_term({:global, :Z}, m) == {:global, :Z}
    end

    test "recurses through structural nodes and leaves unmapped atoms alone", %{map: m} do
      term = {:pi, {:data, :Nat, [], []}, {:data, :Other, [], []}}
      assert Resolution.rekey_term(term, m) == {:pi, {:data, :"Std.Nat#Nat", [], []}, {:data, :Other, [], []}}
    end
  end
end
