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
      term = {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:type, 0}},
              [{:Z, 0, {:var, 0}}, {:S, 1, {:ctor, :Z, []}}]}
      assert Resolution.rekey_term(term, m) ==
               {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), {:data, :"Std.Nat#Nat", [], []}, {:type, 0}},
                [{:"Std.Nat#Z", 0, {:var, 0}}, {:"Std.Nat#S", 1, {:ctor, :"Std.Nat#Z", []}}]}
    end

    test "leaves a :global untouched (functions keep bare names)", %{map: m} do
      assert Resolution.rekey_term({:global, :Z}, m) == {:global, :Z}
    end

    test "recurses through structural nodes and leaves unmapped atoms alone", %{map: m} do
      term = {:pi, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:data, :Other, [], []}}
      assert Resolution.rekey_term(term, m) == {:pi, Cure.Core.Grade.unrestricted(), {:data, :"Std.Nat#Nat", [], []}, {:data, :Other, [], []}}
    end
  end

  describe "rekey_module_env/3" do
    setup do
      # A tiny Std.Nat-shaped env: family Nat (nullary), ctors Z / S(Nat), and a
      # def `plus` that matches on Nat via a :case whose branch tags are Z / S.
      env =
        %Cure.Core.Env{}
        |> Cure.Core.Inductive.declare(
          Cure.Core.Inductive.family(:Nat, [], [], 0),
          [
            Cure.Core.Inductive.ctor(:Z, [], []),
            Cure.Core.Inductive.ctor(:S, [{:n, {:data, :Nat, [], []}}], [])
          ]
        )
        |> Cure.Core.Env.add_def(
          :plus,
          {:pi, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:data, :Nat, [], []}},
          {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:data, :Nat, [], []}},
           [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:ctor, :S, [{:var, 0}]}}]}
        )

      %{env: env}
    end

    test "moves family + ctor keys to :\"Mod#Name\" and repoints ctor_to_family", %{env: env} do
      out = Cure.Elab.Resolution.rekey_module_env(env, "Std.Nat", MapSet.new([:Nat]))

      assert Map.has_key?(out.families, :"Std.Nat#Nat")
      refute Map.has_key?(out.families, :Nat)
      assert out.families[:"Std.Nat#Nat"].name == :"Std.Nat#Nat"

      assert Map.has_key?(out.ctors, :"Std.Nat#Z")
      assert Map.has_key?(out.ctors, :"Std.Nat#S")
      refute Map.has_key?(out.ctors, :Z)
      assert out.ctor_to_family[:"Std.Nat#Z"] == :"Std.Nat#Nat"
      assert out.ctor_to_family[:"Std.Nat#S"] == :"Std.Nat#Nat"
    end

    test "rewrites embedded terms in ctor arg types", %{env: env} do
      out = Cure.Elab.Resolution.rekey_module_env(env, "Std.Nat", MapSet.new([:Nat]))
      assert [{:n, {:data, :"Std.Nat#Nat", [], []}}] = out.ctors[:"Std.Nat#S"].args
    end

    test "rewrites embedded terms in def bodies including :case branch tags", %{env: env} do
      out = Cure.Elab.Resolution.rekey_module_env(env, "Std.Nat", MapSet.new([:Nat]))
      body = out.defs[:plus].body
      assert {:case, _, _, [{:"Std.Nat#Z", 0, _}, {:"Std.Nat#S", 1, _}]} = body
      assert out.defs[:plus].type == {:pi, Cure.Core.Grade.unrestricted(), {:data, :"Std.Nat#Nat", [], []}, {:data, :"Std.Nat#Nat", [], []}}
    end

    test "leaves a non-owned family in the same env untouched", %{env: env} do
      env2 =
        Cure.Core.Inductive.declare(env, Cure.Core.Inductive.family(:Bool, [], [], 0),
          [Cure.Core.Inductive.ctor(:True, [], []), Cure.Core.Inductive.ctor(:False, [], [])])

      out = Cure.Elab.Resolution.rekey_module_env(env2, "Std.Nat", MapSet.new([:Nat]))
      assert Map.has_key?(out.families, :Bool)
      assert Map.has_key?(out.ctors, :True)
    end
  end

  describe "classify/2" do
    test "local declaration shadows a single imported owner: that import is a loser" do
      owners = %{Nat: MapSet.new(["Std.Nat"])}
      out = Cure.Elab.Resolution.classify(owners, MapSet.new([:Nat]))
      assert out.losers == %{"Std.Nat" => MapSet.new([:Nat])}
      assert out.ambiguous == MapSet.new()
    end

    test "one import owner, no local: NOT a collision (no re-key)" do
      owners = %{Nat: MapSet.new(["Std.Nat"])}
      out = Cure.Elab.Resolution.classify(owners, MapSet.new())
      assert out.losers == %{}
      assert out.ambiguous == MapSet.new()
    end

    test "same module owning a name (diamond dedup already applied): still ONE owner, no collision" do
      # Std.Vector's transitive Nat is attributed to Std.Nat by the AST scan, so
      # owners(Nat) = {Std.Nat} — a single owner even though reached two ways.
      owners = %{Nat: MapSet.new(["Std.Nat"]), Vector: MapSet.new(["Std.Vector"])}
      out = Cure.Elab.Resolution.classify(owners, MapSet.new())
      assert out.losers == %{}
      assert out.ambiguous == MapSet.new()
    end

    test "two distinct import owners, no local: ambiguous, both losers" do
      owners = %{Nat: MapSet.new(["Std.Foo", "Std.Bar"])}
      out = Cure.Elab.Resolution.classify(owners, MapSet.new())
      assert out.ambiguous == MapSet.new([:Nat])
      assert out.losers == %{"Std.Foo" => MapSet.new([:Nat]), "Std.Bar" => MapSet.new([:Nat])}
    end

    test "two distinct import owners WITH a local: local wins, both imports lose, not ambiguous" do
      owners = %{Nat: MapSet.new(["Std.Foo", "Std.Bar"])}
      out = Cure.Elab.Resolution.classify(owners, MapSet.new([:Nat]))
      assert out.ambiguous == MapSet.new()
      assert out.losers == %{"Std.Foo" => MapSet.new([:Nat]), "Std.Bar" => MapSet.new([:Nat])}
    end
  end

  describe "resolve_qualified/3" do
    setup do
      # env where Std.Nat has been re-keyed (loser), and an unshadowed Std.Bool.
      env =
        %Cure.Core.Env{}
        |> Cure.Core.Inductive.declare(Cure.Core.Inductive.family(:"Std.Nat#Nat", [], [], 0),
             [Cure.Core.Inductive.ctor(:"Std.Nat#Z", [], []),
              Cure.Core.Inductive.ctor(:"Std.Nat#S", [{:n, {:data, :"Std.Nat#Nat", [], []}}], [])])
        |> Cure.Core.Inductive.declare(Cure.Core.Inductive.family(:Bool, [], [], 0),
             [Cure.Core.Inductive.ctor(:True, [], []), Cure.Core.Inductive.ctor(:False, [], [])])

      %{env: env}
    end

    test "value path resolves a re-keyed ctor", %{env: env} do
      assert Cure.Elab.Resolution.resolve_qualified(env, "Std.Nat.Z", :value) == {:ok, :"Std.Nat#Z"}
    end

    test "type path resolves via module==typename collapse", %{env: env} do
      assert Cure.Elab.Resolution.resolve_qualified(env, "Std.Nat", :type) == {:ok, :"Std.Nat#Nat"}
    end

    test "type path resolves the explicit .Nat spelling identically", %{env: env} do
      assert Cure.Elab.Resolution.resolve_qualified(env, "Std.Nat.Nat", :type) == {:ok, :"Std.Nat#Nat"}
    end

    test "falls back to a bare key for an unshadowed module", %{env: env} do
      assert Cure.Elab.Resolution.resolve_qualified(env, "Std.Bool.True", :value) == {:ok, :True}
      assert Cure.Elab.Resolution.resolve_qualified(env, "Std.Bool", :type) == {:ok, :Bool}
    end

    test "returns :error for an unresolvable path", %{env: env} do
      assert Cure.Elab.Resolution.resolve_qualified(env, "Std.Nope.Gone", :value) == :error
    end
  end

  describe "ambiguous_modules/2" do
    test "reports ≥2 origins for a name re-keyed off the bare atom" do
      env =
        %Cure.Core.Env{}
        |> Cure.Core.Inductive.declare(Cure.Core.Inductive.family(:"Std.Foo#Nat", [], [], 0),
             [Cure.Core.Inductive.ctor(:"Std.Foo#FZero", [], [])])
        |> Cure.Core.Inductive.declare(Cure.Core.Inductive.family(:"Std.Bar#Nat", [], [], 0),
             [Cure.Core.Inductive.ctor(:"Std.Bar#BZero", [], [])])

      mods = Cure.Elab.Resolution.ambiguous_modules(env, :Nat)
      assert Enum.sort(mods) == ["Std.Bar", "Std.Foo"]
    end

    test "returns [] when a bare winner key is present" do
      env =
        %Cure.Core.Env{}
        |> Cure.Core.Inductive.declare(Cure.Core.Inductive.family(:Nat, [], [], 0), [])
        |> Cure.Core.Inductive.declare(Cure.Core.Inductive.family(:"Std.Bar#Nat", [], [], 0), [])

      assert Cure.Elab.Resolution.ambiguous_modules(env, :Nat) == []
    end
  end
end
