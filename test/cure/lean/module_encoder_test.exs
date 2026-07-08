defmodule Cure.Lean.ModuleEncoderTest do
  use ExUnit.Case, async: true

  alias Cure.Core.Env
  alias Cure.Lean.ModuleEncoder

  # single-endpoint motive M for the transport fixture: λx:Type1. Eq(Type1,x,x)
  defp transport_motive,
    do: {:lam, {:type, 1}, {:data, :Equivalent, [{:type, 1}], [{:var, 0}, {:var, 0}]}}

  test "encodes only the admitted Lean-core fragment" do
    env =
      Env.empty()
      |> Env.add_def(:id_type, {:pi, {:type, 0}, {:type, 0}}, {:lam, {:type, 0}, {:var, 0}}, [
        :present
      ])
      |> Env.add_def(
        :type_refl,
        {:data, :Equivalent, [{:type, 1}], [{:type, 0}, {:type, 0}]},
        {:ctor, :reflexive, [{:type, 0}]},
        []
      )
      |> Env.add_def(
        :local_refl,
        {:pi, {:type, 0}, {:data, :Equivalent, [{:type, 0}], [{:var, 0}, {:var, 0}]}},
        {:lam, {:type, 0}, {:ctor, :reflexive, [{:var, 0}]}},
        []
      )
      # The transport rides Cure Core's J/subst :case spelling (the primitive
      # {:rewrite} node retired, Phase C); the encoder canonicalizes it back to
      # the Lean-side rewrite IR.
      |> Env.add_def(
        :rewrite_id,
        {:data, :Equivalent, [{:type, 1}], [{:type, 0}, {:type, 0}]},
        {:app,
         {:case, {:ctor, :reflexive, [{:type, 0}]},
          {:lam, {:type, 1},
           {:lam, {:type, 1},
            {:lam, {:data, :Equivalent, [{:type, 1}], [{:var, 1}, {:var, 0}]},
             {:pi, {:app, transport_motive(), {:var, 2}}, {:app, transport_motive(), {:var, 2}}}}}},
          [
            {:reflexive, 1,
             {:lam, {:app, Cure.Elab.Subst.shift(transport_motive(), 1, 0), {:type, 0}}, {:var, 0}}}
          ]}, {:ctor, :reflexive, [{:type, 0}]}},
        []
      )

    assert {:ok, payload} = ModuleEncoder.from_env(env, only_defs: [:id_type, :local_refl, :type_refl, :rewrite_id])
    assert payload["families"] == []
    assert payload["builtins"] == []
    assert payload["certified"] == []
    assert Enum.map(payload["defs"], & &1["name"]) == ["id_type", "local_refl", "rewrite_id", "type_refl"]

    rewrite = Enum.find(payload["defs"], &(&1["name"] == "rewrite_id"))
    assert rewrite["type"]["node"] == "eq"
    assert rewrite["body"]["node"] == "rewrite"
    assert rewrite["body"]["proof"]["node"] == "refl"
    assert rewrite["body"]["motive"]["body"]["node"] == "eq"
  end

  test "rejects Cure-specific Core convenience nodes before the bridge" do
    rejected = [
      {:absurd},
      {:prim, :add, [{:var, 0}, {:var, 1}]},
      {:ctor, :Mk, []},
      {:data, :Nat, [], []},
      {:case, {:var, 0}, {:lam, {:type, 0}, {:type, 0}}, []},
      {:hole, "x"},
      {:int_type},
      {:float_lit, 1.0}
    ]

    for {term, idx} <- Enum.with_index(rejected) do
      env = Env.add_def(Env.empty(), :"bad_#{idx}", {:type, 0}, term, [])

      assert {:error, {:lean_core_rejected, %{reason: :unsupported_cure_core_node}}} =
               ModuleEncoder.from_env(env)
    end
  end

  test "rejects unsafe bare atom global names" do
    env = Env.add_def(Env.empty(), :bad_name, {:type, 0}, {:global, :"Std.Nat#Nat"}, [])

    assert {:error, {:lean_core_rejected, %{node: :global, reason: :unsafe_name}}} =
             ModuleEncoder.from_env(env)
  end

  test "rejects unbound local values even though local-context translation is supported" do
    env = Env.add_def(Env.empty(), :bad_refl, {:type, 0}, {:ctor, :reflexive, [{:var, 0}]}, [])

    assert {:ok, payload} = ModuleEncoder.from_env(env)

    assert [%{"body" => %{"node" => "refl", "value" => %{"node" => "var", "index" => 0}}}] = payload["defs"]
  end

  test "rejects unknown malformed rewrite nodes before the bridge" do
    env = Env.add_def(Env.empty(), :bad_rewrite, {:type, 0}, {:rewrite, {:type, 0}}, [])

    assert {:error, {:lean_core_rejected, %{node: :rewrite, reason: :unknown_core_node}}} =
             ModuleEncoder.from_env(env)
  end
end
