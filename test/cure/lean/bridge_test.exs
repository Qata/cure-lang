defmodule Cure.Lean.BridgeTest do
  use ExUnit.Case, async: false

  alias Cure.Lean.Bridge

  @lean_skip if System.find_executable("lean"), do: false, else: "lean executable not found"

  setup do
    previous_executable = Application.get_env(:cure, :lean_bridge_executable)
    previous_lean4lean = Application.get_env(:cure, :lean4lean_path)
    previous_env_executable = System.get_env("CURE_LEAN_BRIDGE")
    previous_env_lean4lean = System.get_env("CURE_LEAN4LEAN_PATH")

    on_exit(fn ->
      restore_app_env(:lean_bridge_executable, previous_executable)
      restore_app_env(:lean4lean_path, previous_lean4lean)
      restore_system_env("CURE_LEAN_BRIDGE", previous_env_executable)
      restore_system_env("CURE_LEAN4LEAN_PATH", previous_env_lean4lean)
    end)

    Application.delete_env(:cure, :lean_bridge_executable)
    Application.delete_env(:cure, :lean4lean_path)
    System.delete_env("CURE_LEAN_BRIDGE")
    System.delete_env("CURE_LEAN4LEAN_PATH")

    :ok
  end

  test "reports a clear missing executable diagnostic" do
    path = "/definitely/missing/cure-lean-bridge"

    assert {:error, {:lean_bridge_unavailable, %{executable: ^path, reason: :enoent}}} =
             Bridge.health(lean_bridge_executable: path)
  end

  test "resolves lean4lean path from option before environment" do
    System.put_env("CURE_LEAN4LEAN_PATH", "/env/lean4lean")

    assert Bridge.lean4lean_path(lean4lean_path: "/opt/lean4lean") == "/opt/lean4lean"
  end

  test "exposes protocol version" do
    assert Bridge.protocol_version() == 1
  end

  @tag skip: @lean_skip
  test "checks a minimal Core module with Lean" do
    payload = %{
      "format" => "cure-core-v1",
      "families" => [],
      "defs" => [
        %{
          "name" => "idType",
          "type" => %{
            "node" => "pi",
            "dom" => %{"node" => "type", "level" => 0},
            "cod" => %{"node" => "type", "level" => 0}
          },
          "body" => %{
            "node" => "lam",
            "dom" => %{"node" => "type", "level" => 0},
            "body" => %{"node" => "var", "index" => 0}
          },
          "quantities" => nil
        }
      ],
      "certified" => [],
      "builtins" => []
    }

    assert {:ok, %{"checked_by" => "lean", "status" => "ok"}} = Bridge.check_module(payload)
  end

  @tag skip: @lean_skip
  test "checks native Lean equality and reflexivity" do
    payload = %{
      "format" => "cure-core-v1",
      "families" => [],
      "defs" => [
        %{
          "name" => "typeRefl",
          "type" => %{
            "node" => "eq",
            "type" => %{"node" => "type", "level" => 1},
            "lhs" => %{"node" => "type", "level" => 0},
            "rhs" => %{"node" => "type", "level" => 0}
          },
          "body" => %{"node" => "refl", "value" => %{"node" => "type", "level" => 0}},
          "quantities" => []
        }
      ],
      "certified" => [],
      "builtins" => []
    }

    assert {:ok, %{"checked_by" => "lean", "status" => "ok"}} = Bridge.check_module(payload)
  end

  @tag skip: @lean_skip
  test "checks reflexivity over a local binder" do
    payload = %{
      "format" => "cure-core-v1",
      "families" => [],
      "defs" => [
        %{
          "name" => "localRefl",
          "type" => %{
            "node" => "pi",
            "dom" => %{"node" => "type", "level" => 0},
            "cod" => %{
              "node" => "eq",
              "type" => %{"node" => "type", "level" => 0},
              "lhs" => %{"node" => "var", "index" => 0},
              "rhs" => %{"node" => "var", "index" => 0}
            }
          },
          "body" => %{
            "node" => "lam",
            "dom" => %{"node" => "type", "level" => 0},
            "body" => %{"node" => "refl", "value" => %{"node" => "var", "index" => 0}}
          },
          "quantities" => []
        }
      ],
      "certified" => [],
      "builtins" => []
    }

    assert {:ok, %{"checked_by" => "lean", "status" => "ok"}} = Bridge.check_module(payload)
  end

  @tag skip: @lean_skip
  test "checks closed native Lean equality transport for rewrite" do
    payload = %{
      "format" => "cure-core-v1",
      "families" => [],
      "defs" => [
        %{
          "name" => "rewriteClosed",
          "type" => %{
            "node" => "eq",
            "type" => %{"node" => "type", "level" => 1},
            "lhs" => %{"node" => "type", "level" => 0},
            "rhs" => %{"node" => "type", "level" => 0}
          },
          "body" => %{
            "node" => "rewrite",
            "proof" => %{"node" => "refl", "value" => %{"node" => "type", "level" => 0}},
            "motive" => %{
              "node" => "lam",
              "dom" => %{"node" => "type", "level" => 1},
              "body" => %{
                "node" => "eq",
                "type" => %{"node" => "type", "level" => 1},
                "lhs" => %{"node" => "var", "index" => 0},
                "rhs" => %{"node" => "var", "index" => 0}
              }
            },
            "body" => %{
              "node" => "refl",
              "value" => %{"node" => "type", "level" => 0}
            }
          },
          "quantities" => []
        }
      ],
      "certified" => [],
      "builtins" => []
    }

    assert {:ok, %{"checked_by" => "lean", "status" => "ok"}} = Bridge.check_module(payload)
  end

  defp restore_app_env(key, nil), do: Application.delete_env(:cure, key)
  defp restore_app_env(key, value), do: Application.put_env(:cure, key, value)

  defp restore_system_env(key, nil), do: System.delete_env(key)
  defp restore_system_env(key, value), do: System.put_env(key, value)
end
