defmodule Cure.Kernel.BackendTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Kernel.Backend
  alias Cure.Types.Checker

  @lean_skip if System.find_executable("lean"), do: false, else: "lean executable not found"

  setup do
    previous_backend = Application.get_env(:cure, :kernel_backend)
    previous_env = System.get_env("CURE_KERNEL_BACKEND")

    on_exit(fn ->
      restore_app_env(:kernel_backend, previous_backend)
      restore_system_env("CURE_KERNEL_BACKEND", previous_env)
    end)

    Application.delete_env(:cure, :kernel_backend)
    System.delete_env("CURE_KERNEL_BACKEND")

    :ok
  end

  test "defaults to the existing Elixir core backend" do
    assert {:ok, :elixir_core} = Backend.selected_backend()
    assert {:ok, Cure.Kernel.Backend.ElixirCore} = Backend.backend_module()
  end

  test "option selection wins over config and environment" do
    Application.put_env(:cure, :kernel_backend, :elixir_core)
    System.put_env("CURE_KERNEL_BACKEND", "elixir_core")

    assert {:ok, :lean} = Backend.selected_backend(kernel_backend: :lean)
  end

  test "environment selection accepts string aliases" do
    System.put_env("CURE_KERNEL_BACKEND", "elixir-core")

    assert {:ok, :elixir_core} = Backend.selected_backend()
  end

  test "unknown backend is structured" do
    assert {:error, {:unknown_kernel_backend, "bogus"}} =
             Backend.selected_backend(kernel_backend: "bogus")
  end

  test "type checker forwards backend options for dependent modules" do
    ast =
      parse!("""
      mod BackendOption
        type Nat = Z | S(Nat)
        type Vec(a: Type) indices (n: Nat)
          empty : Vec(a, Z)
      end
      """)

    assert {:error, [{:dependent_type_error, message, [line: 0]}]} =
             Checker.check_module(ast, kernel_backend: "bogus", emit_events: false)

    assert message =~ "unknown_kernel_backend"
    assert message =~ "bogus"
  end

  @tag skip: @lean_skip
  test "CURE_KERNEL_BACKEND=lean makes the type checker use the Lean bridge" do
    System.put_env("CURE_KERNEL_BACKEND", "lean")

    ast =
      parse!("""
      mod LeanTiny
        fn id_type({A: Type}, x: A) -> A = x
      end
      """)

    assert {:ok, ^ast} = Checker.check_module(ast, emit_events: false)
  end

  test "lean backend does not use the Elixir core kernel as the admission gate" do
    ast =
      parse!("""
      mod LeanOnly
        fn old_kernel_rejects({A: Type}, x: A) -> Type = x
      end
      """)

    assert {:error, [{:dependent_type_error, old_kernel_message, [line: 0]}]} =
             Checker.check_module(ast, kernel_backend: :elixir_core, emit_events: false)

    assert old_kernel_message =~ "conversion_failure"

    bridge = fake_ok_bridge!()
    System.put_env("CURE_LEAN_BRIDGE", bridge)
    System.put_env("CURE_KERNEL_BACKEND", "lean")

    assert {:ok, ^ast} = Checker.check_module(ast, emit_events: false)
  end

  @tag skip: @lean_skip
  test "lean backend checks source rewrite through Lean transport" do
    ast =
      parse!("""
      mod LeanChecksRewrite
        fn bad({A: Type}, p: Eq(Type, A, A), x: A) -> A = rewrite p in x
      end
      """)

    System.put_env("CURE_KERNEL_BACKEND", "lean")

    assert {:ok, ^ast} = Checker.check_module(ast, emit_events: false)
  end

  defp restore_app_env(key, nil), do: Application.delete_env(:cure, key)
  defp restore_app_env(key, value), do: Application.put_env(:cure, key, value)

  defp restore_system_env(key, nil), do: System.delete_env(key)
  defp restore_system_env(key, value), do: System.put_env(key, value)

  defp parse!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  defp fake_ok_bridge! do
    path = Path.join(System.tmp_dir!(), "cure-lean-fake-#{System.unique_integer([:positive])}")

    File.write!(path, """
    #!/bin/sh
    printf '{"status":"ok","checked_by":"lean","protocol":1}\\n'
    """)

    File.chmod!(path, 0o755)
    path
  end
end
