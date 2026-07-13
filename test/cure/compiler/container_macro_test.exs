defmodule Cure.Compiler.ContainerMacroTest do
  use ExUnit.Case, async: false

  @containers [
    {"actor", "Cure.TestActor", :start_link, [0]},
    {"fsm", "Cure.TestFsm", :start_link, [0]},
    {"sup", "Cure.TestSup", :start_link, []},
    {"app", "Cure.TestApp", :start, [:normal, []]}
  ]

  test "the four OTP surfaces are auto-preluded syntax macros" do
    for {keyword, name, _fun, _args} <- @containers do
      source = "#{keyword} #{name}\n"
      assert {:ok, ast} = Cure.Compiler.parse_source(source, file: "container_macro.cure")

      case keyword do
        "sup" ->
          assert {:lift_module, meta, []} = ast
          assert meta[:module] == name

        _ ->
          assert {:container, meta, []} = ast
          assert Keyword.get(meta, :macro_generated)
          assert Keyword.get(meta, :name) == name
      end
    end
  end

  test "a raw container body is parsed by the ordinary parser" do
    assert {:ok, {:lift_module, meta, []}} =
             Cure.Compiler.parse_source("sup Cure.Body\n  strategy = :one_for_all\n", file: "body.cure")

    assert meta[:module] == "Cure.Body"
    assert Enum.any?(meta[:declarations], &match?({:assignment, _, _}, &1))
  end

  test "generic lowering emits runnable OTP modules for every container kind" do
    for {keyword, name, fun, args} <- @containers do
      source = "#{keyword} #{name}\n"
      assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)

      expected_module =
        if keyword == "sup", do: String.to_atom(name), else: Module.concat(String.split(name, "."))

      assert module == expected_module
      assert match?({:ok, _}, apply(module, fun, args))
    end
  end

  test "no per-container compiler modules remain in the lowering path" do
    refute Code.ensure_loaded?(Cure.Actor.Compiler)
    refute Code.ensure_loaded?(Cure.FSM.Compiler)
    refute Code.ensure_loaded?(Cure.Sup.Compiler)
    refute Code.ensure_loaded?(Cure.App.Compiler)
    assert function_exported?(Cure.Compiler.ContainerMacro, :forms, 1)
  end
end
