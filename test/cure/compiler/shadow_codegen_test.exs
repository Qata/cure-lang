defmodule Cure.Compiler.ShadowCodegenTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Codegen

  test "a qualified nullary constructor call compiles to the same tagged tuple as its bare form" do
    {:ok, qualified_form} = Codegen.compile_expr({:function_call, [name: "Std.Nat.Z"], []})
    {:ok, bare_form} = Codegen.compile_expr({:function_call, [name: "Z"], []})

    assert qualified_form == bare_form
    assert {:tuple, _line, [{:atom, _, :z}]} = qualified_form
  end

  test "a qualified constructor call with args compiles to a tagged tuple, not a remote call" do
    {:ok, form} =
      Codegen.compile_expr({:function_call, [name: "Std.Nat.S"], [{:function_call, [name: "Std.Nat.Z"], []}]})

    assert {:tuple, _line, [{:atom, _, :s}, {:tuple, _, [{:atom, _, :z}]}]} = form
  end

  test "a qualified NON-constructor call (lowercase tail) is still a remote call, unchanged" do
    {:ok, form} = Codegen.compile_expr({:function_call, [name: "Std.Nat.plus"], []})
    assert {:call, _line, {:remote, _, {:atom, _, _mod}, {:atom, _, :plus}}, []} = form
  end

  test "an FFI call with a PascalCase tail (Erlang.Length) stays a remote call, NOT a tuple" do
    {:ok, form} = Codegen.compile_expr({:function_call, [name: "Erlang.Length"], [{:literal, [], []}]})
    assert {:call, _line, {:remote, _, {:atom, _, :erlang}, {:atom, _, :length}}, _} = form
  end

  test "a program using Std.Nat.Z compiles to a module with a bare :z tag, not a dotted/remote artifact" do
    src = """
    mod EscapeCodegen
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn imported_zero() -> Std.Nat = Std.Nat.Z()
    end
    """

    {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
    {:ok, forms} = Codegen.compile_module(ast, emit_events: false)

    dump = inspect(forms)
    refute String.contains?(dump, "Std.Nat.Z")
    refute String.contains?(dump, "#")
    assert String.contains?(dump, ":z}")
  end
end
