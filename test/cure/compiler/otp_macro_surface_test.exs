defmodule Cure.Compiler.OtpMacroSurfaceTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, OtpMacro, Parser}

  test "lift module parses behaviour and quoted callback bodies as pure data" do
    source = """
    lift module Cure.Generated.Worker
      behaviour GenServer
      callback init(arg: Int) -> arg
      callback handle_info(msg: Int, state: Int) -> state
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:lift_module, meta, []}} = Parser.parse(tokens, emit_events: false)
    assert meta[:module] == "Cure.Generated.Worker"
    assert meta[:behaviour] == :GenServer

    assert Enum.map(meta[:callbacks], &{&1.name, &1.arity}) == [
             {:init, 1},
             {:handle_info, 2}
           ]

    assert {:variable, _, "arg"} = hd(meta[:callbacks]).body

    assert {:ok, %{kind: :quoted_module, behaviour: :GenServer}} =
             OtpMacro.lift_module_ast({:lift_module, meta, []})
  end

  test "a transparent macro can substitute an identifier into lift module" do
    source = """
    mod M
      macro Lift
        syntax liftit <name: Identifier> becomes lift module name
      liftit Cure.Generated.Worker
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:container, _, children}} = Parser.parse(tokens, emit_events: false)
    assert {:lift_module, meta, []} = List.last(children)
    assert meta[:module] == "Cure.Generated.Worker"
  end

  test "lifted modules compile as independent units through the common emitter" do
    source = """
    mod Main
      lift module Cure.Generated.Worker
        behaviour GenServer
        callback init(arg: Int) -> arg
    """

    assert {:ok, main} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert main == :"Cure.Main"
    assert function_exported?(:"Cure.Generated.Worker", :init, 1)
    assert apply(:"Cure.Generated.Worker", :init, [42]) == 42
  end

  test "duplicate lifted module names are rejected before emission" do
    source = """
    mod Main
      lift module Cure.Generated.Worker
        behaviour GenServer
        callback init(arg: Int) -> arg
      lift module Cure.Generated.Worker
        behaviour GenServer
        callback init(arg: Int) -> arg
    """

    assert {:error, {:codegen_error, {:duplicate_lifted_module, "Cure.Generated.Worker"}}} =
             Cure.Compiler.compile_and_load(source, emit_events: false)
  end
end
