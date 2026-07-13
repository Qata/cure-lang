defmodule Cure.Compiler.OtpMacroSurfaceTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, LiftModule, OtpMacro, Parser}

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
        syntax liftit <name: ModuleName> becomes lift module name
          behaviour GenServer
      liftit Cure.Generated.Worker
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:container, _, children}} = Parser.parse(tokens, emit_events: false)
    assert {:lift_module, meta, []} = List.last(children)
    assert meta[:module] == "Cure.Generated.Worker"
    assert meta[:source_provenance].file == "nofile"
  end

  test "a transparent macro parses a raw body splice into ordinary declarations" do
    source = """
    mod M
      macro Lift
        syntax one becomes 42
        syntax liftit <name: ModuleName> <body: raw until dedent> becomes lift module name
          behaviour GenServer
          body
      liftit Cure.Generated.Worker
        fn init(arg: Int) -> Int = one
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:container, _, children}} = Parser.parse(tokens, emit_events: false)
    assert {:lift_module, meta, []} = List.last(children)
    assert meta[:module] == "Cure.Generated.Worker"
    assert [{:function_def, function_meta, [{:literal, _, 42}]}] = meta[:declarations]
    assert function_meta[:name] == "init"
  end

  test "a transparent macro can compile a parsed raw body splice" do
    source = """
    mod Main
      macro Lift
        syntax one becomes 42
        syntax liftit <name: ModuleName> <body: raw until dedent> becomes lift module name
          behaviour GenServer
          body
      liftit Cure.Generated.Worker
        fn init(arg: Int) -> Int = one
    """

    assert {:ok, main} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert main == :"Cure.Main"
    assert function_exported?(:"Cure.Generated.Worker", :init, 1)
    assert apply(:"Cure.Generated.Worker", :init, [42]) == 42
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

  test "lifted modules are ordered after generated modules they import" do
    source = """
    mod Main
      lift module Cure.Generated.Root
        behaviour GenServer
        use Cure.Generated.Worker
        callback init(arg: Int) -> arg
      lift module Cure.Generated.Worker
        behaviour GenServer
        callback init(arg: Int) -> arg
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, emit_events: false)
    assert {:ok, requests} = LiftModule.collect(ast)
    assert Enum.map(requests, & &1.module) == ["Cure.Generated.Worker", "Cure.Generated.Root"]
    assert [root] = Enum.filter(requests, &(&1.module == "Cure.Generated.Root"))
    assert root.dependencies == ["Cure.Generated.Worker"]
  end

  test "lifted module dependency cycles are rejected before emission" do
    ast =
      {:container, [],
       [
         {:lift_module,
          [module: "Cure.A", behaviour: :GenServer, callbacks: [], declarations: [{:import, [source: "Cure.B"], []}]],
          []},
         {:lift_module,
          [module: "Cure.B", behaviour: :GenServer, callbacks: [], declarations: [{:import, [source: "Cure.A"], []}]],
          []}
       ]}

    assert {:error, {:lifted_module_dependency_cycle, _}} = LiftModule.collect(ast)
  end
end
