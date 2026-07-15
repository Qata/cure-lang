defmodule Cure.Compiler.DeclarationMacroExpansionTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  @source """
  mod M
    use Std.Syntax

    macro Make
      syntax make <x: Code> computed by id

    fn id(input: MakeSyntax) -> Syntax = input.x

    make lift module Cure.DeclarationMacroActor
      behaviour gen_server
      callback init(initial: Int) returns Effect(Tuple(Atom, Int)) = %[:ok, initial]
  end
  """

  test "a computed declaration expands before lifted modules are collected" do
    assert {:ok, module} = Cure.Compiler.compile_and_load(@source, emit_events: false)
    assert module == :"Cure.M"
    assert apply(:"Cure.DeclarationMacroActor", :init, [7]) == {:ok, 7}
  end

  test "the declaration pass does not consume computed uses in function bodies" do
    source = """
    mod M
      use Std.Syntax
      use Std.List

      macro Mk
        syntax mk computed by build

      fn build(input: Syntax) -> Syntax =
        Leaf(:literal, [KV(:subtype, SAtom(:integer))], SInt(1))

      fn f() -> Int = mk
    end
    """

    assert {:ok, ast} = Cure.Compiler.parse_source(source)
    assert {:ok, expanded} = Program.expand_declaration_uses(ast)
    assert find_computed_use(expanded)
  end

  test "repeated computed holes are typed and reflected as List(Syntax)" do
    source = """
    mod M
      use Std.Syntax

      macro Gather
        syntax gather <items: Code>... computed by build

      fn build(input: GatherSyntax) -> Syntax =
        match input.items
          [] -> Leaf(:literal, [KV(:subtype, SAtom(:integer))], SInt(0))
          [_ | _] -> Leaf(:literal, [KV(:subtype, SAtom(:integer))], SInt(1))

      fn result() -> Int = gather 1 2 3
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :result, []) == 1
  end

  test "a structured family lowers to nested syntax records and expands" do
    source = """
    mod M
      use Std.Syntax

      macro actor <name: ModuleName>
        syntax family ActorDefinition
          state Type
          optional initial Expression
        accepts ActorDefinition
        expands with derive_actor

      fn derive_actor(input: ActorSyntax) -> Syntax = input.definition.initial

      fn result() -> Int = actor Counter
        state Int
        initial 7
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :result, []) == 7
  end

  test "a structured expander may receive leading captures directly" do
    source = """
    mod M
      use Std.Syntax

      macro actor <name: ModuleName>
        syntax family ActorDefinition
          state Type
          optional initial Expression
        accepts ActorDefinition
        expands with derive_actor

      fn derive_actor(name: Syntax, definition: ActorDefinitionSyntax) -> Syntax = definition.initial

      fn result() -> Int = actor Counter
        state Int
        initial 9
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :result, []) == 9
  end

  test "absent optional computed holes retain their reflected field slot" do
    source = """
    mod M
      use Std.Syntax

      macro Optional
        syntax opt (<value: Code>)? computed by identity

      fn identity(input: OptSyntax) -> Syntax = Leaf(:literal, [KV(:subtype, SAtom(:integer))], SInt(0))
      fn result() -> Syntax = opt
    end
    """

    assert {:ok, ast} = Cure.Compiler.parse_source(source)
    assert {:ok, [nil]} = find_computed_input(ast)
  end

  defp find_computed_input({:computed_use, _meta, [_elab, {:macro_input, _input_meta, children}]}),
    do: {:ok, children}

  defp find_computed_input({:function_def, _meta, body}), do: find_computed_input(body)

  defp find_computed_input({_tag, _meta, children}) when is_list(children) do
    Enum.find_value(children, :not_found, fn child ->
      case find_computed_input(child) do
        :not_found -> nil
        result -> result
      end
    end)
  end

  defp find_computed_input(list) when is_list(list) do
    Enum.find_value(list, :not_found, fn child ->
      case find_computed_input(child) do
        :not_found -> nil
        result -> result
      end
    end)
  end

  defp find_computed_input(_other), do: :not_found

  defp find_computed_use({:computed_use, _meta, _children}), do: true
  defp find_computed_use({:function_def, _meta, body}), do: find_computed_use(body)

  defp find_computed_use({_tag, _meta, children}) when is_list(children),
    do: Enum.any?(children, &find_computed_use/1)

  defp find_computed_use(list) when is_list(list), do: Enum.any?(list, &find_computed_use/1)
  defp find_computed_use(_other), do: false
end
