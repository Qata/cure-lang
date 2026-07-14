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

  defp find_computed_use({:computed_use, _meta, _children}), do: true
  defp find_computed_use({:function_def, _meta, body}), do: find_computed_use(body)

  defp find_computed_use({_tag, _meta, children}) when is_list(children),
    do: Enum.any?(children, &find_computed_use/1)

  defp find_computed_use(list) when is_list(list), do: Enum.any?(list, &find_computed_use/1)
  defp find_computed_use(_other), do: false
end
