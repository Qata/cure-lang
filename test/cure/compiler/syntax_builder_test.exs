defmodule Cure.Compiler.SyntaxBuilderTest do
  use ExUnit.Case, async: false

  @source """
  mod M
    use Std.Syntax

    fn tag_of() -> Atom = tag(Node(:sample, [], []))

    fn quoted_children() -> List(Syntax) =
      children(Quoted(Leaf(:literal, [], SInt(1))))

    fn find_name() -> AttrResult =
      attr([KV(:other, SInt(0)), KV(:name, SStr("worker"))], :name)

    fn build_node() -> Syntax =
      node(:generated, [attr_value(:kind, syntax_atom(:actor))], [])
  """

  test "source-level syntax helpers analyze and construct reflected syntax" do
    assert {:ok, module} = Cure.Compiler.compile_and_load(@source, emit_events: false)

    assert apply(module, :tag_of, []) == :sample

    assert apply(module, :quoted_children, []) == [
             {:Leaf, :literal, [], {:SInt, 1}}
           ]

    assert apply(module, :find_name, []) == {:Found, {:SStr, String.to_charlist("worker")}}

    assert apply(module, :build_node, []) ==
             {:Node, :generated, [{:KV, :kind, {:SAtom, :actor}}], []}
  end
end
