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

    fn context_name() -> AttrResult =
      context_attr(
        Node(:sample, [attr_value(:expansion_context, SSyntax(Node(:callback_context, [KV(:callback, SAtom(:handle_cast))], [])))], []),
        :callback
      )

    fn build_node() -> Syntax =
      node(:generated, [attr_value(:kind, syntax_atom(:actor))], [])

    fn build_literals() -> List(Syntax) = [int_literal(7), float_literal(2.5), bool_literal(true), string_literal("ok"), atom_literal(:ready)]
  """

  test "source-level syntax helpers analyze and construct reflected syntax" do
    assert {:ok, module} = Cure.Compiler.compile_and_load(@source, emit_events: false)

    assert apply(module, :tag_of, []) == :sample

    assert apply(module, :quoted_children, []) == [
             {:Leaf, :literal, [], {:SInt, 1}}
           ]

    assert apply(module, :find_name, []) == {:Found, {:SStr, String.to_charlist("worker")}}

    assert apply(module, :context_name, []) == {:Found, {:SAtom, :handle_cast}}

    assert apply(module, :build_node, []) ==
             {:Node, :generated, [{:KV, :kind, {:SAtom, :actor}}], []}

    assert apply(module, :build_literals, []) == [
             {:Leaf, :literal, [{:KV, :subtype, {:SAtom, :integer}}], {:SInt, 7}},
             {:Leaf, :literal, [{:KV, :subtype, {:SAtom, :float}}], {:SFloat, 2.5}},
             {:Leaf, :literal, [{:KV, :subtype, {:SAtom, :boolean}}], {:SBool, true}},
             {:Leaf, :literal, [{:KV, :subtype, {:SAtom, :string}}], {:SStr, ~c"ok"}},
             {:Leaf, :literal, [{:KV, :subtype, {:SAtom, :symbol}}], {:SAtom, :ready}}
           ]
  end

  test "raw syntax construction is available only through an explicit unsafe API" do
    source = """
    mod M
      use Std.Syntax
      use Std.Syntax.Raw

      fn build_raw() -> Syntax = unsafe_node(:raw, [], [unsafe_leaf(:value, [], SInt(1))])
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)

    assert apply(module, :build_raw, []) ==
             {:Node, :raw, [], [{:Leaf, :value, [], {:SInt, 1}}]}
  end
end
