defmodule Cure.Compiler.UnionParseTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  # Collect every {tag, meta, children} 3-tuple in the AST.
  defp collect(node, acc) do
    acc = if is_tuple(node) and tuple_size(node) == 3, do: [node | acc], else: acc

    cond do
      is_tuple(node) -> Enum.reduce(Tuple.to_list(node), acc, &collect/2)
      is_list(node) -> Enum.reduce(node, acc, &collect/2)
      true -> acc
    end
  end

  defp find_union(ast) do
    collect(ast, []) |> Enum.find(&match?({:union_type, _, _}, &1))
  end

  describe "union types in type-expression position" do
    test "parses a two-member union in a parameter annotation" do
      ast = parse!("mod M\n  fn f(x: Int | String) -> Int = 1\nend\n")

      assert {:union_type, [], [a, b]} = find_union(ast)
      assert {:variable, _, "Int"} = a
      assert {:variable, _, "String"} = b
    end

    test "parses a three-member union in a return annotation" do
      ast = parse!("mod M\n  fn f(x: Int) -> Int | String | Bool = 1\nend\n")
      assert {:union_type, [], members} = find_union(ast)
      assert length(members) == 3
    end

    test "parses literal members" do
      ast = parse!("mod M\n  fn f(x: 3 | :north | \"s\") -> Int = 1\nend\n")

      assert {:union_type, [], [i, s, str]} = find_union(ast)
      assert {:literal, m1, 3} = i
      assert m1[:subtype] == :integer
      assert {:literal, m2, :north} = s
      assert m2[:subtype] == :symbol
      assert {:literal, m3, "s"} = str
      assert m3[:subtype] == :string
    end

    test "parses an applied type as a member" do
      ast = parse!("mod M\n  fn f(x: List(Int) | Int) -> Int = 1\nend\n")
      assert {:union_type, [], [{:function_call, fm, _}, {:variable, _, "Int"}]} = find_union(ast)
      assert fm[:name] == "List"
    end

    test "allows a leading bar" do
      ast = parse!("mod M\n  typealias P = | Int | String\nend\n")
      assert {:union_type, [], members} = find_union(ast)
      assert length(members) == 2
    end

    test "binds LOOSER than -> : `A -> B | C` is `(A -> B) | C`" do
      ast = parse!("mod M\n  typealias P = Int -> Bool | String\nend\n")

      assert {:union_type, [], [arrow, {:variable, _, "String"}]} = find_union(ast)
      assert {:function_call, am, _} = arrow
      assert am[:function_type] == true
    end

    test "parses a union nested in a type argument" do
      ast = parse!("mod M\n  fn f(m: Map(String, Int | Bool)) -> Int = 1\nend\n")
      assert {:union_type, [], members} = find_union(ast)
      assert length(members) == 2
    end

    test "parses a parenthesised union in domain position" do
      ast = parse!("mod M\n  typealias P = (Int | String) -> Bool\nend\n")
      assert {:union_type, [], members} = find_union(ast)
      assert length(members) == 2
    end
  end

  describe "regression: `|` in ADT declaration bodies still means constructor alternatives" do
    test "plain enum is unaffected" do
      ast = parse!("mod M\n  type Color = Red | Green | Blue\nend\n")
      assert find_union(ast) == nil
    end

    test "enum whose first variant is parenthesised-arrow-shaped is unaffected" do
      ast = parse!("mod M\n  type Handler = Cb(Int) | Nope\nend\n")
      assert find_union(ast) == nil

      assert {:container, meta, variants} =
               ast |> collect([]) |> Enum.find(&match?({:container, _, _}, &1))

      assert meta[:container_type] == :enum
      assert length(variants) == 2
    end

    test "the empty type `type Empty = |` still parses" do
      ast = parse!("mod M\n  type Empty = |\nend\n")
      assert find_union(ast) == nil
    end
  end
end
