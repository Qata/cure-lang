defmodule Cure.MetaAST.ConformanceTest do
  use ExUnit.Case, async: true

  alias Cure.MetaAST.Conformance

  # A canonical leaf node used as a stand-in subterm throughout.
  defp var(name), do: {:variable, [scope: :local], name}

  describe "compliant AST (the C2 target shape)" do
    test "a node with only scalars in meta and every subterm in children is conformant" do
      # This is exactly the invariant's end-state: meta holds line/col/scope, and
      # scrutinee + arms + their patterns/bodies all live in children as wrapper
      # nodes. `pattern_match` in the real tree already looks like this.
      ast =
        {:pattern_match, [line: 1, col: 1],
         [
           var("x"),
           {:match_arm, [line: 2],
            [
              {:pattern, [], [{:literal, [subtype: :integer], 0}]},
              {:body, [], [{:literal, [subtype: :integer], 1}]}
            ]}
         ]}

      assert Conformance.conformant?(ast)
      assert Conformance.violations(ast) == []
      assert Conformance.violation_buckets(ast) == MapSet.new()
    end

    test "primitives and empty children are conformant" do
      assert Conformance.conformant?({:nil_lit, [], []})
      assert Conformance.conformant?(42)
      assert Conformance.conformant?(:ok)
      assert Conformance.conformant?("string")
    end
  end

  describe ":node_in_meta — canonical node hiding a subterm in meta" do
    test "param with its type parked under :type" do
      ast = {:param, [type: var("Nat")], "x"}

      assert [%{kind: :node_in_meta, tag: :param, key: :type}] = Conformance.violations(ast)
      refute Conformance.conformant?(ast)
    end

    test "function_def flags both :params and :return_type, not the scalars" do
      ast =
        {:function_def,
         [
           return_type: var("Nat"),
           name: "f",
           params: [{:param, [], ["x"]}],
           visibility: :public,
           arity: 1,
           line: 1,
           col: 3
         ], [var("x")]}

      buckets = Conformance.violation_buckets(ast)
      assert MapSet.member?(buckets, {:node_in_meta, :function_def, :return_type})
      assert MapSet.member?(buckets, {:node_in_meta, :function_def, :params})
      # name/visibility/arity/line/col are scalars — never flagged.
      refute Enum.any?(Conformance.violations(ast), &(&1.key in [:name, :visibility, :arity, :line, :col]))
    end

    test "match_arm with its pattern in meta" do
      ast = {:match_arm, [pattern: var("Pat")], [var("body")]}
      assert [%{kind: :node_in_meta, tag: :match_arm, key: :pattern}] = Conformance.violations(ast)
    end

    test "a subterm nested deeper in meta is still reached" do
      # param whose type is itself a node with a further node in ITS meta.
      inner = {:param, [type: var("Bool")], "y"}
      ast = {:outer, [thing: inner], []}

      buckets = Conformance.violation_buckets(ast)
      assert MapSet.member?(buckets, {:node_in_meta, :outer, :thing})
      assert MapSet.member?(buckets, {:node_in_meta, :param, :type})
    end
  end

  describe ":bad_shape — non-canonical tuple that hides a node" do
    test "named_implicit_pat (4-tuple)" do
      ast = {:named_implicit_pat, [line: 1], "k", var("m")}
      assert [%{kind: :bad_shape, tag: :named_implicit_pat, arity: 4}] = Conformance.violations(ast)
    end

    test "named_dom (name where meta belongs)" do
      ast = {:named_dom, "x", var("Nat")}
      assert [%{kind: :bad_shape, tag: :named_dom, arity: 3}] = Conformance.violations(ast)
    end

    test "arrow_chain (2-tuple)" do
      ast = {:arrow_chain, [var("A"), var("B")]}
      assert [%{kind: :bad_shape, tag: :arrow_chain, arity: 2}] = Conformance.violations(ast)
    end

    test "group and builtin (2-tuples)" do
      assert [%{kind: :bad_shape, tag: :group}] = Conformance.violations({:group, [var("x")]})
      assert [%{kind: :bad_shape, tag: :builtin}] = Conformance.violations({:builtin, var("Int")})
    end
  end

  describe ":node_child — canonical node whose children slot is a bare node" do
    test "a single node in the children slot instead of a one-element list" do
      # Metastatic's traverse_children only recurses `is_list` children; a bare
      # node in the slot hits the fallback and is passed through as a leaf, so its
      # whole subtree is lost. The invariant is that children is ALWAYS a list.
      ast = {:wrapper, [line: 1], var("inner")}

      assert [%{kind: :node_child, tag: :wrapper, key: nil}] = Conformance.violations(ast)
      refute Conformance.conformant?(ast)
    end

    test "gadt_ctor's bare arrow_chain child is a non-list children slot" do
      # gadt_ctor is canonical, but its children slot holds a bare arrow_chain
      # tuple, not a list — so the whole constructor domain chain is lost. Flagged
      # at the parent (its children must be a list), NOT as a bad_shape arrow_chain.
      ast = {:gadt_ctor, [name: "C"], {:arrow_chain, [var("A"), var("B")]}}

      assert [%{kind: :node_child, tag: :gadt_ctor, key: nil}] = Conformance.violations(ast)
    end

    test "the subterms under a bare-node child are still descended for deeper defects" do
      # wrapper's child is a bare arrow_chain whose domain is itself a param with a
      # type parked in meta — the node_child flag does not stop the walk.
      ast = {:wrapper, [], {:arrow_chain, [{:param, [type: var("A")], "x"}]}}

      buckets = Conformance.violation_buckets(ast)
      assert MapSet.member?(buckets, {:node_child, :wrapper, nil})
      assert MapSet.member?(buckets, {:node_in_meta, :param, :type})
    end
  end

  describe "no false positives on opaque leaf data" do
    test "an MFA tuple in a child slot is not a node and is not flagged" do
      ast = {:extern_call, [], [{:erlang, :length, 1}, var("xs")]}
      assert Conformance.conformant?(ast)
    end

    test "a decorator argument holding only atoms/ints is not flagged" do
      ast = {:container, [], [{:group_ref, :core, 1}, var("body")]}
      assert Conformance.conformant?(ast)
    end

    test "trivia (comment) wide tuples are ignored" do
      assert Conformance.conformant?({:comment, "note", 1, 2, 3})
      assert Conformance.conformant?({:doc_comment, "doc", 1})
    end

    test "meta scalars do not trip the node_in_meta gate" do
      ast = {:thing, [name: "f", scope: :local, subtype: :integer, arity: 2], [var("x")]}
      assert Conformance.conformant?(ast)
    end

    test "a leaf node's scalar value in the children slot is not a node_child" do
      # variable/literal legitimately carry a non-list scalar in the children slot;
      # it hides no node, so the node_child gate must not fire.
      assert Conformance.conformant?({:variable, [scope: :local], "x"})
      assert Conformance.conformant?({:literal, [subtype: :integer], 42})
    end

    test "an opaque non-list children slot (holds no node) is not a node_child" do
      ast = {:extern_ref, [], {:erlang, :length, 1}}
      assert Conformance.conformant?(ast)
    end
  end

  describe "mixed AST and reporting" do
    test "violation_buckets collapses repeated occurrences to distinct buckets" do
      ast =
        {:mod, [],
         [
           {:param, [type: var("A")], "x"},
           {:param, [type: var("B")], "y"},
           {:match_arm, [pattern: var("P")], [var("b")]}
         ]}

      assert Conformance.violation_buckets(ast) ==
               MapSet.new([
                 {:node_in_meta, :param, :type},
                 {:node_in_meta, :match_arm, :pattern}
               ])
    end

    test "describe renders both kinds" do
      ast =
        {:mod, [],
         [
           {:param, [type: var("A")], "x"},
           {:arrow_chain, [var("A"), var("B")]}
         ]}

      out = ast |> Conformance.violations() |> Conformance.describe()
      assert out =~ "node_in_meta"
      assert out =~ "bad_shape"
      assert Conformance.describe([]) == "no MetaAST-conformance violations"
    end
  end

  describe "against the real parser" do
    alias Cure.Compiler.{Lexer, Parser}

    test "a parsed function surfaces param :type, function_def :params/:return_type" do
      {:ok, toks} = Lexer.tokenize("mod M\n  fn f(x: Nat) -> Nat = x\n", emit_events: false)
      {:ok, ast} = Parser.parse(toks, emit_events: false)

      buckets = Conformance.violation_buckets(ast)
      assert MapSet.member?(buckets, {:node_in_meta, :param, :type})
      assert MapSet.member?(buckets, {:node_in_meta, :function_def, :params})
      assert MapSet.member?(buckets, {:node_in_meta, :function_def, :return_type})
    end
  end
end
