defmodule Cure.Elab.DerivingTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  # A module carrying the `Equatable`/`Ord` interfaces, their primitive `Int`
  # instances, and a recursive `Tree` that derives both. `extra` appends the
  # per-test probe functions. The interface methods (`eq`/`lt`) are invoked
  # DIRECTLY — never `==`/`<` — so the call routes through instance resolution
  # (Task 4) and goes red with `{:no_instance, …}` until deriving generates the
  # `Tree` instance. A `==`-phrased test would evaluate on BEAM's native `==`
  # with no instance at all and never go red.
  defp tree_src(extra) do
    """
    mod DT
      interface Equatable(a)
        fn eq(x: a, y: a) -> Bool
      interface Ord(a)
        fn lt(x: a, y: a) -> Bool
      implementation Equatable for Int
        fn eq(x: Int, y: Int) -> Bool = x == y
      implementation Ord for Int
        fn lt(x: Int, y: Int) -> Bool = x < y
      type Tree = Leaf | Node(Tree, Int, Tree) deriving Equatable, Ord
    #{extra}
    end
    """
  end

  defp load(src, probes) do
    {:ok, env} = Program.elaborate(src)
    functions = Enum.uniq(probes ++ Program.impl_def_names(env))
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.DT", functions: functions)
    m
  end

  test "derived Equatable on a recursive ADT: equal → true, unequal → false" do
    src =
      tree_src("""
        fn t1() -> Tree = Node(Leaf, 1, Node(Leaf, 2, Leaf))
        fn t2() -> Tree = Node(Leaf, 1, Node(Leaf, 2, Leaf))
        fn t3() -> Tree = Node(Leaf, 1, Node(Leaf, 9, Leaf))
        fn eqSame() -> Bool = eq(t1(), t2())
        fn eqDiff() -> Bool = eq(t1(), t3())
      """)

    m = load(src, [:eqSame, :eqDiff, :t1, :t2, :t3])
    assert apply(m, :eqSame, []) == true
    assert apply(m, :eqDiff, []) == false
  end

  test "derived Ord: orders by constructor then field, lexicographically" do
    src =
      tree_src("""
        fn ctorOrder() -> Bool = lt(Leaf, Node(Leaf, 1, Leaf))
        fn ctorOrderRev() -> Bool = lt(Node(Leaf, 1, Leaf), Leaf)
        fn fieldLt() -> Bool = lt(Node(Leaf, 1, Leaf), Node(Leaf, 2, Leaf))
        fn fieldGt() -> Bool = lt(Node(Leaf, 2, Leaf), Node(Leaf, 1, Leaf))
      """)

    m = load(src, [:ctorOrder, :ctorOrderRev, :fieldLt, :fieldGt])
    assert apply(m, :ctorOrder, []) == true
    assert apply(m, :ctorOrderRev, []) == false
    assert apply(m, :fieldLt, []) == true
    assert apply(m, :fieldGt, []) == false
  end

  # `Show` renders to `String`, but the dependent pipeline has neither a `String`
  # surface type nor string concatenation / `Int → String` yet (both arrive with
  # the String value surface, #27/#29). The blocker is upstream of deriving —
  # even *declaring* `interface Show(a) … -> String` fails to resolve `String` —
  # so `deriving Show` is fully out of reach until that lands. `Deriving.generate`
  # reports the specific blocker at its own layer; adding `Show` is then a
  # one-clause change and this test is retired.
  test "deriving Show is an honest, specific blocker (needs string primitives)" do
    {:ok, env} = Program.elaborate("mod E\n  type Unit = MkUnit\nend")

    assert {:error, {:deriving_needs_strings, :Show}} =
             Cure.Elab.Deriving.generate(:Show, {:container, [name: "Color"], []}, env)
  end
end
