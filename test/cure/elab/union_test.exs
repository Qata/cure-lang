defmodule Cure.Elab.UnionTest do
  @moduledoc """
  End-to-end elaboration of anonymous unions, through `Program.elaborate/1` (so the
  stdlib prelude is in scope and `String` resolves).
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Inductive}
  alias Cure.Elab.{Program, Union}

  defp unwrap_lams({:lam, _g, _dom, body}), do: unwrap_lams(body)
  defp unwrap_lams(term), do: term

  defp union_families(env) do
    env.families |> Map.keys() |> Enum.filter(&Union.union_family?/1) |> Enum.sort()
  end

  describe "family generation" do
    test "a union in a parameter annotation declares its family" do
      src = """
      mod M
        fn f(x: Int | Bool) -> Int = 1
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert Inductive.family?(env, :"Union<Bool|Int>")
    end

    test "the family has one constructor per member, family-qualified" do
      src = """
      mod M
        fn f(x: Int | Bool) -> Int = 1
      end
      """

      assert {:ok, env} = Program.elaborate(src)

      names =
        env |> Inductive.ctors_of(:"Union<Bool|Int>") |> Enum.map(& &1.name) |> Enum.sort()

      assert names == [:"Union<Bool|Int>$Bool", :"Union<Bool|Int>$Int"]
    end

    test "a type member's ctor takes one payload argument; a literal member's takes none" do
      src = """
      mod M
        fn f(x: Int | :north) -> Int = 1
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      key = :"Union<Atom#:north|Int>"

      arities =
        env
        |> Inductive.ctors_of(key)
        |> Map.new(fn c -> {c.name, length(c.args)} end)

      assert arities[:"Union<Atom#:north|Int>$Int"] == 1
      assert arities[:"Union<Atom#:north|Int>$Atom#:north"] == 0
    end

    test "Int | Bool and Bool | Int declare ONE family, not two" do
      src = """
      mod M
        fn f(x: Int | Bool) -> Int = 1
        fn g(y: Bool | Int) -> Int = 2
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert union_families(env) == [:"Union<Bool|Int>"]
    end

    test "a one-member union collapses to the member itself — no family is generated" do
      src = """
      mod M
        fn f(x: Int | Int) -> Int = x
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert union_families(env) == []
    end

    test "(A | B) | C flattens: a union-typed alias used as a member splices in" do
      src = """
      mod M
        typealias P = Int | Bool
        fn f(x: P | Atom) -> Int = 1
      end
      """

      assert {:ok, env} = Program.elaborate(src)

      assert Inductive.family?(env, :"Union<Atom|Bool|Int>")

      ctors =
        env |> Inductive.ctors_of(:"Union<Atom|Bool|Int>") |> Enum.map(& &1.name) |> Enum.sort()

      assert length(ctors) == 3
    end
  end

  describe "admission errors surface from elaboration" do
    test "rejects a literal overlapping its own type" do
      src = """
      mod M
        fn f(x: Int | 3) -> Int = 1
      end
      """

      assert {:error, {:union_member_overlap, "Int#3", "Int"}} = Program.elaborate(src)
    end
  end

  describe "injection at check-position" do
    test "a member value is injected when checked against the union" do
      src = """
      mod M
        fn f(n: Int) -> Int | Bool = n
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      body = Env.get_def(env, :f).body |> unwrap_lams()

      assert {:ctor, :"Union<Bool|Int>$Int", [{:var, 0}]} = body
    end

    test "a literal is injected into its literal member constructor" do
      src = """
      mod M
        fn f() -> 3 | 4 = 3
      end
      """

      assert {:ok, env} = Program.elaborate(src)

      assert {:ctor, :"Union<Int#3|Int#4>$Int#3", []} = Env.get_def(env, :f).body
    end

    test "a value whose type is not a member is rejected" do
      src = """
      mod M
        fn f(b: Bool) -> Int | Atom = b
      end
      """

      assert {:error, _} = Program.elaborate(src)
    end
  end

  describe "widening" do
    test "a narrower union is widened into a wider one" do
      src = """
      mod M
        fn narrow(n: Int) -> Int | Bool = n
        fn wide(n: Int) -> Int | Bool | Atom = narrow(n)
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      body = Env.get_def(env, :wide).body |> unwrap_lams()

      assert {:case, _scrut, _motive, branches} = body

      # One branch per ctor of the NARROW family, each remapped to its counterpart
      # in the wide one. This is a real function, not a cast.
      assert branches |> Enum.map(fn {c, ar, _} -> {c, ar} end) |> Enum.sort() ==
               [{:"Union<Bool|Int>$Bool", 1}, {:"Union<Bool|Int>$Int", 1}]
    end

    test "widening to a union that lacks a source member is rejected" do
      src = """
      mod M
        fn narrow(n: Int) -> Int | Atom = n
        fn wide(n: Int) -> Int | Bool = narrow(n)
      end
      """

      assert {:error, _} = Program.elaborate(src)
    end
  end

  describe "elimination via typed patterns" do
    test "a match over a union becomes a Core :case with one branch per member" do
      src = """
      mod M
        fn f(x: Int | Bool) -> Int = match x
          n: Int -> n
          b: Bool -> 0
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      body = Env.get_def(env, :f).body |> unwrap_lams()

      assert {:case, _scrut, _motive, branches} = body

      assert branches |> Enum.map(fn {c, ar, _} -> {c, ar} end) |> Enum.sort() ==
               [{:"Union<Bool|Int>$Bool", 1}, {:"Union<Bool|Int>$Int", 1}]
    end

    test "a literal member is matched as a bare literal and binds nothing" do
      src = """
      mod M
        fn f(x: Int | :north) -> Int = match x
          n: Int -> n
          :north -> 0
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      body = Env.get_def(env, :f).body |> unwrap_lams()

      assert {:case, _, _, branches} = body
      arities = Map.new(branches, fn {c, ar, _} -> {c, ar} end)

      assert arities[:"Union<Atom#:north|Int>$Atom#:north"] == 0
      assert arities[:"Union<Atom#:north|Int>$Int"] == 1
    end

    test "a non-exhaustive match is rejected by the existing coverage check" do
      src = """
      mod M
        fn f(x: Int | Bool) -> Int = match x
          n: Int -> n
      end
      """

      assert {:error, {:missing_branch, _}} = Program.elaborate(src)
    end

    test "a branch naming a non-member is rejected" do
      src = """
      mod M
        fn f(x: Int | Bool) -> Int = match x
          n: Int -> n
          a: Atom -> 0
      end
      """

      assert {:error, _} = Program.elaborate(src)
    end

    test "a sub-union branch binds the narrowed value" do
      src = """
      mod M
        fn f(x: Int | Bool | Atom) -> Int | Bool | Atom = match x
          n: Int -> n
          rest: Bool | Atom -> rest
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      body = Env.get_def(env, :f).body |> unwrap_lams()

      assert {:case, _, _, branches} = body
      # One Core branch per member of the WIDE union — the sub-union arm expanded.
      assert length(branches) == 3
    end

    test "the round trip: inject then eliminate recovers the payload" do
      src = """
      mod M
        fn wrap(n: Int) -> Int | Bool = n
        fn unwrap(x: Int | Bool) -> Int = match x
          n: Int -> n
          b: Bool -> 0
        fn go(n: Int) -> Int = unwrap(wrap(n))
      end
      """

      assert {:ok, _} = Program.elaborate(src)
    end
  end

  # The end-to-end proof: a union is not just well-typed, it RUNS. Construct, match,
  # recover the value on a real BEAM.
  #
  # (Spec §13 asks for this on generic-unix AtomVM. That is not runnable from this
  # repo — cure-lang is the compiler; the AtomVM loop lives in the parent esp32-beam
  # repo. This is the in-repo equivalent; AtomVM validation is a follow-up there.)
  describe "BEAM round-trip" do
    test "construct, match, and recover the payload" do
      src = """
      mod URT
        fn wrap(n: Int) -> Int | Bool = n
        fn unwrap(x: Int | Bool) -> Int = match x
          n: Int -> n
          b: Bool -> 0
        fn go(n: Int) -> Int = unwrap(wrap(n))
      end
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(src)
      assert apply(:"Cure.URT", :go, [7]) == 7
    end

    test "a type member erases to a tagged 2-tuple under its family-qualified ctor" do
      src = """
      mod UTM
        fn wrap(n: Int) -> Int | Bool = n
      end
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(src)

      assert apply(:"Cure.UTM", :wrap, [7]) == {:"Union<Bool|Int>$Int", 7}
    end

    test "a literal member erases to its family-qualified NULLARY ctor atom" do
      src = """
      mod ULT
        fn pick() -> :north | :south = :north
      end
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(src)

      assert apply(:"Cure.ULT", :pick, []) ==
               :"Union<Atom#:north|Atom#:south>$Atom#:north"
    end
  end
end
