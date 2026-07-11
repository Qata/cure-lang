defmodule Cure.Elab.UnionTest do
  @moduledoc """
  End-to-end elaboration of anonymous unions, through `Program.elaborate/1` (so the
  stdlib prelude is in scope and `String` resolves).
  """
  use ExUnit.Case, async: true

  alias Cure.Core.Inductive
  alias Cure.Elab.{Program, Union}

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
end
