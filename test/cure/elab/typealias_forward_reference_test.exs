defmodule Cure.Elab.TypealiasForwardReferenceTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Kernel}
  alias Cure.Elab.Program

  test "a function signature may reference an alias declared later" do
    src = """
    mod M
      fn id(x: UserId) -> UserId = x
      typealias UserId = Int
    end
    """

    assert {:ok, env} = Program.elaborate(src)
    assert Kernel.check_def(env, :id) == :ok
  end

  test "a forward alias chain is transparent after the declaration pass" do
    src = """
    mod M
      fn id(x: A) -> Int = x
      typealias A = B
      typealias B = Int
    end
    """

    assert {:ok, env} = Program.elaborate(src)
    assert Env.certified?(env, :A)
    assert Env.certified?(env, :B)
    assert Kernel.check_def(env, :id) == :ok
  end

  test "a parameterized alias may be used before its declaration" do
    src = """
    mod M
      fn first(x: First(Int, Bool)) -> Int = x
      typealias First(a, b) = a
    end
    """

    assert {:ok, env} = Program.elaborate(src)
    assert Kernel.check_def(env, :first) == :ok
  end

  test "an unknown alias target is still rejected" do
    assert {:error, _} =
             Program.elaborate("mod M\n  typealias A = Missing\nend\n")
  end

  test "mutually recursive aliases are rejected with a finite diagnostic" do
    src = """
    mod M
      typealias A = B
      typealias B = A
    end
    """

    assert {:error, {:cyclic_typealiases, cycle}} = Program.elaborate(src)
    assert hd(cycle) == List.last(cycle)
    assert MapSet.new(cycle) == MapSet.new([:"M#A", :"M#B"])
  end

  test "an explicit alias does not change single-constructor type disambiguation" do
    src = """
    mod M
      type Wrapper = Wrap(Int)
      fn unwrap(x: Wrapper) -> Int =
        match x
          Wrap(value) -> value
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
