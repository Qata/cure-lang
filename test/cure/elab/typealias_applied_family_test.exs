defmodule Cure.Elab.TypealiasAppliedFamilyTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  # A `typealias` to an APPLIED data family (`List(Int)`, `String = List(Char)`)
  # used as a function's return type must drive checking mode for a bare-ctor body
  # (a list literal), exactly as the un-aliased `List(Int)` annotation does. The
  # checked-ctor bidirectional path solves the family/params from the expected
  # type, which it must δ-unfold through the alias first — otherwise the list
  # literal falls to inference mode and the kernel rejects the bare `List`
  # constructor with `:ctor_requires_checking_mode`.
  test "list literal checks against a typealias to List(Int)" do
    src = """
    mod TA
      typealias Ints = List(Int)
      fn f() -> Ints = [1, 2, 3]
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.TA", functions: [:f])
    assert apply(m, :f, []) == [1, 2, 3]
  end

  test "string literal checks against a typealias String = List(Char)" do
    src = """
    mod TA
      use Std.Bounded
      typealias Char = Bounded(1114112)
      typealias String = List(Char)
      fn f() -> String = "hi"
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.TA", functions: [:f])
    assert apply(m, :f, []) == [?h, ?i]
  end
end
