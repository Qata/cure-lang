defmodule Cure.Elab.NestedAliasCtorTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  # Regression guard for the ctor-at-alias-goal kernel fix (commit 6da5d85) plus
  # the conversion checker's δ-unfolding of a certified `typealias`. A bare
  # constructor / list-literal body checked at a goal whose (possibly NESTED)
  # element type is a `typealias` to a data family must δ-unfold that alias to
  # see the family before it can solve the constructor's parameters — otherwise
  # the element falls to inference mode and the kernel rejects the bare `List`
  # constructor with `:ctor_requires_checking_mode`.
  #
  # NOTE: the alias names here are deliberately NOT `S` or `String`. A `typealias`
  # named `S` collides with `Std.Nat`'s successor constructor `S`, and any name
  # that clashes with an in-scope constructor is a *separate shadowing* concern —
  # not a δ-unfold gap. Char/String/Text-style names (the value-surface work) do
  # not collide and exercise the real path.

  test "top-level: list literal at `Row` where Row = List(Int)" do
    src = """
    mod NA
      typealias Row = List(Int)
      fn f() -> Row = [1, 2]
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.NA", functions: [:f])
    assert apply(m, :f, []) == [1, 2]
  end

  test "nested: list-of-lists at List(Row) where Row = List(Int)" do
    src = """
    mod NA
      typealias Row = List(Int)
      fn f() -> List(Row) = [[1, 2], [3]]
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.NA", functions: [:f])
    assert apply(m, :f, []) == [[1, 2], [3]]
  end

  test "conv both directions: List(Row) <-> List(List(Int)) through a call" do
    fwd = """
    mod NA
      typealias Row = List(Int)
      fn mk() -> List(List(Int)) = [[1, 2]]
      fn f() -> List(Row) = mk()
    end
    """

    rev = """
    mod NA
      typealias Row = List(Int)
      fn mk() -> List(Row) = [[1, 2]]
      fn f() -> List(List(Int)) = mk()
    end
    """

    assert {:ok, _} = Program.elaborate(fwd)
    assert {:ok, _} = Program.elaborate(rev)
  end

  test "nested: list of string literals at List(String) where String = List(Char)" do
    src = """
    mod NA
      use Std.Bounded
      typealias Char = Bounded(1114112)
      typealias String = List(Char)
      fn f() -> List(String) = ["hi", "yo"]
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.NA", functions: [:f])
    assert apply(m, :f, []) == [[?h, ?i], [?y, ?o]]
  end
end
