defmodule Cure.Elab.SemigroupConcatTest do
  @moduledoc """
  Concatenation is an operator overload resolved through the `Std.Semigroup`
  interface — not a bespoke case in `build_binop`. `<>` desugars to the
  `combine` method, and `+` on a non-numeric operand desugars to the same
  (Swift-style `+` overload), so both dispatch by coherence to the `List`
  implementation (which delegates to the reducing library `Std.List.append`).
  String is `List(Char)`, so string concat rides the same List instance.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  defp eval(src, fname, mod) do
    {:ok, env} = Program.elaborate(src)
    fns = Program.reachable_def_names(env, [fname])
    {:ok, m} = Emit.compile_and_load(env, module: mod, functions: fns)
    apply(m, fname, [])
  end

  test "`<>` on lists dispatches to Semigroup.combine and appends" do
    src = """
    mod T
      use Std.Semigroup
      use Std.List
      fn go() -> List(Int) = [1, 2] <> [3, 4]
    end
    """
    assert eval(src, :go, :"Cure.SgAngle") == [1, 2, 3, 4]
  end

  test "`+` on lists is the Semigroup overload (Swift-style) and appends" do
    src = """
    mod T
      use Std.Semigroup
      use Std.List
      fn go() -> List(Int) = [1, 2] + [3, 4]
    end
    """
    assert eval(src, :go, :"Cure.SgPlus") == [1, 2, 3, 4]
  end

  test "`<>` on strings appends code points (String = List(Char))" do
    src = """
    mod T
      use Std.Semigroup
      use Std.String
      fn go() -> String = "ab" <> "cd"
    end
    """
    assert eval(src, :go, :"Cure.SgStr") == ~c"abcd"
  end

  test "numeric `+` and `<` are untouched by the overload" do
    assert eval("mod T\n  fn go() -> Int = 2 + 3\nend\n", :go, :"Cure.SgNumAdd") == 5
    assert eval("mod T\n  fn go() -> Bool = 2 < 3\nend\n", :go, :"Cure.SgNumLt") == true
  end

  test "`<>` in checking position (a call argument) dispatches" do
    # The concat operator must resolve when it appears in checking mode, not
    # only as a whole function body — here as the argument of `length`, checked
    # against its `List(Int)` parameter.
    src = """
    mod T
      use Std.Semigroup
      use Std.List
      fn go() -> Int = length([1, 2] <> [3])
    end
    """
    assert eval(src, :go, :"Cure.SgChecked") == 3
  end
end
