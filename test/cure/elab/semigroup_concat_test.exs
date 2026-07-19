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

  # Regression: the generated `combine` List instance lowers its body to a
  # `case Arg of [H|T] -> … ; [] -> … end`. The cons-pattern binders `H`/`T`
  # come from `fresh_var("V")` = `V<unique_integer>`, while the function's own
  # parameters are positional `V<pos>` (small de Bruijn indices). Because
  # `System.unique_integer/1` can hand back a *small* value early in the VM's
  # life, a fresh binder could mint the exact name `V1`/`V2` already in scope as
  # a parameter — turning a fresh cons-bind into an equality match against the
  # whole list and crashing at runtime (a non-deterministic `CaseClauseError`,
  # seeded by VM state). The invariant that rules this out: a synthetic binder
  # must never take the reserved positional shape `V<digits>`. Checking the
  # *shape* (not a specific collision) makes this deterministic regardless of
  # the counter's current value.
  test "synthetic case-pattern binders never take the reserved positional shape" do
    src = """
    mod T
      use Std.Semigroup
      use Std.List
      fn go() -> List(Int) = [1, 2] <> [3, 4]
    end
    """

    {:ok, env} = Program.elaborate(src)
    fns = Program.reachable_def_names(env, [:go])
    {:ok, forms} = Emit.compile_forms(env, :"Cure.SgShape", fns)

    offenders = Enum.flat_map(forms, &case_pattern_vars/1)

    assert Enum.filter(offenders, &(&1 =~ ~r/^V\d+$/)) == [],
           "case-pattern binders with the reserved positional shape V<digits>: " <>
             inspect(Enum.uniq(offenders))
  end

  # Variable names bound in the PATTERN position of any `case` clause, gathered
  # recursively (nested cases included). Function-head parameters are the
  # top-level clause params and are *not* reached here.
  defp case_pattern_vars({:case, _l, scrut, clauses}) do
    from_clauses =
      Enum.flat_map(clauses, fn {:clause, _cl, patterns, _guards, body} ->
        Enum.flat_map(patterns, &pattern_vars/1) ++ Enum.flat_map(body, &case_pattern_vars/1)
      end)

    case_pattern_vars(scrut) ++ from_clauses
  end

  defp case_pattern_vars(form) when is_tuple(form),
    do: Enum.flat_map(Tuple.to_list(form), &case_pattern_vars/1)

  defp case_pattern_vars(form) when is_list(form), do: Enum.flat_map(form, &case_pattern_vars/1)
  defp case_pattern_vars(_), do: []

  defp pattern_vars({:var, _l, name}), do: [Atom.to_string(name)]
  defp pattern_vars({:cons, _l, h, t}), do: pattern_vars(h) ++ pattern_vars(t)
  defp pattern_vars({:tuple, _l, elts}), do: Enum.flat_map(elts, &pattern_vars/1)
  defp pattern_vars(_), do: []

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
