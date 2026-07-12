defmodule Cure.Stdlib.SetDependentRunTest do
  @moduledoc """
  End-to-end run of the SHIPPING `lib/std/set.cure` through the dependent
  pipeline. `Std.Set` is a `Map(t, Bool)` delegating to `Std.Map`/`Std.List`;
  its `from_list`/`intersection`/`difference` use structural recursion (not a
  `foldl` seeded with a polymorphic `new()`, which leaves the seed's
  metavariables unsolved — see
  `test/cure/elab/fold_accumulator_poly_seed_reach_test.exs`).

  `dependent_elaboration_parity_test.exs` guards that the file *elaborates*;
  `set_dependent_capability_test.exs` guards a self-contained *emit*. This pins
  the actual delegated module's *runtime* behaviour so a regression in the
  cross-module lowering is caught as a wrong answer, not just a type error.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Program, Emit}

  setup_all do
    src = File.read!("lib/std/set.cure")
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    {:ok, env} = Program.elaborate(src)
    origins = Program.import_origins(ast)

    fns =
      Program.reachable_def_names(env, [
        :from_list,
        :intersection,
        :difference,
        :union,
        :member,
        :to_list,
        :add,
        :remove,
        :new,
        :size
      ])

    {:ok, m} =
      Emit.compile_and_load(env, module: :"Cure.Test.SetShip", functions: fns, origins: origins)

    {:ok, m: m}
  end

  test "from_list dedups and size counts distinct elements", %{m: m} do
    assert apply(m, :size, [apply(m, :from_list, [[7, 7, 8]])]) == 2
  end

  test "intersection keeps the shared elements", %{m: m} do
    a = apply(m, :from_list, [[1, 2, 3]])
    b = apply(m, :from_list, [[2, 3, 4]])
    assert Enum.sort(apply(m, :to_list, [apply(m, :intersection, [a, b])])) == [2, 3]
  end

  test "difference keeps only elements not in the second set", %{m: m} do
    a = apply(m, :from_list, [[1, 2, 3]])
    b = apply(m, :from_list, [[2, 3, 4]])
    assert Enum.sort(apply(m, :to_list, [apply(m, :difference, [a, b])])) == [1]
  end

  test "member and remove behave", %{m: m} do
    s = apply(m, :from_list, [[1, 2]])
    assert apply(m, :member, [2, s]) == true
    assert apply(m, :member, [9, s]) == false
    assert apply(m, :member, [2, apply(m, :remove, [2, s])]) == false
  end
end
