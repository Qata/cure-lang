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

  Emission is ONE BEAM module per Cure owner (`Cure.Std.Set`, `Cure.Std.Map`),
  exactly as the real compiler lowers a multi-module program — Set's delegating
  calls (`new`/`remove`/`size`) reach `Std.Map`'s same-named functions as REMOTE
  calls. Bundling both owners into a single BEAM module is not a real compile
  target and collides on the shared base names (two `new/0`, `remove/2`, …); the
  owner-qualified identities that canonicalization now keeps distinct are what
  make the split faithful.

  Not `async`: the emitted `Cure.Std.Map` is a *partial* view (Set's delegated
  subset — no `get/2`). It is installed under the same process-global BEAM module
  name that `union_test.exs` installs a *full* `Cure.Std.Map` under, so the two must
  not run concurrently (they would clobber each other's global module). Serialized.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Name, Program, Emit}

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

    # Emit one BEAM module per owning Cure module. `remote_target` lowers a
    # cross-owner `{:global, "Std.Map#size"}` to `{Cure.Std.Map, size}`, so the
    # delegated module must be loaded under that same `Cure.<owner>` name.
    fns
    |> Enum.group_by(&Name.owner/1)
    |> Enum.each(fn {owner, names} ->
      {:ok, _} =
        Emit.compile_and_load(env,
          module: String.to_atom("Cure." <> owner),
          functions: names,
          origins: origins
        )
    end)

    {:ok, m: :"Cure.Std.Set"}
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
