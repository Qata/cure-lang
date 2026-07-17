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

  The delegated `Cure.Std.Map` is emitted at its FULL owner surface (incl.
  `get/2`), identical to the module the stdlib preload JIT-compiles from
  `map.cure` and that `union_test.exs` / `map_parameterized_test.exs` call into —
  so installing it under the shared process-global BEAM name can never drop a
  function another test relies on (it was a tree-shaken partial view that caused
  the historical flake).

  `async: true` is sound: this `setup_all` is the *only* reloader of the global
  `Cure.Std.Map` in the suite — every other `Emit.compile_and_load` targets a
  test-local module and merely remote-calls into the preloaded Map. With a single
  reloader at most two code versions coexist, so BEAM's code-purge (which kills a
  process only when a *third* version loads over live code) cannot fire.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Name, Program, Emit}

  setup_all do
    src = File.read!("lib/std/set.cure")
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    {:ok, env} = Program.elaborate(src)
    origins = Program.import_origins(ast)

    # Seed reachability with the FULL `Std.Map` owner surface, not just Set's
    # delegated subset, so the process-global `Cure.Std.Map` this installs is
    # identical to the full module the real compiler installs (the stdlib preload
    # JIT-compiles all of `map.cure`) and that consumers — `union_test.exs`,
    # `map_parameterized_test.exs` — call into. A tree-shaken partial view would
    # drop `get/2` and clobber that full module under the shared global BEAM name,
    # which is the flaky-test root cause. The real compiler never prunes a
    # dependency owner: `codegen_modules_with_main` emits only the main module and
    # each imported owner is installed at full surface by the preload — so emitting
    # the full owner surface here mirrors the shipping behaviour.
    map_surface = env.defs |> Map.keys() |> Enum.filter(&(Name.owner(&1) == "Std.Map"))

    fns =
      Program.reachable_def_names(
        env,
        [
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
        ] ++ map_surface
      )

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
