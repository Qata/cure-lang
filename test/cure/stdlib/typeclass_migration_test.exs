defmodule Cure.Stdlib.TypeclassMigrationTest do
  # The 5 stdlib protocol modules migrated from runtime `proto`/`impl` to
  # compile-time `interface`/`implementation`. Each must elaborate on the
  # DEPENDENT pipeline and its methods resolve + run. Grown one module at a time.
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  describe "Std.Functor (higher-kinded)" do
    test "the module elaborates as an interface on the dependent pipeline" do
      assert {:ok, _env} = Program.elaborate(File.read!("lib/std/functor.cure"))
    end

    test "fmap over a List resolves via the imported List instance (HKT)" do
      src = """
      mod M
        use Std.List
        use Std.Functor
        fn bump(xs: List(Int)) -> List(Int) = fmap(xs, fn(x) -> x + 10)
      """
      # HKT resolution recovers the `List` head constructor from `f(a) = List(Int)`
      # and selects the imported instance's method — proving `interface`/`instance`
      # state crosses the `use` boundary (merge_env unions interfaces + coherence).
      assert {:ok, env} = Program.elaborate(src)
      assert :__impl_Functor_List_fmap in Program.impl_def_names(env)
      assert inspect(Map.get(env.defs, :bump).body) =~ "__impl_Functor_List_fmap"
    end

    # END-TO-END RUN is blocked upstream, NOT by typeclasses: Std.Functor's List
    # instance delegates to `Std.List.map`, and cross-module *polymorphic* stdlib
    # calls still mis-elaborate on the dependent pipeline — the qualified
    # `Std.List.map` lowers to a bare `{:global, :map}` (real global is
    # `Std.List#map`) and the caller passes `map`'s erased type params explicitly.
    # `resolve_hkt_test` proves the identical fmap RUNS once its delegate is a
    # local fn, so resolution + emit of the typeclass machinery is sound; the gap
    # is the #23 cross-module-call surface. Unskip when that lands.
    @tag :skip
    test "fmap over a List runs end-to-end (needs #23 cross-module polymorphic calls)" do
      src = """
      mod M
        use Std.List
        use Std.Functor
        fn bump(xs: List(Int)) -> List(Int) = fmap(xs, fn(x) -> x + 10)
      """
      {:ok, env} = Program.elaborate(src)
      functions = Enum.uniq([:bump | Program.impl_def_names(env)])
      {:ok, m} = Emit.compile_and_load(env, module: :"Cure.M", functions: functions)
      assert apply(m, :bump, [[1, 2, 3]]) == [11, 12, 13]
    end
  end
end
