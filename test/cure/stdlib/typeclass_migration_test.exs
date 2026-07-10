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

    test "the imported instance's delegate global is re-keyed to match the moved def" do
      # Std.Functor's List instance body calls `Std.List.map`. When M imports both
      # Std.List and Std.Functor, `map` collides (owned via two reachable edges) and
      # its def KEY moves to `:"Std.List#map"`. The instance body's `{:global, :map}`
      # reference MUST follow — otherwise it dangles and emit fails with {:map, N}.
      src = """
      mod M
        use Std.List
        use Std.Functor
        fn bump(xs: List(Int)) -> List(Int) = fmap(xs, fn(x) -> x + 10)
      """
      {:ok, env} = Program.elaborate(src)
      impl = Map.get(env.defs, :__impl_Functor_List_fmap)
      body = inspect(impl.body)
      assert body =~ "Std.List#map"
      refute body =~ "{:global, :map}"
    end

    test "fmap over a List runs end-to-end (#23 cross-module polymorphic calls)" do
      src = """
      mod M
        use Std.List
        use Std.Functor
        fn bump(xs: List(Int)) -> List(Int) = fmap(xs, fn(x) -> x + 10)
      """
      {:ok, env} = Program.elaborate(src)
      # Co-emit the transitive closure: bump -> impl fmap -> Std.List#map.
      roots = [:bump | Program.impl_def_names(env)]
      functions = Program.reachable_def_names(env, roots)
      {:ok, m} = Emit.compile_and_load(env, module: :"Cure.M", functions: functions)
      assert apply(m, :bump, [[1, 2, 3]]) == [11, 12, 13]
    end
  end
end
