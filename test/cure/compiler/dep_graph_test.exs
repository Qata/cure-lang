defmodule Cure.Compiler.DepGraphTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.DepGraph

  @moduletag :tmp_dir

  defp write!(dir, name, contents) do
    path = Path.join(dir, name)
    File.write!(path, contents)
    path
  end

  describe "scan/2 + order/1" do
    test "orders use-dependencies before their dependents", %{tmp_dir: dir} do
      a = write!(dir, "zz_lib.cure", "mod LibA\n  fn ping() -> Int = 41\n")
      b = write!(dir, "aa_user.cure", "mod UserB\n  use LibA\n  fn start() -> Int = ping()\n")

      {:ok, graph} = DepGraph.scan([b, a])
      {:ok, order, []} = DepGraph.order(graph)

      assert order == [a, b]
    end

    test "deterministic: shuffled input, identical output", %{tmp_dir: dir} do
      paths =
        for n <- ["m1", "m2", "m3", "m4"] do
          write!(dir, n <> ".cure", "mod #{String.upcase(n)}\n  fn f() -> Int = 1\n")
        end

      {:ok, g1} = DepGraph.scan(paths)
      {:ok, g2} = DepGraph.scan(Enum.reverse(paths))
      assert DepGraph.order(g1) == DepGraph.order(g2)
      assert {:ok, Enum.sort(paths), []} == DepGraph.order(g1)
    end

    test "cycle: ordering succeeds as an SCC group and reports the closed walk", %{tmp_dir: dir} do
      a = write!(dir, "a.cure", "mod CycA\n  use CycB\n  fn f() -> Int = 1\n")
      b = write!(dir, "b.cure", "mod CycB\n  use CycA\n  fn g() -> Int = 2\n")
      c = write!(dir, "c.cure", "mod Down\n  use CycA\n  fn h() -> Int = 3\n")

      {:ok, graph} = DepGraph.scan([a, b, c])
      # SCC policy (spec §3.1 as amended): no crash — members compile as a
      # group in alphabetical path order, dependents still AFTER the SCC,
      # and the cycle is reported as one closed walk.
      assert {:ok, order, [hops]} = DepGraph.order(graph)

      assert order == [a, b, c]

      modules = Enum.map(hops, & &1.module)
      assert "CycA" in modules and "CycB" in modules
      refute "Down" in modules
      assert Enum.all?(hops, &(is_binary(&1.path) and is_integer(&1.line)))
      # The hop list must be a CLOSED walk, not just "both modules appear
      # somewhere" -- assert it actually loops back to its own start, per
      # the spec's `A (a.cure:3) -> B (b.cure:2) -> A` format.
      assert length(hops) == 3
      assert List.first(hops).module == List.last(hops).module
    end

    test "duplicate module name across files is an error", %{tmp_dir: dir} do
      a = write!(dir, "one.cure", "mod Dup\n  fn f() -> Int = 1\n")
      b = write!(dir, "two.cure", "mod Dup\n  fn g() -> Int = 2\n")

      assert {:error, {:duplicate_module, "Dup", paths}} = DepGraph.scan([a, b])
      assert Enum.sort(paths) == Enum.sort([a, b])
    end

    test "out-of-set use targets impose no ordering", %{tmp_dir: dir} do
      a = write!(dir, "a.cure", "mod OnlyOne\n  use Std.List\n  use NotInSet\n  fn f() -> Int = 1\n")

      {:ok, graph} = DepGraph.scan([a])
      assert {:ok, [^a], []} = DepGraph.order(graph)
      assert graph.nodes[a].order_deps == [] or
               Enum.all?(graph.nodes[a].order_deps, &(&1.target in ["Std.List", "NotInSet"]))
    end

    test "blank placeholders sort last; parse failures are isolated nodes", %{tmp_dir: dir} do
      blank = write!(dir, "a_blank.cure", "   \n")
      bad = write!(dir, "b_bad.cure", "mod ((((\n")
      good = write!(dir, "c_good.cure", "mod Good\n  fn f() -> Int = 1\n")

      {:ok, graph} = DepGraph.scan([blank, bad, good])
      assert graph.nodes[blank].blank?
      assert graph.nodes[bad].parse_error != nil

      {:ok, order, []} = DepGraph.order(graph)
      assert List.last(order) == blank
      assert bad in order and good in order
    end

    test "self-use is ignored", %{tmp_dir: dir} do
      a = write!(dir, "selfy.cure", "mod Selfy\n  use Selfy\n  fn f() -> Int = 1\n")
      {:ok, graph} = DepGraph.scan([a])
      assert {:ok, [^a], []} = DepGraph.order(graph)
    end

    test "stage1 parity: real lib/compiler tree — every cross-SCC use edge is respected" do
      root = Path.expand("../../..", __DIR__)

      files =
        Path.wildcard(Path.join(root, "lib/compiler/**/*.cure"))
        |> Enum.reject(fn p -> String.trim(File.read!(p)) == "" end)

      {:ok, graph} = DepGraph.scan(files)
      {:ok, order, cycles} = DepGraph.order(graph)
      index = order |> Enum.with_index() |> Map.new()

      # The real tree contains a genuine use cycle (Environment <-> Exception,
      # commit 5ef6d80 — spec §2 fact 6 as amended): it must be REPORTED, and
      # edges inside one SCC are exempt from the ordering property.
      scc_of =
        for {cycle, i} <- Enum.with_index(cycles),
            hop <- cycle,
            into: %{},
            do: {hop.path, i}

      assert Enum.any?(cycles, fn cycle ->
               mods = Enum.map(cycle, & &1.module)

               "Compiler.Kernel.Core.Environment" in mods and
                 "Compiler.Kernel.Core.Exception" in mods
             end),
             "expected the known Environment<->Exception cycle to be reported, got: #{inspect(cycles)}"

      for {path, node} <- graph.nodes,
          %{target: target} <- node.order_deps,
          dep_path = graph.modules[target],
          dep_path != nil,
          # intra-SCC edges are exempt (no valid topological constraint exists)
          scc_of[path] == nil or scc_of[path] != scc_of[dep_path] do
        assert index[dep_path] < index[path],
               "#{target} (#{dep_path}) must precede #{node.module} (#{path})"
      end
    end
  end

  describe "order_deps_map/1" do
    test "maps module names to sorted in-set dep names", %{tmp_dir: dir} do
      a = write!(dir, "a.cure", "mod MA\n  fn f() -> Int = 1\n")
      b = write!(dir, "b.cure", "mod MB\n  use MA\n  use Std.List\n  fn g() -> Int = 2\n")

      {:ok, graph} = DepGraph.scan([a, b])
      assert DepGraph.order_deps_map(graph) == %{"MA" => [], "MB" => ["MA"]}
    end
  end
end
