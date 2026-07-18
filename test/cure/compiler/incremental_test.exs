defmodule Cure.Compiler.IncrementalTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{BuildManifest, DepGraph, Incremental}

  # A 3-module chain Leaf <- Mid <- Top via `use`, plus `Amb`, an extra module
  # that `Top` `use`s and calls. Surface syntax is the real Cure form
  # (`mod Name` with no `do`/`end`; `fn name(args) -> T = body`), confirmed
  # against `lib/std/*.cure`.
  @leaf_v1 """
  mod Leaf
    fn pubval() -> Int = helper()
    fn helper() -> Int = 1
  """

  # Same source-code definitions, one added comment line -> the elaborated
  # `export_env` (and thus the interface hash) is byte-identical, but the raw
  # source bytes differ. This is the interface-INVARIANT edit: `Leaf` itself
  # recompiles (its `source_hash` changed) but nothing downstream should.
  #
  # NOTE (deviation from plan's `@leaf_v2_private`): a private-helper *body* edit
  # is NOT interface-invariant here — `export_env` carries private def bodies, so
  # changing `helper`'s body changes the hash and legitimately cascades. The
  # plan's Step-4 fallback prescribes exactly this comment/whitespace edit for a
  # language whose `export_env` includes private defs. Verified empirically.
  @leaf_v2_comment """
  mod Leaf
    ## interface-invariant edit: a comment, no change to any definition
    fn pubval() -> Int = helper()
    fn helper() -> Int = 1
  """

  # Changed PUBLIC surface -> interface changed -> use-dependents must recompile.
  @leaf_v3_public """
  mod Leaf
    fn pubval() -> Int = 7
    fn helper() -> Int = 1
  """

  @amb_v1 """
  mod Amb
    fn thing() -> Int = 1
  """

  @amb_v2 """
  mod Amb
    fn thing() -> Int = 2
  """

  @mid """
  mod Mid
    use Leaf
    fn midval() -> Int = pubval()
  """

  # Top `use`s Mid (the Leaf<-Mid<-Top chain) and also `use`s Amb, calling it
  # with a qualified name. `Amb` is therefore a direct dependency of `Top`.
  #
  # NOTE (deviation from plan): the plan intended `Top` to call `Amb.thing()`
  # WITHOUT `use Amb`, to exercise a "closure-only" edge (present in
  # `closure_deps_map` but not `order_deps_map`) by having the dependent
  # actually resolve a name ambiently. Empirically, a qualified call to a
  # module that is not `use`d does not compile in this compiler
  # (`{:codegen_error, :unknown_global}`) -- that SPECIFIC construction (ambient
  # NAME RESOLUTION without `use`) cannot be built as a unit fixture. That is
  # not the same claim as "no compilable closure-only edge exists": the edge
  # itself is a purely structural artifact of `DepGraph.finalize_node/4`, which
  # appends every `@prelude`-decorated module to EVERY OTHER node's
  # `closure_deps` unconditionally, regardless of whether that node's body
  # references it at all. A dependent needs no ambient call to pick up the
  # edge -- see the closure-only-edge driver fixture (`P`/`Q`/`R`) further
  # below, which compiles and exercises exactly this. The closure-vs-order
  # superset contract is also pinned by a scan-only test below, and its live
  # effect on the real stdlib (ambient preludes) is exercised by the stdlib
  # integration test (Task 5).
  @top """
  mod Top
    use Mid
    use Amb
    fn topval() -> Int = midval()
    fn viaamb() -> Int = Amb.thing()
  """

  setup do
    root = Path.join(System.tmp_dir!(), "cure_incr_#{:erlang.unique_integer([:positive])}")
    src = Path.join(root, "src")
    out = Path.join(root, "ebin")
    File.mkdir_p!(src)
    File.mkdir_p!(out)
    on_exit(fn -> File.rm_rf!(root) end)

    write = fn name, body -> File.write!(Path.join(src, name), body) end
    write.("leaf.cure", @leaf_v1)
    write.("mid.cure", @mid)
    write.("top.cure", @top)
    write.("amb.cure", @amb_v1)

    {:ok, src: src, out: out, write: write}
  end

  defp paths(src), do: Path.wildcard(Path.join(src, "*.cure"))

  defp compile(src, out, opts \\ []) do
    Incremental.compile_dir(paths(src), out, Keyword.put_new(opts, :source_roots, [src]))
  end

  test "first build compiles every module", %{src: src, out: out} do
    assert {:ok, s} = compile(src, out)
    assert Enum.sort(s.compiled) == ["Amb", "Leaf", "Mid", "Top"]
    assert s.skipped_fresh == []
    assert s.errors == []
  end

  test "no-change rebuild compiles nothing", %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    assert {:ok, s} = compile(src, out)
    assert s.compiled == []
    assert Enum.sort(s.skipped_fresh) == ["Amb", "Leaf", "Mid", "Top"]
  end

  test "editing a leaf's comment (interface-invariant) recompiles only the leaf",
       %{src: src, out: out, write: write} do
    assert {:ok, _} = compile(src, out)
    write.("leaf.cure", @leaf_v2_comment)
    assert {:ok, s} = compile(src, out)
    assert s.compiled == ["Leaf"]
    assert "Mid" in s.skipped_fresh and "Top" in s.skipped_fresh
  end

  test "editing a leaf's PUBLIC surface cascades to its use-dependents",
       %{src: src, out: out, write: write} do
    assert {:ok, _} = compile(src, out)
    write.("leaf.cure", @leaf_v3_public)
    assert {:ok, s} = compile(src, out)
    assert "Leaf" in s.compiled and "Mid" in s.compiled and "Top" in s.compiled
  end

  test "editing a directly-depended module recompiles its caller",
       %{src: src, out: out, write: write} do
    assert {:ok, _} = compile(src, out)
    write.("amb.cure", @amb_v2)
    assert {:ok, s} = compile(src, out)
    assert "Amb" in s.compiled
    assert "Top" in s.compiled
    # Mid does not depend on Amb, so it stays fresh.
    assert "Mid" in s.skipped_fresh
  end

  test "closure_deps_map (the driver's dirty graph) is a strict superset of use-only edges" do
    # The driver decides propagation over `closure_deps_map/1`, not
    # `order_deps_map/1`. This matters for edges that are NOT `use` edges —
    # ambient `@prelude` providers and qualified-call targets — which appear in
    # the closure map only. A dependent that actually RESOLVES a name ambiently
    # (no `use`) is not compilable in this compiler (see the NOTE on `@top`
    # above), so that specific shape is scan-only here; the structural
    # `@prelude`-append edge itself (no ambient call needed) IS compilable and
    # is exercised end-to-end by the `P`/`Q`/`R` driver fixture further below.
    # Scan-only assertion of the superset relationship:
    root = Path.join(System.tmp_dir!(), "cure_closure_#{:erlang.unique_integer([:positive])}")
    src = Path.join(root, "src")
    File.mkdir_p!(src)
    on_exit(fn -> File.rm_rf!(root) end)

    File.write!(Path.join(src, "amb.cure"), "@prelude\nmod Amb\n  @prelude\n  fn thing() -> Int = 1\n")
    File.write!(Path.join(src, "consumer.cure"), "mod Consumer\n  fn go() -> Int = thing()\n")

    {:ok, graph} = DepGraph.scan(Path.wildcard(Path.join(src, "*.cure")))
    closure = DepGraph.closure_deps_map(graph)
    order = DepGraph.order_deps_map(graph)

    # Consumer ambiently depends on Amb: present in closure, absent from order.
    assert "Amb" in Map.get(closure, "Consumer", [])
    refute "Amb" in Map.get(order, "Consumer", [])
  end

  test "a missing beam forces recompile even when the hash matches", %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    File.rm!(Path.join(out, "Cure.Leaf.beam"))
    assert {:ok, s} = compile(src, out)
    assert "Leaf" in s.compiled
  end

  test "a toolchain change forces a full rebuild", %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    m = BuildManifest.load(out)
    BuildManifest.save(%{m | toolchain: <<0>>}, out)
    assert {:ok, s} = compile(src, out)
    assert Enum.sort(s.compiled) == ["Amb", "Leaf", "Mid", "Top"]
  end

  test "deleting a source removes its beam and drops it from the manifest", %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    File.rm!(Path.join(src, "top.cure"))
    assert {:ok, s} = compile(src, out)
    assert "Top" in s.deleted
    refute File.exists?(Path.join(out, "Cure.Top.beam"))
    refute Map.has_key?(BuildManifest.load(out).modules, "Top")
  end

  test "a toolchain bump in the same build as a deleted source still deletes the beam",
       %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    m = BuildManifest.load(out)
    BuildManifest.save(%{m | toolchain: <<0>>}, out)
    File.rm!(Path.join(src, "top.cure"))
    assert {:ok, s} = compile(src, out)
    assert "Top" in s.deleted
    refute File.exists?(Path.join(out, "Cure.Top.beam"))
  end

  test "a foreign manifest entry (outside this run's roots) is left untouched", %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    # Simulate a stdlib entry from a prior build sharing this output dir.
    File.write!(Path.join(out, "Cure.Std.Fake.beam"), "stub")
    m = BuildManifest.load(out)

    foreign =
      Map.put(m.modules, "Std.Fake", %{
        source_path: "lib/std/fake.cure",
        source_hash: <<1>>,
        interface_hash: <<2>>,
        deps: [],
        beams: ["Cure.Std.Fake.beam"]
      })

    BuildManifest.save(%{m | modules: foreign}, out)

    assert {:ok, s} = compile(src, out)
    refute "Std.Fake" in s.deleted
    assert File.exists?(Path.join(out, "Cure.Std.Fake.beam"))
    assert Map.has_key?(BuildManifest.load(out).modules, "Std.Fake")
  end

  test "a compile error keeps the module dirty and does not advance the manifest",
       %{src: src, out: out, write: write} do
    assert {:ok, _} = compile(src, out)
    write.("leaf.cure", "mod Leaf\n  fn pubval() -> Int = nonexistent_fn()\n")
    assert {:ok, s} = compile(src, out)
    # Leaf errors; its use-dependents (Mid, Top) cannot resolve the broken chain
    # and error too — a correct cascade. The contract under test is that the
    # failing module is reported and the manifest is not advanced.
    assert Enum.any?(s.errors, fn {m, _} -> m == "Leaf" end)
    # manifest NOT advanced: next run still sees Leaf as dirty
    assert {:ok, s2} = compile(src, out)
    assert "Leaf" in (s2.compiled ++ Enum.map(s2.errors, &elem(&1, 0)))
  end

  test "a dependency failing to compile treats its dependent as dirty too",
       %{src: src, out: out, write: write} do
    assert {:ok, _} = compile(src, out)
    # break Leaf; Mid `use`s Leaf. Mid must not be recorded fresh against a broken dep.
    write.("leaf.cure", "mod Leaf\n  fn pubval() -> Int = nonexistent_fn()\n")
    assert {:ok, s} = compile(src, out)
    assert Enum.any?(s.errors, fn {m, _} -> m == "Leaf" end)
    # Mid is either recompiled or errored this build, never silently skipped fresh.
    refute "Mid" in s.skipped_fresh
  end

  test "a source with a genuine parse error is reported, not silently dropped", %{src: src, out: out} do
    File.write!(Path.join(src, "broken.cure"), "mod Broken\n  fn x( = end\n")
    assert {:ok, s} = compile(src, out)
    assert s.errors != []
  end

  test "force rebuilds everything", %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    assert {:ok, s} = compile(src, out, force: true)
    assert Enum.sort(s.compiled) == ["Amb", "Leaf", "Mid", "Top"]
  end

  # Proves `beams_for/3` does not over-match on Cure's dotted module-naming
  # convention. `Ns.Base` and `Ns.Base.Child` are two INDEPENDENT top-level
  # modules (two files, two `mod` declarations) that merely share a dotted
  # prefix — mirroring real stdlib siblings like `Std.Otp` / `Std.Otp.Call`.
  # A bare `Cure.Ns.Base.*.beam` wildcard would match `Cure.Ns.Base.Child.beam`
  # too; deleting `Ns.Base`'s source must not delete `Ns.Base.Child`'s beam.
  @ns_base """
  mod Ns.Base
    fn baseval() -> Int = 1
  """

  @ns_base_child """
  mod Ns.Base.Child
    fn childval() -> Int = 2
  """

  test "deleting a module does not delete a sibling whose name shares its dotted prefix",
       %{src: src, out: out, write: write} do
    write.("ns_base.cure", @ns_base)
    write.("ns_base_child.cure", @ns_base_child)
    assert {:ok, s0} = compile(src, out)
    assert "Ns.Base" in s0.compiled and "Ns.Base.Child" in s0.compiled

    File.rm!(Path.join(src, "ns_base.cure"))
    assert {:ok, s} = compile(src, out)
    assert "Ns.Base" in s.deleted
    refute "Ns.Base.Child" in s.deleted
    assert File.exists?(Path.join(out, "Cure.Ns.Base.Child.beam"))
    assert Map.has_key?(BuildManifest.load(out).modules, "Ns.Base.Child")
  end

  # Regression (compile-order soundness): the driver must compile every module
  # AFTER its `use`-dependencies (`order_deps`), because codegen links a module's
  # use-deps' beams — build them out of order and a cold build fails with
  # `{:missing_stdlib_module, ...}` (empty code path) or, worse, silently links a
  # STALE dep beam already on the path. The trap: the ambient `@prelude`
  # primitives (`Std.Atom`, `Std.Binary`, `Std.Char`, ...) form a *cycle* in
  # `closure_deps_map/1`, so ordering the walk by the closure graph emits that SCC
  # ALPHABETICALLY — placing `Std.Binary` before `Std.Char` even though
  # `Binary use Char`. `compile_order/1` must instead follow the acyclic
  # `order_deps` graph, exactly as the pre-incremental loop did. This is checked
  # on the real stdlib graph because a compilable ambient cycle can't be built as
  # a bare temp fixture, and the test BEAM keeps the stdlib loaded+sticky (so an
  # in-process cold build resolves deps from memory and can't surface the miss).
  # Regression test for the `dep_changed?/2` not-yet-visited fallback added by
  # the ordering fix (`cae31e7f`). `P` is `@prelude` -- every OTHER module's
  # `closure_deps` gets `P` appended unconditionally (`DepGraph.finalize_node`),
  # regardless of whether it actually references `P`. `P` itself `use`s `R`
  # (a real order_dep), so the acyclic `order_deps` walk schedules `R` before
  # `P`. `Q` has no relationship to `P` at all beyond that ambient closure
  # edge, and no order_dep on anything, so alphabetically it is scheduled
  # BEFORE `P` (`Q` < `R` < `P`). When the driver decides `Q`'s freshness,
  # `P` is not yet in `state.iface` -- the "not-yet-visited closure dep"
  # branch. That branch falls back to `base_dirty[P]`, which reports "clean"
  # (P's own source/beam are untouched) even though P's INTERFACE is about to
  # change this very build, because its real dependency `R` changed. `Q`
  # ambiently depends on `P` (that's what the closure edge means) and must
  # not be served a stale beam.
  @p_prelude """
  @prelude
  mod P
    use R
    fn pval() -> Int = R.val()
  """

  @r_v1 """
  mod R
    fn val() -> Int = 1
  """

  @r_v2 """
  mod R
    fn val() -> Int = 2
  """

  @q_ambient """
  mod Q
    fn qval() -> Int = 42
  """

  test "a closure-only ambient-prelude dependency's cascaded interface change is not missed by the not-yet-visited fallback" do
    root = Path.join(System.tmp_dir!(), "cure_ambient_#{:erlang.unique_integer([:positive])}")
    src = Path.join(root, "src")
    out = Path.join(root, "ebin")
    File.mkdir_p!(src)
    on_exit(fn -> File.rm_rf!(root) end)

    File.write!(Path.join(src, "p.cure"), @p_prelude)
    File.write!(Path.join(src, "r.cure"), @r_v1)
    File.write!(Path.join(src, "q.cure"), @q_ambient)
    paths = Path.wildcard(Path.join(src, "*.cure"))

    assert {:ok, s0} = Incremental.compile_dir(paths, out, source_roots: [src])
    assert Enum.sort(s0.compiled) == ["P", "Q", "R"]

    # Precondition: Q really is scheduled before P in this graph -- otherwise
    # this test isn't exercising the not-yet-visited fallback at all.
    {:ok, graph} = DepGraph.scan(paths)
    pos = Incremental.compile_order(graph) |> Enum.with_index() |> Map.new()
    assert pos["Q"] < pos["P"]

    File.write!(Path.join(src, "r.cure"), @r_v2)
    assert {:ok, s} = Incremental.compile_dir(paths, out, source_roots: [src])

    assert "R" in s.compiled
    assert "P" in s.compiled, "P has a real use-dep on R, which changed -- P must recompile"

    assert "Q" in s.compiled,
           "Q ambiently depends on P (prelude closure edge) and P's interface changed " <>
             "this build -- Q must not be served a stale beam"
  end

  test "compile_order places every module after its use-dependencies (real stdlib graph)" do
    {:ok, graph} = DepGraph.scan(Path.wildcard("lib/std/*.cure"))
    order = Incremental.compile_order(graph)

    pos = order |> Enum.with_index() |> Map.new()
    order_deps = DepGraph.order_deps_map(graph)

    violations =
      for m <- order,
          d <- Map.get(order_deps, m, []),
          Map.has_key?(pos, d),
          pos[d] > pos[m],
          do: {m, d}

    assert violations == [], "module compiled before its use-dep: #{inspect(violations)}"
    # The exact edge that the buggy closure-ordering got wrong.
    assert pos["Std.Char"] < pos["Std.Binary"]
    # Every named stdlib module is scheduled exactly once.
    assert length(order) == map_size(order_deps)
  end
end
