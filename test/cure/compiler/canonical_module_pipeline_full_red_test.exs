defmodule Cure.Compiler.CanonicalModulePipelineFullRedTest do
  use ExUnit.Case, async: true

  @moduletag :canonical_module_pipeline_red
  @moduletag :tmp_dir

  describe "prelude and environment laws" do
    test "prelude providers add only their declared ambient exports", %{tmp_dir: dir} do
      hidden = write!(dir, "hidden.cure", "mod P.Hidden\n  fn secret() -> Int = 9\n")

      provider =
        write!(
          dir,
          "provider.cure",
          "@prelude\nmod P.Provider\n  use P.Hidden\n  fn ambient() -> Int = 1\n"
        )

      consumer = write!(dir, "consumer.cure", "mod P.Consumer\n  fn value() -> Int = ambient()\n")

      assert {:ok, checked} = check([consumer, provider, hidden], dir)
      assert {:ok, {"fixture", "P.Provider", :value, "ambient"}} = resolve(checked, "P.Consumer", "ambient")
      assert {:error, :not_in_lexical_scope} = resolve(checked, "P.Consumer", "secret")
      refute semantic_edge?(checked, "P.Consumer", "P.Hidden", :prelude_symbol_use)
    end

    test "loading and merging interfaces is idempotent and permutation invariant", %{tmp_dir: dir} do
      a = write!(dir, "a.cure", "mod Merge.A\n  typealias Letter = Int\n")
      b = write!(dir, "b.cure", "mod Merge.B\n  use Merge.A\n  fn id(x: Letter) -> Letter = x\n")
      assert {:ok, checked} = check([b, a], dir)

      assert {:ok, ia} = pipeline(:interface, [checked, "Merge.A"])
      assert {:ok, ib} = pipeline(:interface, [checked, "Merge.B"])
      assert {:ok, once} = pipeline(:merge_interfaces, [[ia, ib]])
      assert {:ok, twice} = pipeline(:merge_interfaces, [[ia, ib, ia, ib]])
      assert {:ok, reversed} = pipeline(:merge_interfaces, [[ib, ia]])

      assert pipeline(:semantic_environment_dump, [once]) ==
               pipeline(:semantic_environment_dump, [twice])

      assert pipeline(:canonical_identities, [once]) == pipeline(:canonical_identities, [reversed])
      assert pipeline(:definitionally_equal?, [once, "Merge.A.Letter", "Int"])
    end

    test "direct imports win no preference from transitive or ambient availability", %{tmp_dir: dir} do
      direct = write!(dir, "direct.cure", "mod Scope.Direct\n  fn same() -> Int = 1\n")
      ambient = write!(dir, "ambient.cure", "@prelude\nmod Scope.Ambient\n  fn same() -> Int = 2\n")
      transitive = write!(dir, "transitive.cure", "mod Scope.Transitive\n  fn same() -> Int = 3\n")

      bridge =
        write!(dir, "bridge.cure", "mod Scope.Bridge\n  use Scope.Transitive\n  fn bridge() -> Int = same()\n")

      consumer =
        write!(
          dir,
          "consumer.cure",
          "mod Scope.Consumer\n  use Scope.Direct\n  use Scope.Bridge\n  fn value() -> Int = same()\n"
        )

      assert {:ok, checked} = check([consumer, bridge, transitive, ambient, direct], dir)
      assert {:ok, {"fixture", "Scope.Direct", :value, "same"}} = resolve(checked, "Scope.Consumer", "same")
    end

    test "conformance publication is owner-local, idempotent, and does not depend on merge order", %{
      tmp_dir: dir
    } do
      protocol =
        write!(
          dir,
          "protocol.cure",
          "mod Law.Protocol\n  interface Same(t)\n    fn same(x: t, y: t) -> Bool\n"
        )

      owner =
        write!(
          dir,
          "owner.cure",
          "mod Law.Owner\n  use Law.Protocol\n  type Box = Box(Int)\n  implementation Same for Box\n    fn same(x: Box, y: Box) -> Bool = true\n"
        )

      consumer =
        write!(
          dir,
          "consumer.cure",
          "mod Law.Consumer\n  use Law.Protocol\n  use Law.Owner\n  fn eq(x: Box) -> Bool = same(x, x)\n"
        )

      assert {:ok, checked} = check([consumer, protocol, owner], dir)
      assert pipeline(:conformance_owner, [checked, "Same", "Law.Owner.Box"]) == "Law.Owner"
      assert pipeline(:conformance_count, [checked, "Same", "Law.Owner.Box"]) == 1

      assert {:ok, permuted} = check([owner, consumer, protocol], dir)

      assert pipeline(:selected_conformance, [checked, "Law.Consumer", "Same", "Law.Owner.Box"]) ==
               pipeline(:selected_conformance, [permuted, "Law.Consumer", "Same", "Law.Owner.Box"])
    end

    test "only explicit reexports cross a second module boundary", %{tmp_dir: dir} do
      base = write!(dir, "base.cure", "mod Export.Base\n  fn value() -> Int = 1\n")
      private_bridge = write!(dir, "private.cure", "mod Export.Private\n  use Export.Base\n")
      public_bridge = write!(dir, "public.cure", "mod Export.Public\n  public use Export.Base\n")
      consumer = write!(dir, "consumer.cure", "mod Export.Consumer\n")
      assert {:ok, checked} = check([consumer, public_bridge, private_bridge, base], dir)

      assert {:error, :not_exported} =
               pipeline(:resolve_reexport, [checked, "Export.Private", :value, "value"])

      assert {:ok, {"fixture", "Export.Base", :value, "value"}} =
               pipeline(:resolve_reexport, [checked, "Export.Public", :value, "value"])
    end
  end

  describe "cycles and staged compilation" do
    test "ordinary runtime cycles compile from explicit signatures", %{tmp_dir: dir} do
      a = write!(dir, "a.cure", "mod Cycle.A\n  fn even(n: Int) -> Bool = Cycle.B.odd(n - 1)\n")
      b = write!(dir, "b.cure", "mod Cycle.B\n  fn odd(n: Int) -> Bool = Cycle.A.even(n - 1)\n")

      assert {:ok, checked} = check([b, a], dir)
      assert pipeline(:component_class, [checked, "Cycle.A"]) == :runtime_cycle
      assert pipeline(:component_members, [checked, "Cycle.A"]) == ["Cycle.A", "Cycle.B"]
    end

    test "an interface SCC checks signatures as one component", %{tmp_dir: dir} do
      a = write!(dir, "a.cure", "mod Cycle.TypeA\n  type A = MkA(Cycle.TypeB.B)\n")
      b = write!(dir, "b.cure", "mod Cycle.TypeB\n  type B = MkB(Cycle.TypeA.A)\n")

      assert {:ok, checked} = check([a, b], dir)
      assert pipeline(:interfaces_frozen_together?, [checked, ["Cycle.TypeA", "Cycle.TypeB"]])
    end

    test "compile-time cycles report the body-requiring edge and complete path", %{tmp_dir: dir} do
      a = write!(dir, "a.cure", "mod Cycle.MetaA\n  type T = Cycle.MetaB.F(T)\n")
      b = write!(dir, "b.cure", "mod Cycle.MetaB\n  fn F(t: Type) -> Type = Cycle.MetaA.T\n")

      assert {:error,
              {:compile_time_cycle,
               %{path: ["Cycle.MetaA", "Cycle.MetaB", "Cycle.MetaA"], requires_body: requires_body}}} =
               check([b, a], dir)

      assert requires_body.declaration == {"fixture", "Cycle.MetaB", :value, "F"}
      assert requires_body.span.path == b
    end
  end

  describe "macros and generated dependencies" do
    test "authored and generated qualified calls resolve to identical Core", %{tmp_dir: dir} do
      provider = write!(dir, "provider.cure", "mod Macro.Provider\n  fn value() -> Int = 7\n")

      authored =
        write!(dir, "authored.cure", "mod Macro.Authored\n  fn run() -> Int = Macro.Provider.value()\n")

      generated =
        write!(
          dir,
          "generated.cure",
          """
          mod Macro.Generated
            macro ProviderValue
              syntax provider_value becomes Macro.Provider.value()

            fn run() -> Int = provider_value
          """
        )

      assert {:ok, checked} = check([generated, authored, provider], dir)

      # Everything but the defining key: the two functions are in different
      # modules, so their own keys differ by construction. What must agree is the
      # call each one elaborated to — a generated qualified call has to reach the
      # same canonical global as the authored one, at the same type.
      assert {:ok, authored_core} = pipeline(:normalized_core, [checked, "Macro.Authored", "run"])
      assert {:ok, generated_core} = pipeline(:normalized_core, [checked, "Macro.Generated", "run"])
      assert Map.delete(authored_core, :key) == Map.delete(generated_core, :key)
      assert authored_core.body == {:global, :"Macro.Provider#value"}
    end

    test "generated references and declarations extend the graph until stable", %{tmp_dir: dir} do
      provider = write!(dir, "provider.cure", "mod Macro.Dependency\n  fn value() -> Int = 1\n")

      # The rule lives in another module on purpose. Only then is the reference
      # its template introduces invisible to the publisher's own header scan, so
      # resolving it is something expansion had to discover rather than something
      # the first scan already knew.
      rules =
        write!(
          dir,
          "rules.cure",
          """
          mod Macro.Rules
            macro Publish
              syntax publish becomes fn made() -> Int = Macro.Dependency.value()
          """
        )

      generated =
        write!(
          dir,
          "generated.cure",
          """
          mod Macro.Publisher
            use Macro.Rules
            publish
          """
        )

      assert {:ok, checked} = check([generated, rules, provider], dir)
      assert semantic_edge?(checked, "Macro.Publisher", "Macro.Dependency", :macro_generated_reference)

      assert pipeline(:canonical_definition, [checked, "Macro.Publisher", :value, "made"]) ==
               {:ok, {"fixture", "Macro.Publisher", :value, "made"}}

      assert pipeline(:expansion_rounds, [checked]) >= 2
    end

    test "compiled and fallback macro execution have identical expansion and isolated fresh state", %{
      tmp_dir: dir
    } do
      # Two sibling uses of one rule, each of which mints a binder. Whatever
      # freshening does, it has to do it per use-site: a single shared name here
      # would let one expansion's binder capture the other's.
      source =
        write!(
          dir,
          "macro.cure",
          """
          mod Macro.Parity
            macro Doubled
              syntax doubled <x: Code> becomes let <fresh h> = x in h + h

            fn first() -> Int = doubled 1
            fn second() -> Int = doubled 2
          """
        )

      assert {:ok, compiled} = check([source], dir, macro_execution: :compiled)
      assert {:ok, fallback} = check([source], dir, macro_execution: :core_fallback)
      assert pipeline(:expanded_syntax_dump, [compiled]) == pipeline(:expanded_syntax_dump, [fallback])
      assert pipeline(:fresh_name_sets, [compiled]) == pipeline(:fresh_name_sets, [fallback])
      assert pipeline(:sibling_expansions_disjoint?, [compiled])
    end
  end

  describe "canonical Core, closure, and diagnostics" do
    test "the semantic graph has one exhaustive edge vocabulary" do
      assert pipeline(:semantic_edge_kinds, []) == [
               :lexical_use,
               :qualified_reference,
               :prelude_symbol_use,
               :type_reference,
               :value_reference,
               :interface_provider,
               :implementation_selection,
               :macro_home,
               :macro_generated_reference,
               :generated_declaration_owner,
               :extern_owner,
               :runtime_call
             ]
    end

    test "canonical identity survives declaration order, lifting, totality, reachability, and emission", %{
      tmp_dir: dir
    } do
      sources = [
        "mod Identity.A\n  fn run() -> Int = same()\n  fn same() -> Int = 1\n",
        "mod Identity.A\n  fn same() -> Int = 1\n  fn run() -> Int = same()\n"
      ]

      dumps =
        for {source, index} <- Enum.with_index(sources) do
          path = write!(dir, "identity_#{index}.cure", source)
          assert {:ok, checked} = check([path], dir)
          assert pipeline(:all_core_globals_canonical?, [checked])
          assert pipeline(:totality_keys, [checked]) == pipeline(:reachability_keys, [checked])
          assert {:ok, closure} = pipeline(:emission_closure, [checked, "Identity.A", "run"])
          assert Enum.all?(closure, &match?({:definition, {"fixture", _, _, _}, _}, &1))
          pipeline(:normalized_core, [checked, "Identity.A", "run"])
        end

      assert Enum.uniq(dumps) |> length() == 1
    end

    test "every reachable key resolves or reports a typed predecessor path", %{tmp_dir: dir} do
      broken = write!(dir, "broken.cure", "mod Closure.Broken\n  fn run() -> Int = missing()\n")

      assert {:error,
              {:unresolved_global,
               %{
                 key: {"fixture", "Closure.Broken", :value, "missing"},
                 origin: origin,
                 closure_path: [
                   {"fixture", "Closure.Broken", :value, "run"},
                   {"fixture", "Closure.Broken", :value, "missing"}
                 ]
               }}} = check([broken], dir)

      assert origin.path == broken
      assert origin.line == 2
    end

    test "one provider failure suppresses dependent missing-module cascades", %{tmp_dir: dir} do
      provider = write!(dir, "provider.cure", "mod Failure.Provider\n  fn bad() -> Int = nope\n")
      a = write!(dir, "a.cure", "mod Failure.A\n  fn value() -> Int = Failure.Provider.bad()\n")
      b = write!(dir, "b.cure", "mod Failure.B\n  fn value() -> Int = Failure.Provider.bad()\n")

      assert {:error, diagnostics} = check([b, provider, a], dir, collect_diagnostics: true)
      assert Enum.count(diagnostics, &(&1.code == :provider_check_failed)) == 1
      refute Enum.any?(diagnostics, &(&1.code in [:missing_stdlib_module, :missing_module]))

      assert Enum.all?(diagnostics, fn diagnostic ->
               diagnostic.primary.span.path == provider or diagnostic.severity == :note
             end)
    end
  end

  describe "artifacts and incremental compilation" do
    test "interface hashes ignore bodies but include semantic interface and direct dependency hashes", %{
      tmp_dir: dir
    } do
      v1 = write!(dir, "v1.cure", "mod Hash.Provider\n  fn value() -> Int = 1\n")
      assert {:ok, first} = check([v1], dir)
      first_hash = pipeline(:interface_hash, [first, "Hash.Provider"])

      File.write!(v1, "mod Hash.Provider\n  fn value() -> Int = 2\n")
      assert {:ok, body_changed} = check([v1], dir)
      assert pipeline(:interface_hash, [body_changed, "Hash.Provider"]) == first_hash

      File.write!(v1, "mod Hash.Provider\n  fn value() -> Nat = 2\n")
      assert {:ok, signature_changed} = check([v1], dir)
      refute pipeline(:interface_hash, [signature_changed, "Hash.Provider"]) == first_hash
    end

    test "corrupt, stale, and undeclared interface artifacts are rejected before body checking", %{
      tmp_dir: dir
    } do
      provider = write!(dir, "provider.cure", "mod Artifact.Provider\n  fn value() -> Int = 1\n")

      consumer =
        write!(dir, "consumer.cure", "mod Artifact.Consumer\n  fn value() -> Int = Artifact.Provider.value()\n")

      artifacts = Path.join(dir, "artifacts")
      assert {:ok, checked} = check([provider], dir)
      assert :ok = pipeline(:write_interfaces, [checked, artifacts])

      assert {:ok, path} = pipeline(:interface_path, [artifacts, "Artifact.Provider"])
      assert :ok = pipeline(:corrupt_interface_for_test, [path, :dependency_hash])

      assert {:error, {:invalid_interface_artifact, %{module: "Artifact.Provider", reason: :hash_mismatch}}} =
               check([consumer], dir, interface_roots: [artifacts], forbid_source_fallback: true)
    end

    test "incremental invalidation follows checked semantic edges rather than discovery order", %{
      tmp_dir: dir
    } do
      provider = write!(dir, "provider.cure", "mod Inc.Provider\n  fn value() -> Int = 1\n")
      consumer = write!(dir, "consumer.cure", "mod Inc.Consumer\n  fn value() -> Int = Inc.Provider.value()\n")
      cache = Path.join(dir, "cache")
      assert {:ok, _} = check([consumer, provider], dir, cache: cache)

      File.write!(provider, "mod Inc.Provider\n  fn value() -> Int = 2\n")
      assert {:ok, body_only} = check([provider, consumer], dir, cache: cache)
      assert pipeline(:rebuilt_modules, [body_only]) == ["Inc.Provider"]

      # An added declaration changes the provider's interface without breaking
      # the consumer: the consumer must rebuild because the interface it was
      # checked against is gone, not because it stopped type-checking.
      File.write!(provider, "mod Inc.Provider\n  fn value() -> Int = 2\n  fn extra() -> Int = 3\n")
      assert {:ok, interface_change} = check([consumer, provider], dir, cache: cache)
      assert pipeline(:rebuilt_modules, [interface_change]) == ["Inc.Consumer", "Inc.Provider"]
    end
  end

  describe "isolation, entry points, and concrete regressions" do
    test "manifest, interfaces, and diagnostics are invariant under all file permutations", %{tmp_dir: dir} do
      a = write!(dir, "z.cure", "mod Perm.A\n  fn value() -> Int = 1\n")
      b = write!(dir, "m.cure", "mod Perm.B\n  fn value() -> Int = Perm.A.value()\n")
      c = write!(dir, "a.cure", "mod Perm.C\n  use Perm.B\n  fn value() -> Int = value()\n")

      observations =
        for paths <- permutations([a, b, c]) do
          assert {:ok, checked} = check(paths, dir, discovery_concurrency: Enum.random(1..4))

          {
            pipeline(:manifest_dump, [checked]),
            pipeline(:interface_hashes, [checked]),
            pipeline(:normalized_diagnostics, [checked])
          }
        end

      assert observations |> Enum.uniq() |> length() == 1
    end

    test "parse and print metadata do not alter semantic identity", %{tmp_dir: dir} do
      source = write!(dir, "metadata.cure", "mod Metadata.Stable\n  fn value() -> Int = 1\n")
      assert {:ok, original} = check([source], dir)
      assert {:ok, printed} = pipeline(:parse_print_recheck, [original, [metadata: :fresh]])
      assert pipeline(:manifest_dump, [original]) == pipeline(:manifest_dump, [printed])
      assert pipeline(:interface_hashes, [original]) == pipeline(:interface_hashes, [printed])
    end

    test "concurrent generations publish atomically and never consume staging artifacts", %{tmp_dir: dir} do
      source = write!(dir, "source.cure", "mod Atomic.Source\n  fn value() -> Int = 1\n")
      output = Path.join(dir, "output")

      tasks =
        for generation <- 1..4 do
          Task.async(fn ->
            check([source], dir, output: output, generation: generation, publication: :atomic)
          end)
        end

      results = Task.await_many(tasks, 30_000)
      assert Enum.all?(results, &match?({:ok, _}, &1))
      assert {:ok, published} = pipeline(:open_published_generation, [output])
      assert pipeline(:generation_complete?, [published])
      refute pipeline(:contains_staging_reference?, [published])
    end

    test "all compilation entry points submit the same manifest and produce the same interface", %{
      tmp_dir: dir
    } do
      source = write!(dir, "entry.cure", "mod Entry.Point\n  fn value() -> Int = 1\n")
      entries = [:project, :stdlib, :incremental, :test, :docs, :macro, :repl, :bundle, :escript]

      results =
        for entry <- entries do
          assert {:ok, result} =
                   pipeline(:check_entry_point, [entry, [source], [package: "fixture", source_roots: [dir]]])

          {pipeline(:manifest_dump, [result]), pipeline(:interface_hash, [result, "Entry.Point"])}
        end

      assert results |> Enum.uniq() |> length() == 1
    end

    # Checking every stdlib module from cold is minutes of real work, not a hang.
    @tag timeout: :timer.minutes(10)
    test "the real stdlib universe never elaborates unrelated provider bodies to construct ambient scope" do
      paths = Path.wildcard("lib/std/**/*.cure")

      assert {:ok, checked} =
               pipeline(:check, [paths, [module_pipeline: :canonical, package: "stdlib", kind: :stdlib]])

      refute pipeline(:body_elaboration_edge?, [checked, "Std.Bool", "Std.Binary"])
      assert pipeline(:provider_body_elaboration_count, [checked, "Std.Binary", :during_prelude_bootstrap]) == 0
    end

    # Checking every stdlib module from cold is minutes of real work, not a hang.
    @tag timeout: :timer.minutes(10)
    test "nominal String and reversed regex filenames compile without ordering-only uses" do
      paths = Path.wildcard("lib/std/**/*.cure") |> Enum.reverse()

      assert {:ok, checked} =
               pipeline(:check, [paths, [module_pipeline: :canonical, package: "stdlib", kind: :stdlib]])

      assert pipeline(:type_representation, [checked, "Std.String", "String"]) == :nominal
      assert pipeline(:checked?, [checked, "Std.Regex.Syntax.Model"])
      assert pipeline(:diagnostics, [checked]) == []
    end

    test "the canonical pipeline reports no alternate semantic authorities or fallback paths", %{tmp_dir: dir} do
      source = write!(dir, "authority.cure", "mod Authority.One\n  fn value() -> Int = 1\n")
      assert {:ok, checked} = check([source], dir)

      assert pipeline(:semantic_authorities, [checked]) == [:module_manifest, :checked_interfaces]

      assert pipeline(:alternate_path_counts, [checked]) == %{
               beam_export_probes: 0,
               source_jit_loads: 0,
               stamped_ast_scans: 0,
               late_bare_recoveries: 0,
               entry_point_graphs: 0,
               mutable_environment_merges: 0,
               codegen_rechecks: 0
             }
    end
  end

  defp check(paths, dir, extra \\ []) do
    pipeline(:check, [
      paths,
      Keyword.merge([module_pipeline: :canonical, package: "fixture", source_roots: [dir]], extra)
    ])
  end

  defp resolve(checked, module, name), do: pipeline(:resolve, [checked, module, :value, name])

  defp semantic_edge?(checked, source, target, kind),
    do: pipeline(:semantic_edge?, [checked, source, target, kind])

  defp pipeline(function, arguments), do: apply(Cure.Compiler.ModulePipeline, function, arguments)

  defp permutations([]), do: [[]]

  defp permutations(values) do
    for value <- values,
        rest <- permutations(List.delete(values, value)),
        do: [value | rest]
  end

  defp write!(dir, name, source) do
    path = Path.join(dir, name)
    File.write!(path, source)
    path
  end
end
