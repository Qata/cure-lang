defmodule Cure.DiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Adapter, Label, ProvenanceFrame, Renderer, SourceRegistry, Suggestion, TextEdit}

  setup do
    source = "mod Demo\n  fn answer() -> Int = unknowñ\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:demo, source, "src/demo.cure")
    start = :binary.match(source, "unknowñ") |> elem(0)
    {:ok, span} = SourceRegistry.span(registry, :demo, start, start + byte_size("unknowñ"))
    %{registry: registry, span: span}
  end

  test "source spans retain byte offsets and Unicode display columns", %{span: span} do
    assert span.start_line == 2
    assert span.start_column == 24
    assert span.end_column == 31
    assert span.end_byte - span.start_byte == 8
  end

  test "all renderers consume the same structured diagnostic", %{registry: registry, span: span} do
    replacement = %TextEdit{span: span, replacement: "known"}

    diagnostic =
      Diagnostic.new(
        code: "E101",
        key: :unknown_value,
        severity: :error,
        title: "Unknown value",
        message: "`unknowñ` is not available in this scope.",
        primary: %Label{span: span, style: :primary, message: "not found"},
        notes: ["names are namespace-sensitive"],
        suggestions: [
          %Suggestion{message: "replace it with `known`", applicability: :maybe_incorrect, edits: [replacement]}
        ],
        provenance: [%ProvenanceFrame{kind: :macro_expansion, name: "actor Worker"}],
        payload: %{namespace: :value, name: "unknowñ"}
      )

    plain = Renderer.plain(diagnostic, registry)
    machine = Renderer.to_map(diagnostic)
    lsp = Renderer.lsp(diagnostic, registry)
    host = Renderer.code_diagnostic(diagnostic)
    mix = Renderer.mix_diagnostic(diagnostic)

    assert plain =~ "error[E101]: Unknown value"
    assert plain =~ "2 |   fn answer() -> Int = unknowñ"
    assert plain =~ "^^^^^^^ not found"
    assert plain =~ "expansion: actor Worker"
    assert machine["code"] == lsp["code"]
    assert machine["primary"]["span"]["start_byte"] == span.start_byte
    assert lsp["range"]["start"] == %{"line" => 1, "character" => 23}
    assert Jason.decode!(Renderer.json(diagnostic))["payload"]["name"] == "unknowñ"
    assert host.details == diagnostic
    assert host.position == {2, 24}
    assert mix.compiler_name == "Cure"
    assert {:ok, ^diagnostic} = Renderer.from_host_diagnostic(mix)
  end

  test "LSP positions count UTF-16 code units rather than Unicode scalars" do
    registry = SourceRegistry.new() |> SourceRegistry.register(:astral, "a😀b", "astral.cure")
    {:ok, span} = SourceRegistry.span(registry, :astral, 5, 6)
    label = %Label{span: span, style: :primary}

    diagnostic =
      Diagnostic.new(
        code: "E101",
        key: :unknown_value,
        severity: :error,
        title: "Unknown",
        message: "missing",
        primary: label
      )

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 0, "character" => 3},
             "end" => %{"line" => 0, "character" => 4}
           }
  end

  test "stable category extraction supports diagnostics and legacy shapes" do
    diagnostic =
      Diagnostic.new(code: "E101", key: :unknown_value, severity: :error, title: "Unknown", message: "missing")

    assert Diagnostic.key(diagnostic) == :unknown_value
    assert Diagnostic.key({:error, {:unknown_global, :missing}}) == :unknown_global
    assert Diagnostic.code({:extern_untyped_head, "needs a type (E056)", line: 2}) == "E056"
  end

  test "unknown-name adapter retains namespace, offender, candidates, and source", %{registry: registry, span: span} do
    diagnostic =
      Adapter.from_error({:unknown_constructor, :Nothng},
        span: span,
        candidates: [:Nothing, :Something],
        checking: :decode
      )

    assert diagnostic.code == "E091"
    assert diagnostic.key == :unknown_name
    assert diagnostic.payload.namespace == :constructor
    assert diagnostic.payload.name == "Nothng"
    assert diagnostic.payload.checking == :decode
    assert Renderer.plain(diagnostic, registry) =~ "`Nothng` was not found"
    assert hd(diagnostic.suggestions).message =~ "`Nothing`"
  end

  test "plain rendering includes cross-file secondary labels", %{registry: registry, span: span} do
    registry = SourceRegistry.register(registry, :definition, "type Token = Token\n", "src/token.cure")
    {:ok, definition_span} = SourceRegistry.span(registry, :definition, 5, 10)

    diagnostic =
      Diagnostic.new(
        code: "E101",
        key: :type_mismatch,
        severity: :error,
        title: "Type mismatch",
        message: "The values have different types.",
        primary: %Label{span: span, style: :primary, message: "used here"},
        secondary: [%Label{span: definition_span, style: :secondary, message: "defined here"}]
      )

    rendered = Renderer.plain(diagnostic, registry)
    assert rendered =~ "::: src/token.cure:1:6"
    assert rendered =~ "1 | type Token = Token"
    assert rendered =~ "^^^^^ defined here"
  end

  test "lifted module failures are reported at the public macro boundary" do
    diagnostic =
      Adapter.from_error(
        {:lift_module_error,
         %{
           module: "Cure.Actor.Worker",
           behaviour: :GenServer,
           source_provenance: %{file: "worker.cure", line: 3, col: 1, macro: "actor"},
           expansion_provenance: [%{keyword: "actor", line: 3, col: 1}],
           cause: {:unknown_global, :MissingMessage}
         }}
      )

    assert diagnostic.code == "E092"
    assert diagnostic.title == "Actor expansion failed"
    assert diagnostic.message =~ "`MissingMessage` is not available"
    assert diagnostic.payload.cause.code == "E091"
    assert diagnostic.payload.cause.payload.name == "MissingMessage"
    refute diagnostic.message =~ "{:unknown_global"
    assert Renderer.plain(diagnostic) =~ "edit the `actor` declaration instead"
  end

  test "invalid spans and codes are rejected", %{registry: registry} do
    assert {:error, :span_out_of_bounds} = SourceRegistry.span(registry, :demo, 0, 10_000)

    assert_raise ArgumentError, fn ->
      Diagnostic.new(code: "unknown", key: :bad, severity: :error, title: "Bad", message: "bad")
    end
  end
end
