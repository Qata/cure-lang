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
    terminal = Renderer.terminal(diagnostic, registry, color: true)
    machine = Renderer.to_map(diagnostic)
    lsp = Renderer.lsp(diagnostic, registry)
    host = Renderer.code_diagnostic(diagnostic)
    mix = Renderer.mix_diagnostic(diagnostic)

    assert plain =~ "-- UNKNOWN VALUE [E101]"
    assert terminal =~ IO.ANSI.cyan() <> "-- UNKNOWN VALUE [E101]"
    assert plain =~ "2 |   fn answer() -> Int = unknowñ"
    assert plain =~ "^^^^^^^ not found"
    assert terminal =~ IO.ANSI.red() <> "^^^^^^^" <> IO.ANSI.reset()
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

  test "parser diagnostics underline the full unexpected token" do
    source = "mod Demo\n  fn run(] -> Int = 1\n"
    error = {:parse_error, [{:expected, :rparen, :got, :arrow, 2, 12}]}
    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "demo.cure", source)

    assert diagnostic.primary.span.end_column - diagnostic.primary.span.start_column == 2
    assert Renderer.plain(diagnostic, registry) =~ "^^ this syntax does not fit here"

    assert Renderer.terminal(diagnostic, registry, color: true) =~
             IO.ANSI.red() <> "^^" <> IO.ANSI.reset()
  end

  test "parser diagnostic widths come from lexer spans rather than a token-width table" do
    source = "mod Demo\n  fn run(x) => Int = x\n"
    error = {:parse_error, [{:expected, :arrow, :got, :fat_arrow, 2, 13}]}
    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "demo.cure", source)

    assert diagnostic.primary.span.end_byte - diagnostic.primary.span.start_byte == 2
    assert binary_part(source, diagnostic.primary.span.start_byte, 2) == "=>"
    assert Renderer.plain(diagnostic, registry) =~ "^^ this syntax does not fit here"
  end

  test "lexer failures explain authored syntax without exposing raw tuples" do
    source = "mod Demo\n\tfn run() = 1\n"
    error = {:lex_error, {:tab_not_allowed, 2, 1}}
    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "demo.cure", source)

    assert diagnostic.code == "E094"
    assert diagnostic.title == "Tabs are not valid indentation"
    assert Renderer.plain(diagnostic, registry) =~ "indentation uses spaces"
    refute Renderer.plain(diagnostic, registry) =~ "{:tab_not_allowed"
  end

  test "unique missing lexer delimiters provide an insertion edit" do
    source = "\"not closed"
    error = {:lex_error, {:unterminated_string, 1, 1}}
    {diagnostic, _registry} = Cure.Compiler.Errors.to_diagnostic(error, "demo.cure", source)

    assert [%Suggestion{applicability: :machine_applicable, edits: [%TextEdit{replacement: "\""}]}] =
             diagnostic.suggestions
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

    assert Renderer.lsp(diagnostic, registry, :utf8)["range"]["start"]["character"] == 5
    assert Renderer.lsp(diagnostic, registry, :utf32)["range"]["start"]["character"] == 2
  end

  test "one-based source coordinates normalize to canonical byte spans" do
    registry = SourceRegistry.new() |> SourceRegistry.register(:source, "αβ\nvalue\n", "unicode.cure")
    assert {:ok, span} = SourceRegistry.span_at(registry, :source, 2, 2, 3)
    assert {span.start_byte, span.end_byte} == {6, 9}
    assert {span.start_line, span.start_column, span.end_column} == {2, 2, 5}
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

  test "name candidates rank usable namespace and arity matches before spelling" do
    diagnostic =
      Adapter.unknown_name(:value, "map",
        arity: 2,
        candidates: [
          %{name: "map", namespace: :type, arity: 2, visibility: :public},
          %{name: "map", namespace: :value, arity: 2, visibility: :private},
          %{name: "mop", namespace: :value, arity: 1, visibility: :public},
          %{name: "map_values", namespace: :value, arity: 2, visibility: :private},
          %{name: "map_values", namespace: :value, arity: 2, visibility: :public}
        ]
      )

    assert diagnostic.payload.candidates == ["map_values", "mop", "map"]
    assert hd(diagnostic.payload.candidate_details).visibility == :public
    assert hd(diagnostic.payload.candidate_details).arity == 2
  end

  test "conversion failures present Cure types and retain Core payloads", %{registry: registry, span: span} do
    actual = {:data, :"Std.Bool#Bool", [], []}
    expected = {:data, :"Std.Int#Int", [], []}
    diagnostic = Adapter.from_error({:conversion_failure, actual, expected}, span: span)

    assert diagnostic.code == "E093"
    assert Diagnostic.message(diagnostic) == "Expected `Int`, but found `Bool`."
    assert diagnostic.payload.expected_surface == "Int"
    assert diagnostic.payload.actual_surface == "Bool"
    assert diagnostic.payload.expected_core == inspect(expected)
    assert Renderer.plain(diagnostic, registry) =~ "this expression has the wrong type"
  end

  test "type mismatch prose follows its expectation origin", %{registry: registry, span: span} do
    annotation_origin = %Cure.Diagnostic.ExpectationOrigin{kind: :annotation, span: span}
    condition_origin = %Cure.Diagnostic.ExpectationOrigin{kind: :condition}

    annotation =
      Adapter.from_error(%Cure.Diagnostic.TypeProblem{
        kind: :type_mismatch,
        actual: "String",
        expected: "Int",
        origin: annotation_origin,
        span: span
      })

    condition =
      Adapter.from_error(%Cure.Diagnostic.TypeProblem{
        kind: :type_mismatch,
        actual: "Int",
        expected: "Bool",
        origin: condition_origin,
        span: span
      })

    assert annotation.title == "Annotation does not match"
    assert Renderer.plain(annotation, registry) =~ "type written in its annotation"
    assert condition.title == "Condition is not boolean"
    assert Renderer.plain(condition, registry) =~ "condition must produce `Bool`"
    assert Renderer.terminal(condition, registry, color: :always) =~ IO.ANSI.green() <> "Bool"
    assert condition.payload.actual_core == inspect("Int")
  end

  test "source checking context upgrades kernel conversion failures", %{registry: registry, span: span} do
    diagnostic =
      Adapter.from_error(
        {:source_context, {:conversion_failure, {:bool_type}, {:int_type}},
         %{
           checking: :answer,
           span: span,
           expression_category: :literal,
           expectation_origin: :annotation
         }}
      )

    assert diagnostic.title == "Annotation does not match"
    assert diagnostic.payload.origin.kind == :annotation
    assert diagnostic.payload.origin.owner == :answer
    assert diagnostic.payload.expression_category == :literal
    assert diagnostic.payload.debug.cause == {:conversion_failure, {:bool_type}, {:int_type}}
    assert Renderer.plain(diagnostic, registry) =~ "type written in its annotation"
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
    assert rendered =~ "at src/token.cure:1:6"
    assert rendered =~ "1 | type Token = Token"
    assert rendered =~ "----- defined here"
  end

  test "carets align after tabs and multiline labels underline every covered line" do
    source = "head\n\tbody\nlast"
    registry = SourceRegistry.new() |> SourceRegistry.register(:multi, source, "multi.cure")
    {:ok, span} = SourceRegistry.span(registry, :multi, 2, 13)

    diagnostic =
      Diagnostic.new(
        code: "E101",
        key: :type_mismatch,
        severity: :error,
        title: "Type mismatch",
        message: "covered expression failed",
        primary: %Label{span: span, style: :primary, message: "whole expression"}
      )

    rendered = Renderer.plain(diagnostic, registry)
    assert rendered =~ "1 | head\n  >   ^^"
    assert rendered =~ "2 |     body\n  > ^^^^^^^^"
    assert rendered =~ "3 | last\n  > ^^ whole expression"
  end

  test "zero-width insertion spans still render one caret" do
    registry = SourceRegistry.new() |> SourceRegistry.register(:insert, "abc", "insert.cure")
    {:ok, span} = SourceRegistry.span(registry, :insert, 1, 1)

    diagnostic =
      Diagnostic.new(
        code: "E101",
        key: :missing_token,
        severity: :error,
        title: "Missing token",
        message: "insert a token",
        primary: %Label{span: span, style: :primary, message: "insert here"}
      )

    assert Renderer.plain(diagnostic, registry) =~ "1 | abc\n  |  ^ insert here"
  end

  test "machine-applicable structured edits become LSP quick fixes", %{registry: registry, span: span} do
    diagnostic =
      Diagnostic.new(
        code: "E091",
        key: :unknown_name,
        severity: :error,
        title: "Unknown value",
        message: "The value is not in scope.",
        primary: %Label{span: span, style: :primary},
        suggestions: [
          %Suggestion{
            message: "Replace it with `known`",
            applicability: :machine_applicable,
            edits: [%TextEdit{span: span, replacement: "known"}]
          }
        ]
      )

    lsp = Renderer.lsp(diagnostic, registry)
    assert [action] = Cure.LSP.Server.compute_code_actions("file:///fallback.cure", [lsp])
    assert action["title"] == "Replace it with `known`"

    assert [{uri, edits}] = Map.to_list(get_in(action, ["edit", "changes"]))
    assert String.ends_with?(uri, "/src/demo.cure")

    assert edits == [
             %{
               "range" => %{
                 "start" => %{"line" => 1, "character" => 23},
                 "end" => %{"line" => 1, "character" => 30}
               },
               "newText" => "known"
             }
           ]
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
    assert Diagnostic.message(diagnostic) =~ "`MissingMessage` is not available"
    assert diagnostic.payload.cause.code == "E091"
    assert diagnostic.payload.cause.payload.name == "MissingMessage"
    refute Diagnostic.message(diagnostic) =~ "{:unknown_global"
    assert Renderer.plain(diagnostic) =~ "edit the `actor`"
    assert Renderer.plain(diagnostic) =~ "declaration instead"

    machine = Jason.decode!(Renderer.json(diagnostic))
    assert machine["payload"]["cause"]["code"] == "E091"
    assert machine["body"]["kind"] == "paragraph"
  end

  test "compiler presentation attaches a real caret to an authored macro failure" do
    source = "mod Demo\n  actor Worker\n"

    error =
      {:lift_module_error,
       %{
         module: "Cure.Actor.Worker",
         behaviour: :GenServer,
         source_provenance: %{file: "worker.cure", line: 2, col: 3, macro: "actor"},
         expansion_provenance: [%{keyword: "actor", line: 2, col: 3}],
         cause: {:unknown_global, :MissingMessage}
       }}

    rendered = Cure.Compiler.Errors.format_with_source(error, "worker.cure", source)
    assert rendered =~ "2 |   actor Worker"
    assert rendered =~ "  ^ this `actor` declaration generated the failing module"
    refute rendered =~ "{:unknown_global"
  end

  test "invalid spans and codes are rejected", %{registry: registry} do
    assert {:error, :span_out_of_bounds} = SourceRegistry.span(registry, :demo, 0, 10_000)

    assert_raise ArgumentError, fn ->
      Diagnostic.new(code: "unknown", key: :bad, severity: :error, title: "Bad", message: "bad")
    end
  end

  test "unregistered domain errors fail loudly instead of becoming generic diagnostics" do
    assert_raise Cure.Diagnostic.UnhandledError, ~r/no registered diagnostic conversion/, fn ->
      Adapter.from_error({:new_unregistered_error, :detail})
    end

    assert_raise Cure.Diagnostic.UnhandledError, fn ->
      Cure.Compiler.Errors.format_error({:new_unregistered_error, :detail}, "source.cure")
    end
  end

  test "operational failures use stable diagnostic codes" do
    diagnostic = Cure.Diagnostic.Operational.file_read("Cure.toml", :enoent)
    assert diagnostic.code == "E095"
    assert diagnostic.key == :file_read
    assert diagnostic.payload.path == "Cure.toml"
  end

  test "migration warnings render as rich diagnostics" do
    warning =
      Cure.Diagnostic.Operational.migration_warning(%{
        rule: :legacy,
        file: "demo.cure",
        line: 3,
        message: "use the modern form"
      })

    assert warning.severity == :warning
    assert warning.code == "W001"
    assert Cure.Diagnostic.Renderer.plain(warning) =~ "W001"
    assert Cure.Diagnostic.Renderer.plain(warning) =~ "use the modern form"
  end

  test "specialized operational warnings retain stable codes" do
    assert Cure.Diagnostic.Operational.export_unmappable("dependent").code == "E068"
    assert Cure.Diagnostic.Operational.snap_missing("missing.cure").code == "E070"
    assert Cure.Diagnostic.Operational.configuration_warning("bad setting").code == "W002"
  end

  test "task usage and artifact failures are structured" do
    assert Cure.Diagnostic.Operational.usage("bad args").code == "E099"
    assert Cure.Diagnostic.Operational.artifact_error("missing").code == "E100"
  end

  test "codegen-wrapped unknown globals remain structured" do
    rendered = Cure.Compiler.Errors.format_error({:codegen_error, {:unknown_global, :Missing}}, "demo.cure")
    assert rendered =~ "E091"
    refute rendered =~ "{:unknown_global"
  end

  test "payload-bearing unknown names retain resolution context" do
    diagnostic =
      Adapter.from_error(
        {:unknown_name, %{namespace: :type, name: :Missing, candidates: [:Maybe], arity: 1, checking: :Demo}}
      )

    assert diagnostic.code == "E091"
    assert diagnostic.payload.namespace == :type
    assert diagnostic.payload.candidates == ["Maybe"]
    assert diagnostic.payload.arity == 1
    assert diagnostic.payload.checking == :Demo
  end

  test "structured body is authoritative and machine output retains its semantics" do
    diagnostic =
      Diagnostic.new(
        code: "E093",
        key: :conversion_failure,
        severity: :error,
        title: "Type mismatch",
        body:
          Cure.Diagnostic.Doc.paragraph([
            "Expected",
            Cure.Diagnostic.Doc.emphasis(:expected, "Int"),
            "but found",
            Cure.Diagnostic.Doc.emphasis(:observed, "Bool")
          ])
      )

    refute Map.has_key?(diagnostic, :message)
    assert Diagnostic.message(diagnostic) == "Expected Int but found Bool"
    assert Renderer.to_map(diagnostic)["body"]["kind"] == "paragraph"
  end

  test "renderer wraps at an explicit width and normalizes the banner path", %{registry: registry, span: span} do
    diagnostic =
      Diagnostic.new(
        code: "E091",
        key: :unknown_name,
        severity: :error,
        title: "Unknown value",
        message: "This deliberately long explanation wraps at the requested terminal width.",
        primary: %Label{span: span, style: :primary}
      )

    rendered = Renderer.plain(diagnostic, registry, width: 38, project_root: File.cwd!())
    [banner | _] = String.split(rendered, "\n")

    assert banner =~ "[E091]"
    assert String.ends_with?(banner, " src/demo.cure")
    assert rendered =~ "This deliberately long explanation\nwraps at the requested terminal width."
  end

  test "auto color emits no ANSI when output is redirected" do
    diagnostic =
      Diagnostic.new(code: "E095", key: :file_read, severity: :error, title: "File error", message: "missing")

    {:ok, output} = StringIO.open("")

    refute Renderer.terminal(diagnostic, nil, color: :auto, output_device: output) =~ "\e["
    assert Renderer.terminal(diagnostic, nil, color: :always) =~ IO.ANSI.cyan()
    refute Renderer.terminal(diagnostic, nil, color: :never) =~ "\e["
  end
end
