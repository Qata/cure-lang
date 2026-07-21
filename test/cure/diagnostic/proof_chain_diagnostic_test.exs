defmodule Cure.Diagnostic.ProofChainDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, Lexer, Parser}
  alias Cure.Diagnostic.{Renderer, Sink}

  test "E109 preserves authored ranges and projects through every renderer" do
    source = "proof chain\n  first\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "chain_syntax.cure", emit_events: false)
    assert {:error, [reason | _]} = Parser.parse(tokens, file: "chain_syntax.cure", emit_events: false)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "chain_syntax.cure", source)
    assert diagnostic.code == "E109"
    assert diagnostic.key == :proof_chain_syntax
    assert diagnostic.payload.kind == :missing_relation

    plain = Renderer.plain(diagnostic, registry)
    terminal = Renderer.terminal(diagnostic, registry, color: :always, width: 80)
    json = diagnostic |> Renderer.json() |> Jason.decode!()
    lsp = Sink.render(Sink.new(format: :lsp, registry: registry, position_encoding: :utf16), diagnostic)

    assert plain =~ "PROOF CHAIN STEP IS MISSING `==`"
    assert terminal =~ "\e["
    assert json["code"] == "E109"
    assert lsp["code"] == "E109"
    assert lsp["range"]["start"]["line"] == 1
  end

  test "E109 owns every inline chain structure failure" do
    fixtures = [
      {:empty_chain, "proof chain\n"},
      {:missing_relation, "proof chain\n  first\n"},
      {:missing_right_side, "proof chain\n  first\n    == because evidence\n"},
      {:missing_because, "proof chain\n  first\n    == second\n"},
      {:first_step_previous, "proof chain\n  _\n    == second\n    because evidence\n"}
    ]

    for {variant, source} <- fixtures do
      assert {:ok, tokens} = Lexer.tokenize(source, file: "#{variant}.cure", emit_events: false)
      assert {:error, reasons} = Parser.parse(tokens, file: "#{variant}.cure", emit_events: false)

      assert Enum.any?(reasons, fn reason ->
               {diagnostic, _registry} = Errors.to_diagnostic(reason, "#{variant}.cure", source)
               diagnostic.code == "E109" and diagnostic.payload.kind == variant
             end)
    end
  end

  test "E110 blames because evidence rather than generated transitivity" do
    source = """
    mod BadChainDiagnostic
      use Std.Equivalent
      fn proof(x: Int) -> Equivalent(Int, x, x) = proof chain
        x
          == 1
          because reflexive(x)
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: "chain_type.cure", emit_events: false)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "chain_type.cure", source)
    assert diagnostic.code == "E110"
    assert diagnostic.payload.kind == :wrong_justification
    assert diagnostic.payload.step_index == 0

    plain = Renderer.plain(diagnostic, registry)
    json = diagnostic |> Renderer.json() |> Jason.decode!()
    lsp = Renderer.lsp(diagnostic, registry, :utf16)

    assert plain =~ "because reflexive(x)"
    assert plain =~ "this evidence proves a different proposition"
    refute plain =~ "generated trans"
    assert json["payload"]["step_index"] == 0
    assert lsp["code"] == "E110"
    assert lsp["range"]["start"]["line"] == 5
  end

  test "E110 labels adjacent endpoints with different carriers" do
    source = """
    mod CarrierMismatch
      use Std.Equivalent
      fn proof(x: Int) -> Equivalent(Int, x, x) = proof chain
        x
          == 1.0
          because reflexive(x)
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: "chain_carrier.cure", emit_events: false)

    {diagnostic, registry} = Errors.to_diagnostic(reason, "chain_carrier.cure", source)
    assert diagnostic.code == "E110"
    assert diagnostic.payload.kind == :adjacent_endpoints
    assert diagnostic.payload.step_index == 0
    assert length(diagnostic.secondary) >= 1
    assert Renderer.plain(diagnostic, registry) =~ "previous endpoint"
  end
end
