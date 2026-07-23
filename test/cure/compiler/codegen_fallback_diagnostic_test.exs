defmodule Cure.Compiler.CodegenFallbackDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{BeamWriter, Errors}
  alias Cure.Diagnostic.Adapter.Codegen
  alias Cure.Diagnostic.Renderer

  test "an injected BEAM rejection keeps stage, module, source, reason, and fingerprint" do
    module = :"Cure.InjectedBrokenBeam"

    forms = [
      {:attribute, 1, :module, module},
      {:attribute, 1, :export, [missing: 0]}
    ]

    assert {:error, errors, warnings} = BeamWriter.compile_forms(forms)
    assert errors != []

    reason =
      {:codegen_failure,
       %{
         stage: :beam_writer,
         module: module,
         file: "injected_failure.cure",
         reason: {:beam_lint, errors, warnings}
       }}

    {diagnostic, registry} = Errors.to_diagnostic(reason, "injected_failure.cure", "mod InjectedFailure\nend\n")
    rendered = Renderer.plain(diagnostic, registry, width: 100)

    assert diagnostic.code == "E101"
    assert diagnostic.payload.stage == :beam_writer
    assert diagnostic.payload.module == module
    assert diagnostic.payload.file == "injected_failure.cure"
    assert diagnostic.payload.reason != ""
    assert diagnostic.payload.fingerprint =~ ~r/^[0-9a-f]{12}$/

    assert rendered =~ "Stage: `beam_writer`."
    assert rendered =~ "Module: `Cure.InjectedBrokenBeam`."
    assert rendered =~ "Source: `injected_failure.cure`."
    assert rendered =~ "Underlying"
    assert rendered =~ "reason: #{diagnostic.payload.reason}."
    assert rendered =~ "Diagnostic fingerprint: `#{diagnostic.payload.fingerprint}`."
    refute rendered =~ "The compiler could not produce a valid BEAM artifact for this source.\n\nNote:"

    assert :ok =
             Cure.Diagnostic.Registry.validate_exercised_producer_fixtures([:internal_failure_beam_writer],
               only_producers: [:beam_writer]
             )

    direct =
      Codegen.from_error(reason,
        codegen_stage: :ignored,
        source_file: "also-ignored.cure"
      )

    assert direct.code == diagnostic.code
    assert direct.title == diagnostic.title
    assert direct.body == diagnostic.body
    assert direct.payload == diagnostic.payload
  end

  test "fallback fingerprints are stable for the same failure and differ with stage" do
    base = %{
      stage: :beam_writer,
      module: :"Cure.StableFailure",
      file: "stable_failure.cure",
      reason: {:beam_lint, [:deliberate_failure]}
    }

    {first, _registry} = Errors.to_diagnostic({:codegen_failure, base}, base.file, "")
    {second, _registry} = Errors.to_diagnostic({:codegen_failure, base}, base.file, "")

    {other_stage, _registry} =
      Errors.to_diagnostic({:codegen_failure, %{base | stage: :beam_loader}}, base.file, "")

    assert first.payload.fingerprint == second.payload.fingerprint
    refute first.payload.fingerprint == other_stage.payload.fingerprint
  end
end
