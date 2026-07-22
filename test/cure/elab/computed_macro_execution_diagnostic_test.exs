defmodule Cure.Elab.ComputedMacroExecutionDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer

  @source "mod M\n  fn result() -> Int = expand here\nend\n"
  @meta [keyword: "expand", line: 2, col: 24]

  test "an incompatible reflected input explains the expander contract at the invocation" do
    {diagnostic, registry} =
      Errors.to_diagnostic(
        {:computed_macro_error, @meta, :no_compatible_macro_input},
        "input.cure",
        @source
      )

    assert diagnostic.code == "E092"
    assert diagnostic.payload.reason == %{kind: :incompatible_input}

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- COMPUTED MACRO EXPANDER DOES NOT ACCEPT ITS INPUT [E092] --------- input.cure

             The `expand` macro's expander cannot be applied to any supported reflection of
             this invocation. Its parameter type must accept the macro's generated syntax
             record, its direct captured fields, or generic `Syntax`.

             at input.cure:2:24
             2 |   fn result() -> Int = expand here
               |                        ^^^^^^ this invocation cannot be passed to its expander

             Note: The invocation is authored source; change the expander's input type or the
                   macro rule that constructs it.

             Hint: Make the expander accept its generated syntax record, captured fields, or generic `Syntax`
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == range(1, 23, 29)
  end

  test "bounded evaluation exhaustion explains termination without exposing Core" do
    {diagnostic, registry} =
      Errors.to_diagnostic(
        {:computed_macro_error, @meta, :normalization_fuel_exhausted},
        "fuel.cure",
        @source
      )

    assert diagnostic.code == "E092"
    assert diagnostic.payload.reason == %{kind: :evaluation_budget_exhausted}

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- COMPUTED MACRO EXPANSION DID NOT TERMINATE [E092] ----------------- fuel.cure

             The `expand` macro's expander exceeded the compiler's bounded evaluation budget
             before producing syntax. This usually means the expander recurses without
             reaching a smaller input or performs unexpectedly large compile-time work.

             at fuel.cure:2:24
             2 |   fn result() -> Int = expand here
               |                        ^^^^^^ this invocation exhausted the expansion budget

             Note: The compiler stopped evaluation safely; no partial generated syntax was
                   accepted.

             Hint: Make recursive expansion calls structurally smaller, or move large work out of compile-time evaluation
             """)

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(1, 23, 29)
    assert lsp["data"]["payload"]["reason"] == %{"kind" => "evaluation_budget_exhausted"}
    refute inspect(lsp) =~ "Core"
  end

  defp range(line, start_character, end_character) do
    %{
      "start" => %{"line" => line, "character" => start_character},
      "end" => %{"line" => line, "character" => end_character}
    }
  end
end
