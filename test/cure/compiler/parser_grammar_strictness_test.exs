defmodule Cure.Compiler.ParserGrammarStrictnessTest do
  @moduledoc """
  Two ways the parser accepted syntax the spec forbids.

  **A keyword slot that checked only the token type.** `expect(state, expected_type)`
  compares `token.type` and never `token.value`, so `expect(state, :keyword)` in a slot
  documented — by the comment directly above it — as consuming one specific keyword
  swallowed *any* keyword. `impl Show when Int` parsed as `impl Show for Int`. No error
  was recorded, and since the keyword's value never reaches the AST, no later stage could
  notice the substitution either. `expect_keyword/2`, which checks both, already existed
  and was already used elsewhere. The implementation forms still use it for `for`.
  Supervisor children have since moved to source-defined syntax-family productions;
  their literal `as` segment is checked by that grammar matcher instead.

  **Non-associativity that was never implemented.** The spec's operator table and
  `Precedence`'s moduledoc both say comparison, range, and the Melquiades send are
  non-associative and that the parser rejects chaining. It didn't. `right_bp = left_bp + 1`
  is exactly what a *left*-associative operator uses: it stops the operator from swallowing
  a peer on its own right-hand side, and does nothing to stop the Pratt loop from picking
  the freshly-built node back up as a new left operand at the caller's `min_bp`. So
  `a == b == c` left-chained, and `a <-| b <-| c` nested into two sends — the first send's
  return value re-sent to `c`, the exact fan-out `Precedence`'s moduledoc says
  non-associativity exists to prevent. Rejection now lives in the loop, where the token
  after the operator is visible.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Renderer

  defp parse_raw(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    Parser.parse(tokens, emit_events: false)
  end

  defp parse!(source) do
    assert {:ok, ast} = parse_raw(source)
    ast
  end

  describe "a keyword slot accepts only its own keyword" do
    test "the documented supervisor surface accepts assignments and bare worker children" do
      source = """
      sup App.Root
        strategy = :one_for_one
        intensity = 3
        period = 5
        children
          Counter as counter
      """

      assert {:ok, _} = parse_raw(source)
    end

    test "the real compiler parser path accepts the supervisor header" do
      source = "sup App.Root\n  children []\n"
      assert {:ok, _} = Cure.Compiler.parse_source(source, file: "sup.cure")
    end

    test "`impl Proto for Type` rejects another keyword in place of `for`" do
      assert {:error, _} = parse_raw("impl Show when Int\n  fn show(x: Int) -> String = \"x\"\n")
    end

    test "`implementation Iface for Type` rejects another keyword in place of `for`" do
      assert {:error, _} =
               parse_raw("implementation Show when Int\n  fn show(x: Int) -> String = \"x\"\n")
    end

    test "a supervisor child production rejects another keyword in place of `as`" do
      assert {:error, _} =
               parse_raw("sup App.Root\n  children\n    actor Counter when counter\n")
    end

    test "the correct keyword still parses" do
      assert {:ok, _} = parse_raw("impl Show for Int\n  fn show(x: Int) -> String = \"x\"\n")
      assert {:ok, _} = parse_raw("sup App.Root\n  children\n    actor Counter as counter\n")
      assert {:ok, _} = parse_raw("sup App.Root\n  children []\n")
    end
  end

  describe "non-associative operators reject chaining" do
    test "comparison: `a == b == c`" do
      assert {:error, errors} = parse_raw("a == b == c")
      assert Enum.any?(errors, &match?({:non_associative, %{operator: :==, next_operator: :==}}, &1))
    end

    test "comparison, mixed operators at the same level: `a < b <= c`" do
      assert {:error, errors} = parse_raw("a < b <= c")
      assert Enum.any?(errors, &match?({:non_associative, %{operator: :<, next_operator: :<=}}, &1))
    end

    test "range: `a..b..c`" do
      assert {:error, errors} = parse_raw("a..b..c")
      assert Enum.any?(errors, &match?({:non_associative, %{operator: :.., next_operator: :..}}, &1))
    end

    test "Melquiades send: `a <-| b <-| c`" do
      assert {:error, errors} = parse_raw("a <-| b <-| c")
      assert Enum.any?(errors, &match?({:non_associative, %{operator: :"<-|", next_operator: :"<-|"}}, &1))
    end

    test "the conflicting operators receive separate exact source labels" do
      source = "a == b == c"
      assert {:error, [{:non_associative, details} = reason]} = parse_raw(source)

      assert details.operator_span.start_column == 3
      assert details.operator_span.end_column == 5
      assert details.span.start_column == 8
      assert details.span.end_column == 10

      {diagnostic, registry} =
        Cure.Compiler.Errors.to_diagnostic({:parse_error, [reason]}, "operator.cure", source)

      rendered = Renderer.plain(diagnostic, registry, width: 80)
      assert diagnostic.code == "E094"
      assert diagnostic.key == :non_associative

      assert rendered ==
               String.trim_trailing("""
               -- OPERATOR CHAIN NEEDS PARENTHESES [E094] ----------------------- operator.cure

               The '==' operator cannot be chained without parentheses.

               at operator.cure:1:8
               1 | a == b == c
                 |   --   ^^ the conflicting operator is here; this second operator makes the chain ambiguous

               Hint: Add parentheses around the operation that should happen first
               """)

      lsp = Renderer.lsp(diagnostic, registry)

      assert lsp["range"] == %{
               "start" => %{"line" => 0, "character" => 7},
               "end" => %{"line" => 0, "character" => 9}
             }

      assert [%{"location" => %{"range" => first_range}, "message" => first_message}] =
               lsp["relatedInformation"]

      assert first_range == %{
               "start" => %{"line" => 0, "character" => 2},
               "end" => %{"line" => 0, "character" => 4}
             }

      assert first_message == "the conflicting operator is here"
    end
  end

  test "a bare brace explains the valid expression forms and keeps its exact source range" do
    source = "{\n"
    {:ok, tokens} = Lexer.tokenize(source, file: "unexpected.cure", emit_events: false)
    assert {:error, [{:unexpected_token, details} | _]} = Parser.parse(tokens, emit_events: false)
    assert details.observed == "{"

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [{:unexpected_token, details}]}, "unexpected.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- BRACE CANNOT START AN EXPRESSION [E094] --------------------- unexpected.cure

             A bare '{' does not begin a Cure expression. Write `Type{...}` for a record,
             `\#{...}` for a map, or use indentation for a block.

             at unexpected.cure:1:1
             1 | {
               | ^ choose record, map, or block syntax here
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 0, "character" => 0},
             "end" => %{"line" => 0, "character" => 1}
           }

    json = diagnostic |> Renderer.json() |> Jason.decode!()
    assert json["code"] == "E094"
    assert json["title"] == "Brace cannot start an expression"
    assert json["payload"]["kind"] == "bare_brace_expression"
    assert json["suggestions"] == []
  end

  test "an unmatched closing delimiter says that its opener is missing" do
    source = ")\n"
    {:ok, tokens} = Lexer.tokenize(source, file: "closer.cure", emit_events: false)
    assert {:error, [{:unexpected_token, details} | _]} = Parser.parse(tokens, emit_events: false)

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [{:unexpected_token, details}]}, "closer.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- CLOSING DELIMITER HAS NO OPENER [E094] -------------------------- closer.cure

             ')' closes a construct, but there is no matching opener here.

             at closer.cure:1:1
             1 | )
               | ^ this delimiter has nothing to close
             """)

    assert Renderer.lsp(diagnostic, registry)["data"]["key"] == "unmatched_closer"
    assert diagnostic.suggestions == []
  end

  test "a missing closing parenthesis at EOF names the construct and offers the unique insertion" do
    for {source, expected, title, replacement} <- [
          {"(1", :rparen, "Parenthesized expression is not closed", ")"}
        ] do
      {:ok, tokens} = Lexer.tokenize(source, file: "unclosed.cure", emit_events: false)

      assert {:error, errors} = Parser.parse(tokens, emit_events: false)

      assert {:expected_token, ^expected, :eof, nil, _line, _column, _span} =
               Enum.find(errors, &match?({:expected_token, ^expected, _, _, _, _, _}, &1))

      {diagnostic, registry} =
        Cure.Compiler.Errors.to_diagnostic({:parse_error, errors}, "unclosed.cure", source)

      rendered = Renderer.plain(diagnostic, registry, width: 80)
      assert rendered =~ "-- #{String.upcase(title)} [E094]"
      assert rendered =~ "the closing delimiter belongs here"
      assert rendered =~ "Hint: Insert `#{replacement}` to close the construct"

      assert [%{applicability: :machine_applicable, edits: [%{replacement: ^replacement}]}] =
               diagnostic.suggestions

      assert [%{"newText" => ^replacement}] =
               Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")
    end
  end

  test "the real parser path replaces a mismatched closing delimiter" do
    source = "fn run(] -> Int = 1\n"
    {:ok, tokens} = Lexer.tokenize(source, file: "mismatch.cure", emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    assert {:expected_token, :rparen, :rbracket, "]", _line, _column, _span} =
             mismatch = Enum.find(errors, &match?({:expected_token, :rparen, :rbracket, _, _, _, _}, &1))

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [mismatch]}, "mismatch.cure", source)

    assert diagnostic.key == :mismatched_closer
    assert Renderer.plain(diagnostic, registry, width: 80) =~ "Hint: Replace ']' with `)`"

    assert [%{"newText" => ")", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 7},
             "end" => %{"line" => 0, "character" => 8}
           }
  end

  test "a named function without a parameter list points before the return arrow" do
    source = "fn run -> Int = 1\n"
    {:ok, tokens} = Lexer.tokenize(source, file: "params.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:function_parameters_unparenthesized, details} = error
    assert details.function == "run"
    assert details.observed == "->"

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "params.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- FUNCTION PARAMETER LIST IS MISSING [E094] ----------------------- params.cure

             The function `run` needs a parenthesized parameter list after its name. Write
             `()` when it takes no parameters.

             at params.cure:1:8
             1 | fn run -> Int = 1
               |    --- ^^ this function name needs a parameter list after it; the parameter list belongs before this token

             Hint: Insert `()` after the function name
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "()", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 7
    assert insertion.end_byte == 7

    assert [%{"newText" => "()", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 7},
             "end" => %{"line" => 0, "character" => 7}
           }
  end

  test "an invalid function parameter is rejected at the authored binder token" do
    source = "fn run(42) -> Int = 1\n"
    {:ok, tokens} = Lexer.tokenize(source, file: "binder.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:invalid_parameter_name, details} = error
    assert details.observed == 42

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "binder.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- FUNCTION PARAMETER NEEDS A NAME [E094] -------------------------- binder.cure

             42 cannot name a function parameter. Use a lower-case name such as `value`,
             optionally followed by `: Type`.

             at binder.cure:1:8
             1 | fn run(42) -> Int = 1
               |        ^^ write a parameter name here

             Hint: Replace this with a descriptive lower-case parameter name
             """)

    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 0, "character" => 7},
             "end" => %{"line" => 0, "character" => 9}
           }
  end

  test "an invalid implicit parameter keeps both the brace and binder ranges" do
    source = "fn run({42}) -> Int = 1\n"
    {:ok, tokens} = Lexer.tokenize(source, file: "implicit.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:invalid_parameter_name, %{implicit: true} = details} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "implicit.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- FUNCTION PARAMETER NEEDS A NAME [E094] ------------------------ implicit.cure

             42 cannot name an implicit parameter. Write a lower-case binder such as `{type}`
             or `{type: Type}`.

             at implicit.cure:1:9
             1 | fn run({42}) -> Int = 1
               |        -^^ the construct starts here; write a parameter name here

             Hint: Replace this with a descriptive lower-case parameter name
             """)

    assert [related] = Renderer.lsp(diagnostic, registry)["relatedInformation"]
    assert related["message"] == "the construct starts here"

    assert related["location"]["range"] == %{
             "start" => %{"line" => 0, "character" => 7},
             "end" => %{"line" => 0, "character" => 8}
           }

    assert diagnostic.primary.span == details.span
  end

  test "a variadic marker without a binder points at the insertion boundary" do
    source = "fn run(*) -> Int = 1\n"
    {:ok, tokens} = Lexer.tokenize(source, file: "variadic.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:variadic_parameter_name_missing, %{kind: :variadic} = details} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "variadic.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- VARIADIC PARAMETER NEEDS A NAME [E094] ------------------------ variadic.cure

             The `*` marker must be followed by the name that receives extra positional
             arguments, for example `*values`.

             at variadic.cure:1:9
             1 | fn run(*) -> Int = 1
               |        -^ this variadic marker needs a binder; write the variadic parameter name here

             Hint: Add a descriptive lower-case name after the variadic marker
             """)

    assert [%{applicability: :manual, edits: []}] = diagnostic.suggestions

    assert diagnostic.primary.span.start_byte == 8
    assert diagnostic.primary.span.end_byte == 8
    assert details.marker_span.start_byte == 7
    assert details.marker_span.end_byte == 8

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 0, "character" => 8},
             "end" => %{"line" => 0, "character" => 8}
           }

    assert [%{"message" => "this variadic marker needs a binder"}] = lsp["relatedInformation"]
  end

  test "a keyword-variadic marker retains the complete two-star range" do
    source = "fn run(**) -> Int = 1\n"
    {:ok, tokens} = Lexer.tokenize(source, file: "keyword_variadic.cure", emit_events: false)
    assert {:error, [{:variadic_parameter_name_missing, details} | _]} = Parser.parse(tokens, emit_events: false)
    assert details.kind == :keyword_variadic
    assert details.marker_span.start_byte == 7
    assert details.marker_span.end_byte == 9

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic(
        {:parse_error, [{:variadic_parameter_name_missing, details}]},
        "keyword_variadic.cure",
        source
      )

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- VARIADIC PARAMETER NEEDS A NAME [E094] ---------------- keyword_variadic.cure

             The `**` marker must be followed by the name that receives extra named
             arguments, for example `**options`.

             at keyword_variadic.cure:1:10
             1 | fn run(**) -> Int = 1
               |        --^ this variadic marker needs a binder; write the variadic parameter name here

             Hint: Add a descriptive lower-case name after the variadic marker
             """)
  end

  test "a named keyword-variadic parameter reaches the intended AST form" do
    assert {:function_def, meta, _body} = parse!("fn run(**options) = 1")
    assert [{:param, parameter_meta, "options"}] = meta[:params]
    assert parameter_meta[:kind] == :keyword_variadic
  end

  test "an unclosed function call pairs EOF with its opener and offers a closing edit" do
    source = "fetch(1"
    {:ok, tokens} = Lexer.tokenize(source, file: "unclosed_call.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:call_arguments_syntax, %{kind: :call_unclosed}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "unclosed_call.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- FUNCTION CALL IS NOT CLOSED [E094] ----------------------- unclosed_call.cure

             The call to `fetch` reaches the end of the source without the ')' that closes
             its argument list.

             at unclosed_call.cure:1:8
             1 | fetch(1
               |      --^ this call's argument list starts here; the previous argument ends here; close this call with `)`

             Hint: Insert `)` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ")"}]}] =
             diagnostic.suggestions

    assert length(Renderer.lsp(diagnostic, registry)["relatedInformation"]) == 2
  end

  test "adjacent call arguments point between expressions and insert a comma" do
    source = "fetch(1 2)"
    {:ok, tokens} = Lexer.tokenize(source, file: "call_separator.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:call_arguments_syntax, %{kind: :call_argument_separator_missing}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "call_separator.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- CALL ARGUMENTS NEED A COMMA [E094] ---------------------- call_separator.cure

             The call to `fetch` has another argument here, but consecutive arguments must be
             separated by a comma.

             at call_separator.cure:1:9
             1 | fetch(1 2)
               |      -- ^ this call's argument list starts here; the previous argument ends here; insert a comma before this argument

             Hint: Insert `,` between these arguments
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ", ", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 8
    assert insertion.end_byte == 8

    assert [%{"newText" => ", ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 8},
             "end" => %{"line" => 0, "character" => 8}
           }
  end

  test "an unclosed list pairs EOF with its opener and offers a closing bracket" do
    source = "[1"
    {:ok, tokens} = Lexer.tokenize(source, file: "list.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :list}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "list.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- LIST IS NOT CLOSED [E094] ----------------------------------------- list.cure

             This list reaches the end of the source without the ']' that closes its
             elements.

             at list.cure:1:3
             1 | [1
               | --^ this container starts here; the previous element ends here; close this container with `]`

             Hint: Insert `]` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "]"}]}] = diagnostic.suggestions
    assert length(Renderer.lsp(diagnostic, registry)["relatedInformation"]) == 2
  end

  test "adjacent tuple elements get a zero-width comma insertion" do
    source = "%[1 2]"
    {:ok, tokens} = Lexer.tokenize(source, file: "tuple.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:container_elements_syntax, %{kind: :container_separator_missing, container: :tuple}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "tuple.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- TUPLE ELEMENTS NEED A COMMA [E094] ------------------------------- tuple.cure

             This tuple has another element here, but consecutive elements must be separated
             by a comma.

             at tuple.cure:1:5
             1 | %[1 2]
               | --- ^ this container starts here; the previous element ends here; insert a comma before this element

             Hint: Insert `,` between these elements
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ", ", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 4
    assert insertion.end_byte == 4
  end

  test "list separators and tuple closers use the same contextual container family" do
    for {source, expected_kind, expected_container} <- [
          {"[1 2]", :container_separator_missing, :list},
          {"%[1", :container_unclosed, :tuple}
        ] do
      {:ok, tokens} = Lexer.tokenize(source, file: "container.cure", emit_events: false)
      assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)

      assert {:container_elements_syntax, %{kind: ^expected_kind, container: ^expected_container}} = error
    end
  end

  test "an unclosed map pairs EOF with its opener and offers a closing brace" do
    source = "%{a: 1"
    {:ok, tokens} = Lexer.tokenize(source, file: "map.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :map}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "map.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- MAP IS NOT CLOSED [E094] ------------------------------------------- map.cure

             This map reaches the end of the source without the '}' that closes its entries.

             at map.cure:1:7
             1 | %{a: 1
               | ------^ this container starts here; the previous entry ends here; close this container with `}`

             Hint: Insert `}` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "}"}]}] =
             diagnostic.suggestions

    assert length(Renderer.lsp(diagnostic, registry)["relatedInformation"]) == 2
  end

  test "adjacent map entries get a zero-width comma insertion" do
    source = "%{a: 1 b: 2}"
    {:ok, tokens} = Lexer.tokenize(source, file: "map_separator.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:container_elements_syntax, %{kind: :container_separator_missing, container: :map}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "map_separator.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- MAP ENTRIES NEED A COMMA [E094] -------------------------- map_separator.cure

             This map has another entry here, but consecutive entries must be separated by a
             comma.

             at map_separator.cure:1:8
             1 | %{a: 1 b: 2}
               | ------ ^ this container starts here; the previous entry ends here; insert a comma before this entry

             Hint: Insert `,` between these entries
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ", ", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 7
    assert insertion.end_byte == 7

    assert [%{"newText" => ", ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 7},
             "end" => %{"line" => 0, "character" => 7}
           }
  end

  test "an unclosed record points from its opening brace to its last field" do
    source = "Point{x: 1"
    {:ok, tokens} = Lexer.tokenize(source, file: "record.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :record}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "record.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- RECORD IS NOT CLOSED [E094] ------------------------------------- record.cure

             This record reaches the end of the source without the '}' that closes its
             fields.

             at record.cure:1:11
             1 | Point{x: 1
               |      -----^ this container starts here; the previous field ends here; close this container with `}`

             Hint: Insert `}` to close the construct
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "}"}]}] =
             diagnostic.suggestions

    assert length(Renderer.lsp(diagnostic, registry)["relatedInformation"]) == 2
  end

  test "adjacent record fields get a zero-width comma insertion" do
    source = "Point{x: 1 y: 2}"
    {:ok, tokens} = Lexer.tokenize(source, file: "record_separator.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:container_elements_syntax, %{kind: :container_separator_missing, container: :record}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "record_separator.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- RECORD FIELDS NEED A COMMA [E094] --------------------- record_separator.cure

             This record has another field here, but consecutive fields must be separated by
             a comma.

             at record_separator.cure:1:12
             1 | Point{x: 1 y: 2}
               |      ----- ^ this container starts here; the previous field ends here; insert a comma before this field

             Hint: Insert `,` between these fields
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: ", ", span: insertion}]}] =
             diagnostic.suggestions

    assert insertion.start_byte == 11
    assert insertion.end_byte == 11

    assert [%{"newText" => ", ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 11},
             "end" => %{"line" => 0, "character" => 11}
           }
  end

  test "record updates use the same contextual closing-brace family" do
    source = "Point{point | x: 1"
    {:ok, tokens} = Lexer.tokenize(source, file: "record_update.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)
    assert {:container_elements_syntax, %{kind: :container_unclosed, container: :record}} = error
  end

  test "a trailing list comma is blamed directly and can be removed safely" do
    source = "[1,]"
    {:ok, tokens} = Lexer.tokenize(source, file: "trailing_list.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)

    assert {:container_elements_syntax, %{kind: :container_trailing_separator, container: :list}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "trailing_list.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- LIST ENDS WITH AN EXTRA COMMA [E094] --------------------- trailing_list.cure

             This list ends immediately after a comma, but every comma must be followed by
             another element.

             at trailing_list.cure:1:3
             1 | [1,]
               | --^ this container starts here; the previous element ends here; this comma has no following element

             Hint: Remove the trailing comma
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "", span: comma_span}]}] =
             diagnostic.suggestions

    assert binary_part(source, comma_span.start_byte, comma_span.end_byte - comma_span.start_byte) == ","

    assert [%{"newText" => "", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 0, "character" => 2},
             "end" => %{"line" => 0, "character" => 3}
           }
  end

  test "a trailing tuple comma uses the tuple-specific title and complete marker range" do
    source = "%[1,]"
    {:ok, tokens} = Lexer.tokenize(source, file: "trailing_tuple.cure", emit_events: false)
    assert {:error, [error | _]} = Parser.parse(tokens, emit_events: false)

    assert {:container_elements_syntax, %{kind: :container_trailing_separator, container: :tuple}} = error

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "trailing_tuple.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) =~ "-- TUPLE ENDS WITH AN EXTRA COMMA [E094]"
    assert length(Renderer.lsp(diagnostic, registry)["relatedInformation"]) == 2
  end

  describe "associative operators still chain" do
    test "`a + b + c` left-associates" do
      assert {:binary_op, _, [{:binary_op, _, [_a, _b]}, _c]} = parse!("a + b + c")
    end

    test "`a + b == c + d` groups the comparison outermost" do
      assert {:binary_op, meta, [{:binary_op, _, _}, {:binary_op, _, _}]} = parse!("a + b == c + d")
      assert Keyword.get(meta, :operator) == :==
    end

    test "a single comparison of two arithmetic chains is not a chain" do
      assert {:ok, _} = parse_raw("a * b < c * d")
    end

    test "comparisons joined by `and` are not a chain" do
      assert {:ok, _} = parse_raw("a < b and b < c")
    end
  end
end
