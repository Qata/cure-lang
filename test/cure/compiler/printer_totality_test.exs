defmodule Cure.Compiler.PrinterTotalityTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Printer
  alias Cure.Compiler.Printer.UnprintableNodeError

  test "an unhandled node kind raises loudly, never silently inspects" do
    # A synthetic node kind the Printer has no clause for.
    bogus = {:definitely_not_a_real_node_kind, [line: 1, col: 1], []}

    assert_raise UnprintableNodeError, fn ->
      Printer.quoted_to_string(bogus)
    end
  end

  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(src, file) do
    {:ok, toks} = Lexer.tokenize(src, file: file, emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    ast
  end

  # Every non-error node kind the parser can construct in a *well-formed*
  # program. Error/diagnostic node kinds (produced only on parse failure)
  # are excluded — they never appear in a successfully parsed AST.
  @error_node_kinds ~w(
    error expected unexpected_token parser ok pickup_no_else pickup_else_not_last
    pickup_multiple_else lambda_block_unterminated with_multi_arity_mismatch
    named_implicit_not_in_pattern if_deprecated
  )a

  defp node_kinds(ast, acc \\ MapSet.new())
  defp node_kinds({k, _m, ch}, acc) when is_atom(k) and is_list(ch),
    do: Enum.reduce(ch, MapSet.put(acc, k), &node_kinds/2)
  defp node_kinds({k, _m, _v}, acc) when is_atom(k), do: MapSet.put(acc, k)
  defp node_kinds(l, acc) when is_list(l), do: Enum.reduce(l, acc, &node_kinds/2)
  defp node_kinds(_, acc), do: acc

  test "printer is total over the construct-complete fixture (no raise, reparses, fixpoint)" do
    file = "test/fixtures/printer_totality.cure"
    src = File.read!(file)
    ast = parse!(src, file)

    # (a) prints without raising UnprintableNodeError
    out1 = Cure.Compiler.Printer.quoted_to_string(ast)

    # (b) reparses
    ast2 = parse!(out1, file)

    # (c) print is a byte-fixpoint
    out2 = Cure.Compiler.Printer.quoted_to_string(ast2)
    assert out1 == out2
  end

  test "the whole in-repo corpus prints without raising, reparses, and is a print-fixpoint" do
    # Spec §5.3/§7's Printer-totality gate is explicit that this applies to
    # "the whole in-repo .cure corpus", not only the synthetic fixture above:
    # "corpus parse->print never inspects a tuple and always reparses; print
    # is a fixpoint." The fixture test above proves construct-completeness
    # (it is *designed* to contain one of everything); this test proves the
    # same three properties additionally hold for every real file that
    # already exists in this repo, which is a separate, non-redundant claim
    # -- a corpus file could in principle exercise a node-kind combination,
    # ordering, or depth the hand-built fixture doesn't.
    files = Path.wildcard("lib/**/*.cure") ++ Path.wildcard("examples/**/*.cure")

    for file <- files do
      src = File.read!(file)

      with {:ok, toks} <- Lexer.tokenize(src, file: file, emit_events: false),
           {:ok, ast} <- Parser.parse(toks, file: file, emit_events: false) do
        # A successfully-parsed AST must never contain an error/diagnostic node
        # kind (those are only ever produced on parse failure, per the comment
        # on @error_node_kinds above) -- a genuine invariant this gate is
        # well-positioned to check, since it already walks every corpus file's
        # AST. This is also what actually exercises `@error_node_kinds` and
        # `node_kinds/2` in real test code (both were otherwise unused module
        # attribute/private-function definitions, which fails this project's
        # `mix test --warnings-as-errors` alias -- see mix.exs's `test` alias).
        kinds = node_kinds(ast)

        assert MapSet.disjoint?(kinds, MapSet.new(@error_node_kinds)),
               "#{file}: a successfully parsed AST contained an error node kind: " <>
                 "#{inspect(MapSet.to_list(MapSet.intersection(kinds, MapSet.new(@error_node_kinds))))}"

        # (a) must not raise UnprintableNodeError for any node the corpus exercises.
        out1 = Cure.Compiler.Printer.quoted_to_string(ast)

        # (b) reparses
        {:ok, toks2} = Lexer.tokenize(out1, file: file, emit_events: false)

        assert {:ok, ast2} = Parser.parse(toks2, file: file, emit_events: false),
               "#{file}: migrated/reprinted output failed to reparse"

        # (c) print is a byte-fixpoint
        out2 = Cure.Compiler.Printer.quoted_to_string(ast2)
        assert out1 == out2, "#{file}: print(reparse(print(ast))) != print(ast) -- not a fixpoint"
      end
    end
  end

  # The kinds Cure.Compiler.Printer currently has a `to_string/3` clause
  # for — derived by scanning the module's own source text, not by
  # calling it (calling it would require already knowing each kind's
  # correct arity/shape, which is circular for an exhaustiveness check).
  defp printer_handled_kinds do
    "lib/cure/compiler/printer.ex"
    |> File.read!()
    |> then(&Regex.scan(~r/defp to_string\(\{:([a-z_]+),/, &1))
    |> Enum.map(fn [_, k] -> String.to_atom(k) end)
    |> MapSet.new()
  end

  # Every node-kind atom `parser.ex` constructs as a genuine
  # `{tag, meta, children}` dispatch target (verified by hand against
  # each construction site during the 2026-07-10 plan hardening pass —
  # see the corrected Task-3 list; deliberately NOT auto-derived from a
  # blind regex over parser.ex, which cannot distinguish a real node tag
  # from an internal 2-tuple or a `meta[:kind]` value without reading
  # the surrounding code). Whoever adds a new node kind to the grammar
  # must add it here in the same commit, or this gate cannot do its job.
  @all_node_kinds ~w(
    assignment async_operation attribute_access augmented_assignment
    bin_segment binary_op block comment comprehension conditional
    container decorator early_return exception_handling filter
    function_call function_def generator import lambda list literal map
    match_arm pair pattern_match pickup pickup_clause pickup_else
    property range record_update send string_interpolation throw tuple
    type_annotation unary_op variable yield
    pin as_pattern assert_type gadt_ctor indexed_type interface
    implementation pi_type sigma_type with_abs hole forced_pattern
    child_spec binary_generator named_implicit_pat
  )a

  test "every node kind the parser can construct has a matching Printer clause (static, corpus-independent)" do
    missing = MapSet.difference(MapSet.new(@all_node_kinds), printer_handled_kinds())
    assert MapSet.to_list(missing) == [],
           "Printer is missing a to_string/3 clause for: #{inspect(MapSet.to_list(missing))}"
  end
end
