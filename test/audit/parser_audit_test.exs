defmodule Cure.Audit.ParserTest do
  @moduledoc """
  Red tests from a targeted audit of `lib/cure/compiler/parser.ex` (the
  Pratt parser: token list -> MetaAST). Each test encodes one specific,
  currently-wrong behavior and asserts the CORRECT one per
  `docs/LANGUAGE_SPEC.md` / `lib/cure/compiler/parser/precedence.ex`'s own
  documented contract. See each test's comment for the finding and citation.
  """
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Compiler.{Lexer, Parser}

  # Parse without unwrapping, for tests that expect `{:error, _}`.
  defp parse_raw(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    Parser.parse(tokens, emit_events: false)
  end

  # ══════════════════════════════════════════════════════════════════════
  # PA1-PA3: `expect(state, :keyword)` checks only the TOKEN TYPE, never the
  # keyword's VALUE, at three call sites that are documented (in comments
  # right above the call) as consuming one SPECIFIC keyword ("for" / "as").
  # `defp expect(state, expected_type)` (parser.ex ~5367) does:
  #
  #     if token.type == expected_type do advance(state) else ...error... end
  #
  # It never compares `token.value`. Contrast with `expect_keyword/2`
  # (parser.ex ~5378), which the parser DOES use elsewhere (e.g.
  # `parse_rewrite/2` -> `expect_keyword(state, :in)`) specifically because it
  # checks both type AND value. Because these three sites use the weaker
  # `expect(state, :keyword)` instead of `expect_keyword(state, :for | :as)`,
  # ANY keyword token in that grammar slot is silently swallowed and the
  # parser proceeds as if the correct keyword had been written -- no error is
  # recorded, and since the actual keyword token's value is never stored in
  # the resulting AST, no downstream stage can detect the substitution either.
  # This is "a syntactic form accepted that the spec forbids" (task class 2):
  # `impl Proto for Type` is the only grammar LANGUAGE_SPEC.md documents
  # (proto/impl section) and SUPERVISION.md documents for children
  # (`Module as child_id`); nothing else is a valid separator.
  # ══════════════════════════════════════════════════════════════════════

  # parser.ex:3525, inside parse_impl/1 (`impl Proto for Type`).
  test "PA1: `impl Proto for Type` silently accepts any keyword in place of `for`" do
    src = """
    impl Show when Int
      fn show(x: Int) -> String = "x"
    """

    assert {:error, _errors} = parse_raw(src)
  end

  # parser.ex:3630, inside parse_implementation/1
  # (`implementation Iface for Type [as Name]`).
  test "PA2: `implementation Iface for Type` silently accepts any keyword in place of `for`" do
    src = """
    implementation Show when Int
      fn show(x: Int) -> String = "x"
    """

    assert {:error, _errors} = parse_raw(src)
  end

  # parser.ex:4305, inside parse_sup_child_spec/1
  # (docs/LANGUAGE_SPEC.md "Each line is `Module as child_id`").
  test "PA3: a supervisor child spec silently accepts any keyword in place of `as`" do
    src = """
    sup App.Root
      children
        Counter when counter
    """

    assert {:error, _errors} = parse_raw(src)
  end

  # ══════════════════════════════════════════════════════════════════════
  # PA4-PA6: operators the spec marks non-associative are silently
  # left-chained instead of being rejected.
  #
  # docs/LANGUAGE_SPEC.md's operator table (lines 66-67, 71-72) marks
  # comparison, range, and the Melquiades send operator "non-assoc".
  # `lib/cure/compiler/parser/precedence.ex`'s own moduledoc is explicit
  # about what that means operationally:
  #
  #   "For non-associative operators, right BP = left BP + 1 (and the
  #    parser rejects chaining)."
  #
  # No rejection exists anywhere in parser.ex. The Pratt loop's generic
  # binary-operator clause (`handle_infix_op/5`'s final `_ ->` clause, and
  # the dedicated `:range`/`:range_inclusive` and `:melquiades` clauses)
  # all end by calling `parse_infix(state, ast, min_bp)` -- reusing the
  # CALLER's original `min_bp`, not `right_bp`. `right_bp = left_bp + 1`
  # only stops the operator from swallowing a second same-precedence
  # operator on its OWN right-hand side (`parse_expr(state, right_bp)`);
  # it does nothing to stop the OUTER loop from immediately picking the
  # freshly-built node back up as a new left operand once control returns
  # to `parse_infix/3` at the original (lower) `min_bp`. Mechanically this
  # is byte-for-byte the same trick genuinely left-associative operators
  # (`+`, `*`, ...) use (`right_bp = left_bp + 1` there too) -- the
  # "non-assoc" table entries are, in the actual implementation, just
  # left-associative operators wearing a different comment.
  #
  # `test/cure/compiler/melquiades_parser_test.exs` ("the operator is
  # non-associative: `a <-| b <-| c` does not nest", lines 61-68) already
  # brushes up against this: its own comment admits "errors are swallowed
  # by `parse/1` because non-assoc rejection only changes shape" and then
  # dodges the claim in its test name by parsing `"a <-| b"` (a single
  # send, never a chain) instead of the triple-chain the test name
  # promises. PA6 below parses the actual triple chain.
  # ══════════════════════════════════════════════════════════════════════

  # docs/LANGUAGE_SPEC.md line 71: "`==`, `!=`, `<`, `>`, `<=`, `>=` --
  # comparison (non-assoc)". `a == b == c` has no valid left-to-right
  # reading under non-associativity (Python/Rust either reject or special-
  # case this; Cure's own precedence.ex claims outright rejection) yet
  # today it silently parses as `(a == b) == c`.
  test "PA4: comparison operators are non-associative but the parser silently left-chains `a == b == c`" do
    assert {:error, _errors} = parse_raw("a == b == c")
  end

  # docs/LANGUAGE_SPEC.md line 72: "`..`, `..=` -- range (non-assoc)".
  test "PA5: range operators are non-associative but the parser silently left-chains `a..b..c`" do
    assert {:error, _errors} = parse_raw("a..b..c")
  end

  # docs/LANGUAGE_SPEC.md lines 66-67: "`<-|` / `✉` -- Melquiades send
  # (non-assoc, v0.25.0)". The triple chain `a <-| b <-| c` that
  # melquiades_parser_test.exs's test name promises to check (but doesn't)
  # actually parses today as nested sends `{:send, _, [{:send, _, [a, b]}, c]}`
  # -- i.e. it silently re-sends the FIRST send's return value to `c` as a
  # second message, which is exactly the "fanning out to two sends" the
  # module doc for precedence.ex says non-associativity exists to prevent.
  test "PA6: the Melquiades operator is non-associative but `a <-| b <-| c` silently nests into two sends" do
    assert {:error, _errors} = parse_raw("a <-| b <-| c")
  end
end
