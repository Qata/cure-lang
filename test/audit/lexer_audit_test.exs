defmodule Cure.Audit.LexerTest do
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Compiler.Lexer
  alias Cure.Compiler.Token

  defp lex!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    tokens
  end

  # ---------------------------------------------------------------------------
  # LX1: `paren_depth` is silently reset/discarded on every single-token step
  # inside string interpolation, so newline suppression inside parens does not
  # work for expressions written inside `#{...}`.
  #
  # `lib/cure/compiler/lexer.ex`, `lex_interpolation_expr/2` (~lines 840-874),
  # `_ ->` clause:
  #
  #   inner_state = %{state | tokens: [], paren_depth: 0}
  #   case lex_next(inner_state) do
  #     {:ok, inner_state} ->
  #       produced = Enum.reverse(inner_state.tokens)
  #       next_state = %{inner_state | tokens: state.tokens, paren_depth: state.paren_depth}
  #       ...
  #
  # Every single-token step (a) forces `paren_depth: 0` before lexing, and (b)
  # after lexing ONE token, throws away whatever `inner_state.paren_depth`
  # became (e.g. bumped to 1 by an `(` via `emit_single(..., inc_paren: true)`)
  # and replaces it with the outer `state.paren_depth` snapshot from before
  # this step. So a `(` opened *inside* an interpolation never actually
  # increments the depth counter that `handle_newline/1` checks
  # (`if state.paren_depth > 0`) — every token step sees `paren_depth == 0`,
  # regardless of how many parens are open.
  #
  # Per the lexer's own documented/tested invariant (see
  # `test/cure/compiler/lexer_test.exs` "newlines inside parentheses are
  # suppressed"), a newline inside an open `(...)` must not produce a
  # `:newline` token. That invariant silently breaks the moment the parens
  # are written inside a string interpolation (`"#{...}"`), because the
  # depth tracking there is reset-and-discarded per token instead of
  # threaded through the whole expression. A perfectly ordinary multi-line
  # call inside an interpolated string spuriously emits a `:newline` token
  # in the expression's token stream, which the sub-expression grammar does
  # not expect.
  test "LX1: a newline inside parens is suppressed inside string interpolation, same as at top level" do
    # Cure source: "#{f(a,\nb)}" with a real newline byte between `a,` and `b)`.
    src = "\"" <> "#" <> "{" <> "f(a," <> "\n" <> "b)" <> "}" <> "\""

    tokens = lex!(src)

    assert [%Token{type: :string_interpolation, value: parts}, _eof] = tokens
    assert [{:expr, expr_tokens}] = parts

    refute Enum.any?(expr_tokens, &(&1.type == :newline)),
           "expected no :newline token inside the parenthesised call, got types: #{inspect(Enum.map(expr_tokens, & &1.type))}"

    assert Enum.map(expr_tokens, & &1.type) == [
             :identifier,
             :lparen,
             :identifier,
             :comma,
             :identifier,
             :rparen
           ]
  end

  # ---------------------------------------------------------------------------
  # LX2: a `%{...}` map literal inside a string interpolation truncates the
  # interpolation early and corrupts the rest of the string.
  #
  # `lex_interpolation_expr/2` tracks how many `#{...}` are still open with a
  # `depth` counter, but it only increments `depth` when it sees a *bare* `{`
  # byte directly via its own `peek(state)` dispatch (the `?{ -> ... depth + 1`
  # clause). A `%{` map-literal opener, however, is consumed as a single
  # atomic 2-byte token by `lex_percent/1` (dispatched through the generic
  # `_ -> ... lex_next(inner_state) ...` fallback), so its `{` is never seen
  # raw by `lex_interpolation_expr` and `depth` is never bumped for it.
  #
  # The map literal's closing `}` *is* seen raw by `lex_interpolation_expr`,
  # though (`lex_percent` only consumes the two-byte opener, not the whole
  # literal). Because `depth` was never incremented for the `%{`, that closing
  # `}` hits `?} when depth == 0 -> {[], advance(state, 1)}` and the
  # interpolation is closed right there — one `}` too early. Everything after
  # it (including the real closing `}` of `#{...}`) falls back into ordinary
  # string-body scanning and is swallowed as literal string content instead
  # of ending the string/token stream correctly.
  #
  # Record literals (`TypeName{field: expr}`, docs/LANGUAGE_SPEC.md "Records
  # > Construction") use a *bare* `{`, which the depth tracker does see, so
  # this is specific to the `%{...}` map-literal sigil
  # (docs/LANGUAGE_SPEC.md "Literals": `Maps: %{key: value}`).
  test "LX2: a %{...} map literal inside string interpolation is not truncated early" do
    # `~s` interpolates by default, so `#{` must be escaped to reach the
    # lexer as literal Cure source `"#{ %{a: 1} }"`.
    tokens = lex!(~s("\#{ %{a: 1} }"))

    assert [%Token{type: :string_interpolation, value: parts}, _eof] = tokens

    assert [{:expr, expr_tokens}] = parts,
           "expected the whole map literal to stay inside one interpolation expr, got parts: #{inspect(parts)}"

    assert Enum.map(expr_tokens, & &1.type) == [
             :map_open,
             :identifier,
             :colon,
             :integer,
             :rbrace
           ]
  end

  # ---------------------------------------------------------------------------
  # LX3: a raw newline byte embedded inside a double-quoted string literal
  # does not advance `state.line` (or reset `state.col`), so every token
  # after a multi-line string literal reports the wrong line (and column)
  # for the rest of that logical source region.
  #
  # `lex_string_body/3` (lib/cure/compiler/lexer.ex, the final catch-all
  # clause):
  #
  #   c ->
  #     state = advance(state, 1)
  #     lex_string_body(state, start_col, [<<c>> | acc])
  #
  # `advance/2` only touches `pos` and `col` (`col: state.col + n`); it never
  # touches `line`. Every other multi-line lexer construct in this same file
  # gets this right: `handle_newline/1` (top-level newlines),
  # `collect_fenced_lines/2` (fenced `###` doc comments, which explicitly do
  # `|> Map.put(:line, state.line + 1) |> Map.put(:col, 1)` at each line
  # break), and `lex_indentation/1`'s blank-line branch all bump `line` and
  # reset `col` when they cross a `\n`. `lex_string_body/3` is the one
  # construct that swallows a `\n` byte (a string literal is allowed to span
  # physical lines -- there is no lexer error for it) without doing so.
  #
  # Consequence: every token lexed after a string literal that contains an
  # embedded newline is off by however many embedded newlines occurred
  # inside that string -- which breaks every subsequent error message's line
  # number, exactly the class of bug flagged by "line/column positions
  # drifting ... after a newline inside a string".
  test "LX3: a newline embedded in a string literal still advances the lexer's line counter" do
    # Line 1: `"a` + a literal newline + `b"` (the string spans lines 1-2).
    # Line 2 also holds the closing quote right after `b`.
    # Line 3: `next`, preceded by a real newline that is *outside* the string.
    src = "\"a" <> "\n" <> "b\"" <> "\n" <> "next"

    tokens = lex!(src)

    string_tok = Enum.find(tokens, &(&1.type == :string))
    assert string_tok.value == "a\nb"

    next_tok = Enum.find(tokens, &(&1.value == "next"))
    assert next_tok.line == 3,
           "expected `next` on line 3 (after the 2-line string literal + its own newline), got line #{next_tok.line}"
  end

  # ---------------------------------------------------------------------------
  # Cleared while auditing (documented here, not as red tests, since these
  # are either already covered by existing tests or are intentional,
  # documented design):
  #
  #   - `--event-->` FSM transitions, `|>` vs `|`, `->` vs `-`, `..` vs `.`,
  #     `<<`/`<>`/`<=` vs `<`, `==`/`=>` vs `=`: all correct maximal munch,
  #     already exercised by test/cure/compiler/lexer_test.exs.
  #   - Keyword-vs-identifier: `lex_identifier/1` always consumes the *whole*
  #     word via `consume_while/2` before checking `@keyword_strings`
  #     membership, so `iffy`/`caseless`/`dataset`/`function`/`modular`
  #     never collide with `if`/`case`/`do`/`fn`/`mod` -- correct by
  #     construction, already covered by the "identifiers that start like
  #     keywords" test.
  #   - `for <<b <- buf>>` binary-comprehension generators: the lexer
  #     deliberately emits `<-` as separate `:lt` + `:minus` tokens (no
  #     dedicated arrow token); `lib/cure/compiler/parser.ex` documents and
  #     relies on this at `parse_generator_or_filter/1` /
  #     `parse_binary_generator/1` -- intentional, not a lexer bug.
  #   - Non-ASCII byte-preservation in strings/comments (the historical
  #     double-encoding bug) is fixed and covered by
  #     test/cure/compiler/lexer_test.exs.
  #   - Char-literal UTF-8 decoding (multi-byte / astral codepoints,
  #     truncated-tail-at-EOF) is covered by test/cure/compiler/char_lexer_test.exs.
end
