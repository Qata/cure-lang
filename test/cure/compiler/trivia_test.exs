defmodule Cure.Compiler.TriviaTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Lexer

  test "lexer collects every comment and blank run as positioned trivia" do
    src = """
    mod M

    # leading comment
    fn f() -> Int = 1  # trailing comment
    """

    {:ok, _tokens, trivia} = Lexer.tokenize(src, file: "t.cure", trivia: true)

    texts = for {:comment, t, _l, _c} <- trivia, do: String.trim(t)
    assert "leading comment" in texts
    assert "trailing comment" in texts
    assert Enum.any?(trivia, &match?({:blank, _, _}, &1))
  end

  test "a blank line that contains only indentation whitespace still counts as blank" do
    # Pins the fix for reusing lex_indentation/1's own blank-line branch
    # (lexer.ex:210-231, which strips leading whitespace via measure_indent/1
    # BEFORE checking for end-of-line) rather than a fresh "newline-only line"
    # definition that would miss this case. The blank line between `x` and `y`
    # below has two leading spaces (mirroring the block's own indent), which a
    # naive "line is exactly empty" check would fail to classify as blank.
    src = "mod M\nfn f() -> Int =\n  let x = 1\n  \n  x\n"

    {:ok, _tokens, trivia} = Lexer.tokenize(src, file: "t2.cure", trivia: true)

    assert Enum.any?(trivia, &match?({:blank, _, _}, &1)),
           "a whitespace-only blank line was not collected as trivia: #{inspect(trivia)}"
  end

  # ── Attachment pass (Task 5) ─────────────────────────────────────────────

  alias Cure.Compiler.{Parser, Trivia}
  alias Cure.Compiler.Trivia.UnplacedTriviaError

  defp attach(src, file) do
    {:ok, toks, trivia} = Lexer.tokenize(src, file: file, trivia: true)
    {:ok, ast} = Parser.parse(toks, file: file, emit_events: false)
    Trivia.attach(ast, trivia)
  end

  test "leading comment attaches to the following definition" do
    ast = attach("mod M\n\n# doc\nfn f() -> Int = 1\n", "a.cure")
    leadings =
      ast |> collect_meta(:leading) |> List.flatten() |> Enum.map(&elem(&1, 1)) |> Enum.map(&String.trim/1)
    assert "doc" in leadings
  end

  test "comment after last statement of a nested block lands in that block's trailer" do
    src = """
    mod M
    fn f() -> Int =
      let x = 1
      x
      # nested trailer
    """
    ast = attach(src, "b.cure")
    trailers =
      ast |> collect_meta(:trailer) |> List.flatten() |> Enum.map(&elem(&1, 1)) |> Enum.map(&String.trim/1)
    assert "nested trailer" in trailers
  end

  test "trailing comment on a map-literal pair attaches correctly (pair nodes carry no line/col of their own)" do
    # Exercises the recursive-children span fallback: `:pair` (parser.ex:932,
    # 944, 954) has empty meta, so its effective end must be derived from its
    # value child's position, not read off the pair node itself.
    src = "mod M\nfn f() -> Int =\n  let m = %{x: 1, y: 2}  # tail comment\n  1\n"
    ast = attach(src, "pair.cure")
    trailings =
      ast |> collect_meta(:trailing) |> List.flatten() |> Enum.map(&elem(&1, 1)) |> Enum.map(&String.trim/1)
    assert "tail comment" in trailings
  end

  test "a comment near a lambda with a positionless param leaf does not crash attach/2" do
    # Exercises the transparent-leaf fallback: a lambda `:param` node
    # (parser.ex:2648, `{:param, [], name}`) has no meta AND no children list
    # (its 3rd element is a bare string), so it contributes no position of its
    # own and must not be recursed into.
    src = "mod M\nfn f() -> Int =\n  let g = fn (x) -> x\n  # after the let\n  g(1)\n"
    ast = attach(src, "lambda.cure")
    texts =
      ((ast |> collect_meta(:trailer) |> List.flatten()) ++ (ast |> collect_meta(:leading) |> List.flatten()))
      |> Enum.map(&elem(&1, 1))
      |> Enum.map(&String.trim/1)
    assert "after the let" in texts
  end

  test "attachment is total: an item that cannot be placed raises, never drops" do
    # `Trivia.attach([], ...)` is a direct unit test of attach/2's recursive
    # contract: zero nodes exist for the item to become a `:leading` on, and
    # there is no container node's `meta` to hold it as a `:trailer` either --
    # genuinely nothing to attach to, hence the raise. (A real Parser.parse/2
    # never returns a bare list at top level, so this is defense-in-depth.)
    assert_raise UnplacedTriviaError, fn ->
      Trivia.attach([], [{:comment, "orphan", 1, 1}])
    end
  end

  # helper: collect all values of a given meta key across the AST
  defp collect_meta(ast, key, acc \\ [])
  defp collect_meta({_k, m, ch}, key, acc) when is_list(m) and is_list(ch) do
    acc = if v = Keyword.get(m, key), do: [v | acc], else: acc
    Enum.reduce(ch, acc, &collect_meta(&1, key, &2))
  end
  defp collect_meta({_k, m, _v}, key, acc) when is_list(m) do
    if v = Keyword.get(m, key), do: [v | acc], else: acc
  end
  defp collect_meta(l, key, acc) when is_list(l), do: Enum.reduce(l, acc, &collect_meta(&1, key, &2))
  defp collect_meta(_, _key, acc), do: acc
end
