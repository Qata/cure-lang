defmodule Cure.Compiler.PrinterFidelityTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Printer}

  # The printer backs `cure fmt` / `cure migrate` / `cure rewrite`, so any node it
  # reprints in a form that reparses differently (or raises) silently corrupts
  # user code. These pin round-trip fidelity for node shapes the precedence
  # tests don't reach: the word-spelled prefix operator `bnot`, implicit type
  # parameters `{T: Type}`, and `with`-abstraction rematch arms.

  defp strip(node) do
    case node do
      {tag, _meta, kids} when is_list(kids) -> {tag, Enum.map(kids, &strip/1)}
      {tag, _meta, kid} -> {tag, strip(kid)}
      list when is_list(list) -> Enum.map(list, &strip/1)
      other -> other
    end
  end

  defp parse!(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    ast
  end

  defp assert_roundtrips(src) do
    ast = parse!(src)
    out = Printer.quoted_to_string(ast)
    reparsed = parse!(out)

    assert strip(ast) == strip(reparsed),
           "reprint changed the parse.\n  in:  #{inspect(src)}\n  out: #{out}"

    out
  end

  test "prefix bnot keeps the separating space (bnot a, not bnota)" do
    out = assert_roundtrips("mod M\n  fn f(a: Int) -> Int = bnot a\n")
    assert out =~ "bnot a"
    refute out =~ "bnota"
  end

  test "bnot nested in a bitwise chain round-trips" do
    assert_roundtrips("mod M\n  fn f(a: Int, b: Int) -> Int = a band bnot b\n")
    assert_roundtrips("mod M\n  fn f(a: Int, b: Int) -> Int = bnot a band b\n")
  end

  test "nested unary minus does not fuse into -- (which re-lexes as an FSM arrow)" do
    # `-(-5)` printed as `--5` re-lexes as the start of an FSM transition `--…`,
    # so the reprint fails to parse. The `-` operand needs a separator when its
    # rendering itself begins with `-`.
    out = assert_roundtrips("mod M\n  fn f(x: Int) -> Int = -(-x)\n")
    refute out =~ "--"
    assert_roundtrips("mod M\n  fn f(x: Int) -> Int = -(-(-x))\n")
  end

  test "an implicit type parameter keeps its braces (stays implicit, not positional)" do
    out = assert_roundtrips("mod M\n  fn id({A: Type}, x: A) -> A = x\n")
    assert out =~ "{A: Type}" or out =~ "{A : Type}"
  end

  test "a with-abstraction rematch arm reprints without crashing" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      type NV = VZ | VS(Nat)
      fn foo(n: Nat) -> Nat =
        with view(n)
          S(m) | VS(m) -> S(m)
          Z() | VZ() -> Z()
    """

    out = assert_roundtrips(src)
    assert out =~ "S(m) | VS(m)"
    assert out =~ "Z() | VZ()"
  end
end
