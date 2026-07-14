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

  test "opaque type round-trips instead of inspecting the raw container tuple" do
    # `container_to_string`'s catch-all `inspect/1`-ed the `:opaque` container into
    # a raw Elixir tuple that fails to reparse, so `cure migrate` aborted any file
    # containing an `opaque type`. It must reprint as surface `opaque type Name`.
    out = assert_roundtrips("mod M\n  opaque type Handle\n")
    assert out =~ "opaque type Handle"
    refute out =~ ":container"
  end

  test "parameterized opaque type keeps its head params on round-trip" do
    out = assert_roundtrips("mod M\n  opaque type Box(a)\n")
    assert out =~ "opaque type Box(a)"
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

  test "a typealias reprints as typealias, not type (transparent synonym, not a nominal ADT)" do
    # `typealias X = …` parses to a transparent `:type_annotation`; the printer
    # emitted the keyword `type`, which reparses to a nominal single-constructor
    # `:container` — a different node kind and different semantics. Hits the live
    # corpus (`lib/std/char.cure`, `lib/std/string.cure`).
    out = assert_roundtrips("typealias Char = Bounded(1114112)\n")
    assert out =~ "typealias Char"
    refute out =~ ~r/\btype Char/
  end

  test "a nullary constructor keeps its parens (stays a constructor, not a type reference)" do
    # `None()` in a sum type parses to a nullary constructor `{:function_def,
    # …, []}`; the printer dropped the parens to `None`, which reparses to a bare
    # `{:variable, …}` type reference. Hits `lib/std/option.cure`.
    out = assert_roundtrips("type Option(t) = Some(t) | None()\n")
    assert out =~ "None()"
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

  test "the unit value round-trips as ()" do
    # The parser gives `()` its own node kind (`:unit_value`), not a `:literal`, and the
    # printer had no clause for it — so `cure fmt`/`migrate` RAISED on any file containing
    # the unit value. No stdlib file used `()` until Std.Otp's discard shape did.
    out = assert_roundtrips("mod M\n  fn nothing() -> Unit = ()\n")
    assert out =~ "= ()"
    refute out =~ "unit_value"

    # The shape that exposed it: bind an effectful result, discard it, return unit.
    discard = assert_roundtrips("mod M\n  fn go(p: Int) -> Unit =\n    let x = p\n    ()\n")
    assert discard =~ "()"
  end
end
