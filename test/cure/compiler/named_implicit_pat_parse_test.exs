defmodule Cure.Compiler.NamedImplicitPatParseTest do
  @moduledoc """
  Surface syntax for named-implicit dot patterns (`{ name = <expr> }`) — the
  Lean/Idris-style annotation of a constructor's erased implicit index in a
  pattern-argument position, e.g. `vcons({k = .m}, h, r)`.

  Parsing a `{ IDENT = … }` in expression-prefix position produces a
  `{:named_implicit_pat, meta, name, inner_expr}` node; the inner expression is
  parsed with the full grammar, so a leading `.` yields a `{:forced_pattern,…}`.
  Using a named-implicit OUTSIDE a pattern is rejected at elaboration with
  `{:named_implicit_not_in_pattern, _}`.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp parse!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  # (a) `{k = .m}` as a ctor arg parses to a named-implicit whose inner is a
  #     bare-identifier forced pattern.
  test "(a) `vcons({k = .m}, h, r)` parses the named-implicit dot pattern" do
    ast = parse!("match v { vcons({k = .m}, h, r) -> h }")
    assert {:pattern_match, _, [_scrutinee, arm]} = ast
    assert {:match_arm, ameta, _body} = arm
    assert {:function_call, _cmeta, [arg0, arg1, arg2]} = Keyword.get(ameta, :pattern)
    assert {:named_implicit_pat, _, "k", inner} = arg0
    assert {:forced_pattern, _, {:variable, _, "m"}} = inner
    assert {:variable, _, "h"} = arg1
    assert {:variable, _, "r"} = arg2
  end

  # (b) The inner expression uses the full grammar: `{k = .(Z())}` parses the
  #     compound forced pattern `.(Z())` as a constructor application.
  test "(b) `{k = .(Z())}` parses the compound forced inner" do
    ast = parse!("match v { vcons({k = .(Z())}, h, r) -> h }")
    assert {:pattern_match, _, [_scrutinee, arm]} = ast
    assert {:match_arm, ameta, _body} = arm
    assert {:function_call, _cmeta, [arg0 | _]} = Keyword.get(ameta, :pattern)
    assert {:named_implicit_pat, _, "k", inner} = arg0
    assert {:forced_pattern, _, {:function_call, zmeta, []}} = inner
    assert Keyword.get(zmeta, :name) == "Z"
  end

  # (c) NEGATIVE: a named-implicit used as an ordinary expression (a function
  #     body, not a pattern) is rejected at ELABORATION time. Parsing succeeds by
  #     design, so this drives the fixture through the full pipeline.
  test "(c) a named-implicit in ordinary expression position is rejected" do
    src = """
    type Nat = Z | S(Nat)
    fn f() -> Nat = {k = .m}
    """

    assert {:error, {:named_implicit_not_in_pattern, _meta}} = Program.elaborate(src)
  end
end
