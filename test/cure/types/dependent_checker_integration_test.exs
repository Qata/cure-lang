defmodule Cure.Types.DependentCheckerIntegrationTest do
  @moduledoc """
  The real compiler type-checker (`Cure.Types.Checker.check_module`, the stage
  `Cure.Compiler` calls) routes dependent modules through the `Cure.Core` kernel
  instead of the faked `Cure.Types.*` modules. A well-typed dependent module
  passes; an ill-typed one is rejected with the kernel's judgement — surfaced
  through the language's own compile path, not a side channel.
  """
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Types.Checker

  defp check(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    Checker.check_module(ast, emit_events: false)
  end

  @dependent """
  mod Slice1
    type Dec = Dcoupled | Causal
    type Sig = CSig | ESig
    type SVDesc = SVNil | SVCons(Sig, SVDesc)
    fn andd(x: Dec, y: Dec) -> Dec = x
    type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
      prim : SF(as, bs, Causal)
      seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
    fn compose({as: SVDesc}, {bs: SVDesc}, {cs: SVDesc}, {d1: Dec}, {d2: Dec}, l: SF(as, bs, d1), r: SF(bs, cs, d2)) -> SF(as, cs, andd(d1, d2)) = seq(l, r)
  end
  """

  test "a well-typed dependent module passes through the real checker via the kernel" do
    assert {:ok, _} = check(@dependent)
  end

  test "an ill-typed dependent module is rejected by the real checker via the kernel" do
    bad =
      String.replace(
        @dependent,
        "-> SF(as, cs, andd(d1, d2)) = seq(l, r)",
        "-> SF(as, cs, Dcoupled) = seq(l, r)"
      )

    assert {:error, _} = check(bad)
  end

  test "a non-total function used in a dependent type is rejected via the kernel" do
    bad =
      String.replace(@dependent, "fn andd(x: Dec, y: Dec) -> Dec = x", "fn andd(x: Dec, y: Dec) -> Dec = andd(x, y)")

    assert {:error, _} = check(bad)
  end
end
