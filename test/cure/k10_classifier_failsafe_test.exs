defmodule Cure.K10ClassifierFailsafeTest do
  @moduledoc """
  K10 #12 — soundness of the `dependent?/1` compile-path classifier.

  The compiler and `Types.Checker` gate on `Cure.Elab.Program.dependent?(ast)`:
  dependent modules route to the sound Core kernel; non-dependent ones to the
  weaker legacy checker. `dependent?/1` is SYNTACTIC, so a module that only
  *calls* dependent functions (no local `indexed_type`/`sigma`/`rewrite`/implicit
  param/`Eq`/`refl`/pair-proj) is misclassified as non-dependent.

  This pins why that misclassification is nonetheless FAIL-SAFE: dependent values
  and functions pervasively carry implicit type/index params (`{a}`, `{n}`), and
  the legacy checker does NOT insert implicit arguments — so any attempt to build
  or consume a dependent value in a misclassified module hits an `arity_mismatch`
  reject rather than an unsound accept. The soundness invariant guarded here is
  the load-bearing one: **a misclassified unsafe dependent call is never ACCEPTED
  by the legacy path.**
  """
  use ExUnit.Case, async: false
  alias Cure.Compiler.{Lexer, Parser}

  # `head(empty())` violates head : Vector(a, S(n)) -> a  (empty : Vector(a, Z)),
  # and the module carries no local dependent syntax.
  @src """
  mod ProbeUnsafe
    use Std.Vector

    fn boom() -> Int = head(empty())
  end
  """

  test "a module that only calls a dependent fn is misclassified non-dependent" do
    {:ok, toks} = Lexer.tokenize(@src, file: "probe.cure", emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: "probe.cure", emit_events: false)
    # Documents the (known, #12) classifier under-approximation.
    refute Cure.Elab.Program.dependent?(ast)
  end

  test "the misclassified unsafe dependent call is NOT unsoundly accepted (fail-safe)" do
    {:ok, toks} = Lexer.tokenize(@src, file: "probe.cure", emit_events: false)
    {:ok, ast} = Parser.parse(toks, file: "probe.cure", emit_events: false)

    # Load-bearing soundness invariant: the legacy path rejects (implicit-arg
    # arity barrier), never silently accepting the length-unsafe call.
    assert {:error, _} = Cure.Types.Checker.check_module(ast, file: "probe.cure", emit_events: false)
  end
end
