defmodule Cure.Types.ProofTest do
  use ExUnit.Case, async: true

  @moduledoc """
  Proof containers via the CLASSIC entry points (`Cure.Compiler.compile_and_load`
  and `Cure.Types.Checker.check_module`). Both now delegate `proof` containers to
  the sole (dependent) pipeline, so the witness is the inductive `reflexive`, not
  the legacy `:cure_refl` atom, and E026 surfaces as a dependent type error. These
  tests pin that the classic API surface still handles proof containers correctly
  after the port (see memory pre18-surface-construct-gaps); the dependent-entry
  coverage lives in `Cure.Elab.ProofContainerTest`.
  """

  alias Cure.Compiler

  defp compile(source) do
    Compiler.compile_and_load(source, emit_events: false)
  end

  describe "proof containers" do
    test "compile as modules with proof-shaped functions" do
      source = """
      proof ProofTest.Basic
        fn id_law(n: Int) -> Equivalent(Int, n, n) = reflexive(n)
      """

      assert {:ok, mod} = compile(source)
      assert function_exported?(mod, :id_law, 1)
    end

    test "allow multiple propositions in one container" do
      source = """
      proof ProofTest.Several
        fn plus_zero(n: Int) -> Equivalent(Int, n, n) = reflexive(n)
        fn zero_plus(n: Int) -> Equivalent(Int, n, n) = reflexive(n)
      """

      assert {:ok, mod} = compile(source)
      assert function_exported?(mod, :plus_zero, 1)
      assert function_exported?(mod, :zero_plus, 1)
    end
  end

  describe "proof-shape discipline (E026)" do
    test "rejects non-proof return types" do
      source = """
      proof ProofTest.Bad
        fn meaning() -> Int = 42
      """

      # The checker rejects `meaning/0` because Int is not a proof shape.
      # compile_and_load runs without check_types by default, so we call
      # the type checker directly here.
      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(source, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

      assert {:error, errors} = Cure.Types.Checker.check_module(ast, emit_events: false)
      assert inspect(errors) =~ "E026"
    end
  end
end
