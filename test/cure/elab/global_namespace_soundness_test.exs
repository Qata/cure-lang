defmodule Cure.Elab.GlobalNamespaceSoundnessTest do
  @moduledoc """
  Global / constructor / family name-collision behaviour, and the recorded decision
  about it (see memory `global-def-collision-gap`, audit K12 slice-4).

  Two distinct cases, deliberately treated differently:

  1. **Same-name globals WITHIN A MODULE overwrite (soundness) — REJECTED.** Two
     function definitions in one module sharing a name would silently overwrite one
     another in `env.defs`. `check_no_duplicate_defs` (program.ex) rejects this with
     `{:duplicate_definition, name}` — a landed soundness fix this session. (Two
     SIBLING modules sharing a name is legitimate namespacing and is accepted — see
     `Cure.Elab.CrossModuleNamesTest`.)

  2. **A function COEXISTING with a constructor / type of the same name — ACCEPTED,
     and DECLINED as a tightening (analysis discipline, faithfulness-without-
     soundness).** Constructors (`env.ctors`) and functions (`env.defs`) live in
     separate tables, so there is no overwrite; the fn simply shadows the ctor in
     expression position (Idris/Agda unify the value namespace and would reject the
     clash — a PARITY difference, not a soundness hole). The kernel remains sound
     against it: whatever the E-layer resolves the name to, the trusted Core
     re-checks the result, so a mis-resolution can only produce a *rejected* type
     mismatch, never an accepted ill-typed program. The discriminating test below is
     the recorded proof. A rejection rule here is entangled with the design-gated
     K12 qualified-`Sym` work and the LOCKED type-shadowing Approach B, and is
     flagged for operator design sign-off — so it is NOT landed unilaterally.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp check(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    Program.check_ast(ast)
  end

  test "same-named globals within one module are rejected (no silent overwrite)" do
    src =
      "mod A\n  fn foo(x: Int) -> Int = x\n  fn foo(y: Int) -> Int = y\nend\n"

    assert {:error, {:duplicate_definition, :foo}} = check(src)
  end

  test "a fn/ctor name collision cannot smuggle an ill-typed value past the kernel" do
    # `C` is both a constructor (: Foo) and a fn (() -> Int). Passing `C()` where a
    # `Foo` is expected must never be accepted: resolution picks the fn (Int) and the
    # kernel rejects Int-vs-Foo. (Sound regardless of which side resolution favours.)
    src =
      "mod X\n  type Foo = C\n  fn C() -> Int = 3\n  fn wants(x: Foo) -> Int = 0\n  fn test() -> Int = wants(C())\nend\n"

    assert {:error, {:conversion_failure, _, _}} = check(src)
  end
end
