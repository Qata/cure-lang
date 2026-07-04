defmodule Cure.Elab.TypeShadowingTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp elaborate(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    Program.check_ast(ast)
  end

  test "R1a: explicit `use Std.Nat` + local `Nat = Zero|Suc` — local ctors cover the match" do
    src = """
    mod ExplicitShadow
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn add(a: Nat, b: Nat) -> Nat = match a
        Zero() -> b
        Suc(m) -> Suc(add(m, b))
    end
    """

    assert {:ok, _env} = elaborate(src)
  end
end
