defmodule Cure.Elab.DependentRoutingTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp parse!(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    ast
  end

  test "indexed types route through the dependent compiler" do
    ast =
      parse!("""
      mod RouteIndexed
        type Nat = Z | S(Nat)
        indexed type Vector(a: Type, n: Nat) where
          empty : Vector(a, Z)
      end
      """)

    assert Program.dependent?(ast)
  end

  test "typed erased parameters route through the dependent compiler without indexed types" do
    ast =
      parse!("""
      mod RouteImplicit
        type Nat = Z | S(Nat)
        fn id_nat({n: Nat}, x: Nat) -> Nat = x
      end
      """)

    assert Program.dependent?(ast)
  end

  test "Sigma and projection surface route through the dependent compiler" do
    ast =
      parse!("""
      mod RouteSigma
        type Dec = Dcoupled | Causal
        fn recover(p: Sigma(x: Dec, Dec)) -> Dec = p.2
      end
      """)

    assert Program.dependent?(ast)
  end

  test "plain modules stay on the legacy compiler path" do
    ast =
      parse!("""
      mod RoutePlain
        fn id(x: Int) -> Int = x
      end
      """)

    refute Program.dependent?(ast)
  end
end
