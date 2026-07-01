defmodule Cure.Elab.EraseTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Env
  alias Cure.Elab.{Declarations, Erase}

  @src """
  type Dec = Dcoupled | Causal
  type Sig = CSig | ESig
  type SVDesc = SVNil | SVCons(Sig, SVDesc)
  fn andd(x: Dec, y: Dec) -> Dec = x
  type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
    prim : SF(as, bs, Causal)
    seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
  """

  defp build_env do
    alias Cure.Compiler.{Lexer, Parser}
    {:ok, toks} = Lexer.tokenize(@src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    items = case ast do {:block, _, xs} -> xs; x -> [x] end
    Enum.reduce(items, Env.empty(), fn d, e -> {:ok, e2} = Declarations.elaborate(d, e); e2 end)
  end

  test "erases the erased index arguments from a seq value, keeping l and r" do
    env = build_env()
    nil_ = {:ctor, :SVNil, []}
    causal = {:ctor, :Causal, []}

    seq = {:ctor, :seq, [nil_, nil_, causal, nil_, causal, {:global, :l}, {:global, :r}]}
    assert Erase.erase(env, seq) == {:ctor, :seq, [{:global, :l}, {:global, :r}]}
  end

  test "erases prim to a nullary runtime constructor" do
    env = build_env()
    prim = {:ctor, :prim, [{:ctor, :SVNil, []}, {:ctor, :SVNil, []}]}
    assert Erase.erase(env, prim) == {:ctor, :prim, []}
  end

  test "erases recursively inside nested constructors" do
    env = build_env()
    inner = {:ctor, :prim, [{:ctor, :SVNil, []}, {:ctor, :SVNil, []}]}
    seq =
      {:ctor, :seq,
       [
         {:ctor, :SVNil, []},
         {:ctor, :SVNil, []},
         {:ctor, :Causal, []},
         {:ctor, :SVNil, []},
         {:ctor, :Causal, []},
         inner,
         inner
       ]}

    assert Erase.erase(env, seq) ==
             {:ctor, :seq, [{:ctor, :prim, []}, {:ctor, :prim, []}]}
  end

  test "detects holes in a term" do
    assert Erase.has_hole?({:lam, {:type, 0}, {:hole, "body"}})
    assert Erase.has_hole?({:ctor, :seq, [{:hole, "x"}]})
    refute Erase.has_hole?({:ctor, :prim, []})
  end
end
