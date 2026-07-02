defmodule Cure.Elab.SigmaSurfaceTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.Env
  alias Cure.Elab.Declarations

  @base """
  type Dec = Dcoupled | Causal
  type Sig = CSig | ESig
  type SVDesc = SVNil | SVCons(Sig, SVDesc)
  fn andd(x: Dec, y: Dec) -> Dec = x
  type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
    prim : SF(as, bs, Causal)
    seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
  """

  defp elaborate_all(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    items = case ast do {:block, _, xs} -> xs; x -> [x] end

    Enum.reduce_while(items, {:ok, Env.empty()}, fn decl, {:ok, env} ->
      case Declarations.elaborate(decl, env) do
        {:ok, env2} -> {:cont, {:ok, env2}}
        err -> {:halt, err}
      end
    end)
  end

  defp unwrap_lams({:lam, _dom, body}), do: unwrap_lams(body)
  defp unwrap_lams(term), do: term

  test "forget_dec packages the decoupledness index into a Sigma pair" do
    src =
      @base <>
        "fn forget_dec({as: SVDesc}, {bs: SVDesc}, d: Dec, sf: SF(as, bs, d)) -> Sigma(x: Dec, SF(as, bs, x)) = %[d, sf]\n"

    assert {:ok, env} = elaborate_all(src)
    assert %{name: :forget_dec, type: type, body: body} = Env.get_def(env, :forget_dec)
    assert {:pair, _d, _sf} = unwrap_lams(body)
    # Declared type ends in a dependent Σ.
    assert {:pi, _, _} = type
  end

  test "recover projects the second component at the projected index type" do
    src =
      @base <>
        "fn recover({as: SVDesc}, {bs: SVDesc}, p: Sigma(x: Dec, SF(as, bs, x))) -> SF(as, bs, p.1) = p.2\n"

    assert {:ok, env} = elaborate_all(src)
    assert %{name: :recover, body: body} = Env.get_def(env, :recover)
    assert {:snd, _p} = unwrap_lams(body)
  end

  test "rejects a pair whose second component's type mismatches B[a/x]" do
    # Claim the pair packs Dcoupled, but sf : SF(as,bs,d) with d free ≠ Dcoupled.
    src =
      @base <>
        "fn bad({as: SVDesc}, {bs: SVDesc}, {d: Dec}, sf: SF(as, bs, d)) -> Sigma(x: Dec, SF(as, bs, x)) = %[Dcoupled, sf]\n"

    assert {:error, _} = elaborate_all(src)
  end
end
