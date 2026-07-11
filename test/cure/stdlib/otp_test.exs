defmodule Cure.Stdlib.OtpTest do
  @moduledoc """
  `Std.Otp` — the typed BEAM process algebra. The payoff of the whole Effect stack:
  a `Pid(m)` accepts only messages of type `m`, so sending the WRONG message to a
  process is a COMPILE error (design 2026-07-10-checked-beam-concurrency §2). This
  is the guarantee `Std.Otp.Raw`'s untyped `Pid` cannot give.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program
  alias Cure.Core.Env

  # A program in module `App` that `use`s Std.Otp and declares a message ADT.
  defp app(body) do
    Program.elaborate("mod App\n  use Std.Otp\n  type Cmd = Inc | Dec\n#{body}end\n")
  end

  test "the module itself elaborates on the dependent pipeline" do
    src = File.read!("lib/std/otp.cure")
    {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
    assert {:ok, env, locals} = Program.check_ast_with_locals(ast)
    assert :tell in locals and :cast in locals and :self in locals
    # `tell` is effect-typed and its message argument type IS the pid's phantom.
    assert effect_result?(Env.get_def(env, :tell).type)
  end

  test "a well-typed message to a Pid(m) is accepted" do
    assert {:ok, _} =
             app("  fn go(p: Pid(Cmd)) -> Effect(Unit) =\n    tell(p, Inc())\n")
  end

  test "the WRONG message type to a Pid(m) is a compile error" do
    # `5 : Int` sent to a `Pid(Cmd)` must fail — the message type does not unify
    # with the pid's accepted type.
    assert {:error, _} =
             app("  fn go(p: Pid(Cmd)) -> Effect(Unit) =\n    tell(p, 5)\n")
  end

  test "a sequenced typed conversation elaborates (tell then cast, via effect bind)" do
    assert {:ok, _} =
             app("""
               fn talk(p: Pid(Cmd)) -> Effect(Unit) =
                 let u = tell(p, Inc())
                 cast(p, Dec())
             """)
  end

  test "cast is typed too — wrong message to cast is a compile error" do
    assert {:error, _} =
             app("  fn go(p: Pid(Cmd)) -> Effect(Unit) =\n    cast(p, 5)\n")
  end

  defp effect_result?({:pi, _g, _d, cod}), do: effect_result?(cod)
  defp effect_result?({:effect_type, _}), do: true
  defp effect_result?(_), do: false
end
