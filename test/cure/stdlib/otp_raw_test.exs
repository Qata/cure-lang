defmodule Cure.Stdlib.OtpRawTest do
  @moduledoc """
  `Std.Otp.Raw` — the sealed effect-typed raw base of the BEAM process algebra —
  elaborates on the DEPENDENT pipeline, and every side-effecting operation returns
  `Effect(T)` (no purity lie). This is the first real consumer of the whole Effect
  stack (surface `Effect(T)` + effectful `@extern` + graded binders) composing into
  a library. Message/reply payloads are POLYMORPHIC (the narrow point where the
  typed `Std.Otp` supplies a message code), not `Any`.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program
  alias Cure.Core.Env

  setup_all do
    src = File.read!("lib/std/otp_raw.cure")
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    assert {:ok, env, locals} = Program.check_ast_with_locals(ast)
    {:ok, env: env, locals: locals}
  end

  # Walk a def's Pi telescope to its result and check the head is `Effect(_)`.
  defp effect_result?({:pi, _g, _d, cod}), do: effect_result?(cod)
  defp effect_result?({:effect_type, _}), do: true
  defp effect_result?(_), do: false

  test "the module elaborates on the dependent pipeline", %{locals: locals} do
    assert :raw_self in locals
    assert :raw_send in locals
    assert :raw_call in locals
  end

  test "raw_self : Effect(RawPid(m, m))", %{env: env} do
    assert {:effect_type, {:data, :RawPid, [global: :m, global: :m], []}} =
             Env.get_def(env, :raw_self).type
  end

  test "every side-effecting op returns Effect(_) — the purity lie is closed", %{env: env} do
    for name <- [
          :raw_send,
          :raw_cast,
          :raw_call,
          :raw_monitor,
          :raw_stop,
          :raw_send_after,
          :raw_cancel_timer,
          :raw_demonitor,
          :raw_link,
          :raw_unlink,
          :raw_exit,
          :raw_is_alive,
          :raw_register,
          :raw_unregister,
          :raw_whereis
        ] do
      assert effect_result?(Env.get_def(env, name).type),
             "#{name} must return Effect(_), got #{inspect(Env.get_def(env, name).type)}"
    end
  end

  test "raw_send is a postulated FFI global (an @extern), not an inlinable def", %{env: env} do
    assert {:extern, {:erlang, :send, 2}} = Env.get_def(env, :raw_send).body
  end

  test "messages are polymorphic (not Any): raw_send binds a Type param for the message", %{
    env: env
  } do
    # {m : Type(erased)} -> Pid -> m -> Effect(Unit): the outer binder is the
    # erased message-type param, and the message argument is that bound variable.
    assert {:pi, :erased, {:type, 0}, _} = Env.get_def(env, :raw_send).type
  end
end
