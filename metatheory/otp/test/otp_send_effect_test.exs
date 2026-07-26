defmodule Cure.Stdlib.OtpSendEffectTest do
  @moduledoc """
  `Std.Otp.SendEffect` — obligation (2) made EFFECT-HONEST: the clause-derived pid
  message index and its send-safety survive the `Effect` discipline (`spawn`/`post`
  return `Effect(...)`, sequenced with monadic `let`). The module is re-checked every
  build via the stdlib preload; these tests pin the *safety content* under effects —
  a message not of the actor's derived type is rejected even when threaded through
  `effect_bind`, and a non-total handler still cannot form the actor.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  # The self-contained effect-honest calculus (mirrors metatheory/otp/src/otp_send_effect.cure).
  @calculus """
    type Reply0 = R0
    type Msg = Inc | Dec | Query(Reply0)
    type Response = Ack | Count(Reply0)
    type Pid(m: Type) indices ()
      MkPid : ((m) -> Response) -> Pid(m)
    fn spawn_actor({m: Type}, msg_handler: (m) -> Response) -> Effect(Pid(m)) = MkPid(msg_handler)
    fn post({m: Type}, p: Pid(m), msg: m) -> Effect(Response) = match p
      MkPid(h) -> h(msg)
    fn dispatch(m: Msg) -> Response = match m
      Inc()     -> Ack
      Dec()     -> Ack
      Query(x)  -> Count(x)
  """

  defp verdict(defs) do
    case Program.elaborate("mod SendEff\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "the effect-threaded client (spawn then post) is send-safe" do
    defs = """
      fn deliver_client(msg: Msg) -> Effect(Response) =
        let pid = spawn_actor(dispatch)
        post(pid, msg)
    """

    assert verdict(defs) == :accept
  end

  test "posting a wrong-typed message is rejected under the effect discipline" do
    # pid : Pid(Msg) (index derived from dispatch); posting a Response must reject
    # even though spawn/post are sequenced as effects.
    defs = """
      fn deliver_bad(bad: Response) -> Effect(Response) =
        let pid = spawn_actor(dispatch)
        post(pid, bad)
    """

    assert verdict(defs) == :reject
  end

  test "a non-total handler cannot form the actor, so no effectful send can reach it" do
    defs = """
      fn partial(m: Msg) -> Response = match m
        Inc() -> Ack
      fn deliver_partial(msg: Msg) -> Effect(Response) =
        let pid = spawn_actor(partial)
        post(pid, msg)
    """

    assert verdict(defs) == :reject
  end
end
