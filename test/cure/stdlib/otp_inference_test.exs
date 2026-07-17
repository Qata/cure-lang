defmodule Cure.Stdlib.OtpInferenceTest do
  @moduledoc """
  `Std.Otp.Inference` — the decidable core of mailbox-type inference (G9). Two things
  are pinned: (1) the elaborator INFERS the mailbox type from a handler with no
  annotation (the clause-derived pid index — this is the annotation-free typing the
  literature calls open, for the first-order case); (2) the derived interface's safety
  checks are DECIDABLE — `decide_handles` (membership) and `decide_all_handled`
  (self-send closure) are total, proof-carrying, and usable cross-module.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  defp verdict(src) do
    case Program.elaborate(src) do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "the elaborator infers the mailbox type from the handler with no annotation" do
    # `spawn_actor(dispatch)` yields `Pid(Msg)` — Msg is solved from `dispatch`, never
    # annotated. This is first-order mailbox-type inference in the shipping compiler.
    src = """
    mod Inf
      type Reply0 = R0
      type Msg = Inc | Dec | Query(Reply0)
      type Response = Ack | Count(Reply0)
      type Pid(m: Type) indices ()
        MkPid : ((m) -> Response) -> Pid(m)
      fn spawn_actor({m: Type}, msg_handler: (m) -> Response) -> Pid(m) = MkPid(msg_handler)
      fn dispatch(m: Msg) -> Response = match m
        Inc()    -> Ack
        Dec()    -> Ack
        Query(x) -> Count(x)
      fn post({m: Type}, p: Pid(m), msg: m) -> Response = match p
        MkPid(h) -> h(msg)
      fn client(msg: Msg) -> Response = post(spawn_actor(dispatch), msg)
    end
    """

    assert verdict(src) == :accept
  end

  test "the membership decision procedure is usable cross-module on an inferred interface" do
    src = """
    mod UseInf
      use Std.Decision
      use Std.Otp.Inference
      fn is_tb_handled() -> Decision(Handles(TB, TCons(TA, TCons(TB, TNil)))) =
        decide_handles(TB, TCons(TA, TCons(TB, TNil)))
      fn all_sends_ok() -> Decision(AllHandled(TCons(TA, TNil), TCons(TA, TCons(TB, TNil)))) =
        decide_all_handled(TCons(TA, TNil), TCons(TA, TCons(TB, TNil)))
    end
    """

    assert verdict(src) == :accept
  end

  test "a membership proof exists for a tag in the interface" do
    src = """
    mod MemOk
      use Std.Otp.Inference
      fn tb_in() -> Handles(TB, TCons(TA, TCons(TB, TNil))) = HThere(HHere())
    end
    """

    assert verdict(src) == :accept
  end

  test "a tag absent from the interface has no membership proof (unconstructible)" do
    src = """
    mod MemBad
      use Std.Otp.Inference
      fn tc_in() -> Handles(TC, TCons(TA, TCons(TB, TNil))) = HThere(HThere(HHere()))
    end
    """

    assert verdict(src) == :reject
  end
end
