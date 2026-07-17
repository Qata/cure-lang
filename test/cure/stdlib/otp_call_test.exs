defmodule Cure.Stdlib.OtpCallTest do
  @moduledoc """
  `Std.Otp.Call` — `gen_server:call` failure/totality (G6): a total call reifies its
  failure (`Replied(r) | Failed(CallError)`), and the kernel's exhaustiveness check
  forces every consumer to handle the failure. The proof is re-checked every build via
  the stdlib preload; these tests pin the safety content — a consumer that ignores the
  `Failed` case is rejected as non-total.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @calculus """
    type CallError = Timeout | NoProc | ServerDied
    type CallOutcome(r: Type) indices ()
      Replied : (r) -> CallOutcome(r)
      Failed  : CallError -> CallOutcome(r)
    type Reply = RVal
  """

  defp verdict(defs) do
    case Program.elaborate("mod CallT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "a total consumer handling both reply and failure type-checks" do
    defs = """
      fn resume({r: Type}, {s: Type}, o: CallOutcome(r), on_reply: (r) -> s, on_fail: (CallError) -> s) -> s = match o
        Replied(x) -> on_reply(x)
        Failed(e)  -> on_fail(e)
    """

    assert verdict(defs) == :accept
  end

  test "a consumer that ignores the failure case is rejected as non-total" do
    # The whole point of G6: you cannot pretend a call always succeeds.
    defs = """
      fn bad({r: Type}, o: CallOutcome(r), on_reply: (r) -> Reply) -> Reply = match o
        Replied(x) -> on_reply(x)
    """

    assert verdict(defs) == :reject
  end

  test "both a successful and a failed outcome are inhabited" do
    defs = """
      fn ok_call() -> CallOutcome(Reply) = Replied(RVal)
      fn dead_call() -> CallOutcome(Reply) = Failed(ServerDied)
    """

    assert verdict(defs) == :accept
  end
end
