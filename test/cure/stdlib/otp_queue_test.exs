defmodule Cure.Stdlib.OtpQueueTest do
  @moduledoc """
  `Std.Otp.Queue` — Erlang's amortized two-list functional queue. `enqueue_appends` proves the
  two-list representation faithfully models a FIFO sequence: enqueue places the element at the end
  of the logical order (`to_list(enqueue(x, q)) = to_list(q) ++ [x]`). List ctors are `QNil`/`QCons`
  to avoid ambient name collisions. Cross-checked against Idris (oracle `queue`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.Queue")
  end

  test "enqueue appends to the logical FIFO sequence" do
    src = """
    mod QEnq
      use Std.Otp.Queue
      fn law(x: Nat, q: Q) -> Equivalent(QList, to_list(enqueue(x, q)), append(to_list(q), QCons(x, QNil()))) =
        enqueue_appends(x, q)
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "representation independence: same logical sequence => operations agree" do
    src = """
    mod QRep
      use Std.Otp.Queue
      fn enq(x: Nat, q1: Q, q2: Q, e: Equivalent(QList, to_list(q1), to_list(q2))) -> Equivalent(QList, to_list(enqueue(x, q1)), to_list(enqueue(x, q2))) =
        enqueue_respects(x, q1, q2, e)
      fn deq(q1: Q, q2: Q, e: Equivalent(QList, to_list(q1), to_list(q2))) -> Equivalent(QList, reassemble(dequeue(q1)), reassemble(dequeue(q2))) =
        dequeue_respects(q1, q2, e)
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "dequeue splits off exactly the head (amortized reversal preserves the FIFO sequence)" do
    src = """
    mod QDeq
      use Std.Otp.Queue
      fn law(q: Q) -> Equivalent(QList, reassemble(dequeue(q)), to_list(q)) =
        dequeue_reassembles(q)
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
