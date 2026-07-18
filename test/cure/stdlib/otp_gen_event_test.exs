defmodule Cure.Stdlib.OtpGenEventTest do
  @moduledoc """
  `Std.Otp.GenEvent` — the event-manager behaviour. `notify` broadcasts an event to every handler;
  `notify_preserves_count`/`notify_preserves_ifaces` prove a broadcast preserves the handler
  configuration (count and exact interface list), and the `Manager(ifaces)` index re-certifies it.
  Cross-checked against Idris (oracle `gen_event`).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.GenEvent")
  end

  test "broadcast preserves the handler configuration (count and interfaces)" do
    src = """
    mod GeInst
      use Std.Otp.GenEvent
      fn keeps_count(e: Event, {ifaces: IfaceList}, mgr: Manager(ifaces)) -> Equivalent(Nat, count(notify(e, mgr)), count(mgr)) =
        notify_preserves_count(e, mgr)
      fn keeps_ifaces(e: Event, {ifaces: IfaceList}, mgr: Manager(ifaces)) -> Equivalent(IfaceList, interfaces(notify(e, mgr)), interfaces(mgr)) =
        notify_preserves_ifaces(e, mgr)
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "swap_at (code_change): upgrading a handler preserves the interface configuration" do
    src = """
    mod GeSwap
      use Std.Otp.GenEvent
      fn keeps({ifaces: IfaceList}, mgr: Manager(ifaces), pos: Pos(ifaces), new_st: Nat) -> Equivalent(IfaceList, interfaces(swap_at(mgr, pos, new_st)), interfaces(mgr)) =
        swap_preserves_ifaces(mgr, pos, new_st)
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "remove_at: removing a handler at a position deletes exactly that interface entry" do
    # A two-handler manager; removing the SECOND handler (There Here) leaves a manager typed by
    # the interface list with only the first entry.
    src = """
    mod GeRem
      use Std.Otp.GenEvent
      fn two() -> Manager(ICons(MkEvSet(T(), F(), F()), ICons(MkEvSet(F(), T(), F()), INil()))) =
        add_handler(MkEvSet(T(), F(), F()), Z(), add_handler(MkEvSet(F(), T(), F()), Z(), MNil()))
      fn drop_second() -> Manager(ICons(MkEvSet(T(), F(), F()), INil())) =
        remove_at(two(), There(MkEvSet(T(), F(), F()), Here(MkEvSet(F(), T(), F()), INil())))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "install/remove are inverse on the manager configuration" do
    src = """
    mod GeInv
      use Std.Otp.GenEvent
      fn inv(iface: EvSet, st: Nat, {ifaces: IfaceList}, mgr: Manager(ifaces)) -> Equivalent(Manager(ifaces), remove_head(add_handler(iface, st, mgr)), mgr) =
        add_remove_inverse(iface, st, mgr)
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "the Manager index certifies notify preserves the interface list at the type level" do
    # notify : Manager(ifaces) -> Manager(ifaces); a two-handler manager stays two-handler-typed.
    src = """
    mod GeType
      use Std.Otp.GenEvent
      fn two() -> Manager(ICons(MkEvSet(T(), F(), F()), ICons(MkEvSet(F(), T(), F()), INil()))) =
        add_handler(MkEvSet(T(), F(), F()), Z(), add_handler(MkEvSet(F(), T(), F()), Z(), MNil()))
      fn after() -> Manager(ICons(MkEvSet(T(), F(), F()), ICons(MkEvSet(F(), T(), F()), INil()))) =
        notify(EvA(), two())
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
