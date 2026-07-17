defmodule Cure.Stdlib.OtpSupervisorTest do
  @moduledoc """
  `Std.Otp.Supervisor` — typed supervision: a supervisor's restart preserves its
  declared children (the `Fleet(specs)` type is invariant across restarts). The proof
  is re-checked every build via the stdlib preload; these tests pin the safety content
  — restart returns a fleet of the SAME specs, and a fleet cannot be reshaped to a
  different spec list.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @calculus """
    type ChildSpec = CA | CB | CC
    type Children = CNil | CCons(ChildSpec, Children)
    type Child indices (spec: ChildSpec)
      Alive      : Child(spec)
      Restarting : Child(spec)
    type Fleet indices (specs: Children)
      FNil  : Fleet(CNil)
      FCons : Child(spec) -> Fleet(rest) -> Fleet(CCons(spec, rest))
    fn restart_all({specs: Children}, f: Fleet(specs)) -> Fleet(specs) = match f
      FNil()         -> FNil()
      FCons(c, rest) -> FCons(Alive(), restart_all(rest))
    fn rest_for_one({specs: Children}, f: Fleet(specs), k: Nat) -> Fleet(specs) = match k
      Z()   -> restart_all(f)
      S(k2) -> match f
        FNil()         -> FNil()
        FCons(c, rest) -> FCons(c, rest_for_one(rest, k2))
    fn establish(specs: Children) -> Fleet(specs) = match specs
      CNil()         -> FNil()
      CCons(s, rest) -> FCons(Alive(), establish(rest))
    type Pool indices (spec: ChildSpec)
      PNil  : Pool(spec)
      PCons : Child(spec) -> Pool(spec) -> Pool(spec)
    fn start_child({spec: ChildSpec}, p: Pool(spec)) -> Pool(spec) = PCons(Alive(), p)
    fn restart_pool({spec: ChildSpec}, p: Pool(spec)) -> Pool(spec) = match p
      PNil()         -> PNil()
      PCons(c, rest) -> PCons(Alive(), restart_pool(rest))
  """

  defp verdict(defs) do
    case Program.elaborate("mod SupT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "a supervisor establishes and restarts a fleet of its exact spec" do
    defs = """
      fn boot() -> Fleet(CCons(CA, CCons(CB, CNil))) = establish(CCons(CA, CCons(CB, CNil)))
      fn revive(f: Fleet(CCons(CA, CCons(CB, CNil)))) -> Fleet(CCons(CA, CCons(CB, CNil))) = restart_all(f)
    """

    assert verdict(defs) == :accept
  end

  test "rest_for_one preserves the spec list (keeps a prefix, revives the suffix)" do
    # Keep the first child, revive the child at position 1 and all after it. The result type
    # is still Fleet of the exact same three-child spec.
    defs = """
      fn revive_suffix(f: Fleet(CCons(CA, CCons(CB, CCons(CC, CNil))))) -> Fleet(CCons(CA, CCons(CB, CCons(CC, CNil)))) =
        rest_for_one(f, S(Z()))
    """

    assert verdict(defs) == :accept
  end

  test "restart cannot change the supervisor's declared children (spec list is invariant)" do
    # restart_all's result type is Fleet(specs) with the SAME specs; claiming it yields a
    # DIFFERENT spec list must reject.
    defs = """
      fn bad(f: Fleet(CCons(CA, CNil))) -> Fleet(CCons(CB, CNil)) = restart_all(f)
    """

    assert verdict(defs) == :reject
  end

  test "simple_one_for_one: a dynamic pool keeps its uniform spec across start/restart" do
    defs = """
      fn grow(p: Pool(CA)) -> Pool(CA) = start_child(restart_pool(p))
    """

    assert verdict(defs) == :accept
  end

  test "simple_one_for_one: the pool's uniform spec cannot change" do
    # start_child preserves the pool's spec; claiming it turns a CA-pool into a CB-pool rejects.
    defs = """
      fn bad(p: Pool(CA)) -> Pool(CB) = start_child(p)
    """

    assert verdict(defs) == :reject
  end

  test "the module is compiled into the stdlib preload" do
    assert Code.ensure_loaded?(:"Cure.Std.Otp.Supervisor")
  end

  test "dynamic-pool membership algebra: start grows, terminate cancels start, restart preserves size" do
    src = """
    mod SupPool
      use Std.Otp.Supervisor
      fn grows(spec: ChildSpec, p: Pool(spec)) -> Equivalent(Nat, pool_size(start_child(p)), S(pool_size(p))) =
        start_grows(p)
      fn cancels(spec: ChildSpec, p: Pool(spec)) -> Equivalent(Pool(spec), terminate_child(start_child(p)), p) =
        terminate_start_id(p)
      fn keeps_size(spec: ChildSpec, p: Pool(spec)) -> Equivalent(Nat, pool_size(restart_pool(p)), pool_size(p)) =
        restart_preserves_size(p)
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end
end
