defmodule Cure.Stdlib.OtpRegistryTest do
  @moduledoc """
  `Std.Otp.Registry` — the "type must not lie" obligations (G7): a raw `Pid` is not a
  `GenServer` (F-2), and `whereis` is partial (`PidOption`, F-2c). The proof is
  re-checked every build via the stdlib preload; these tests pin the safety content —
  a bare `Pid` cannot be used where a typed server is expected, and a `whereis`
  consumer that ignores the absent case is rejected as non-total.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @calculus """
    type Pid = MkPid
    type GenServer(q: Type, r: Type) indices ()
      MkGen : Pid -> GenServer(q, r)
    type PidOption = NoPid | SomePid(Pid)
    fn server_pid({q: Type}, {r: Type}, g: GenServer(q, r)) -> Pid = match g
      MkGen(p) -> p
    fn expect_server({q: Type}, {r: Type}, p: Pid) -> GenServer(q, r) = MkGen(p)
    fn with_pid({s: Type}, o: PidOption, on_found: (Pid) -> s, on_absent: () -> s) -> s = match o
      SomePid(p) -> on_found(p)
      NoPid()    -> on_absent()
  """

  defp verdict(defs) do
    case Program.elaborate("mod RegistryT\n#{@calculus}#{defs}\nend\n") do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  test "a name lookup yields a PidOption, and expect_server upgrades a pid explicitly" do
    defs = """
      fn found() -> PidOption = SomePid(MkPid)
      fn upgrade(p: Pid) -> GenServer(Pid, Pid) = expect_server(p)
    """

    assert verdict(defs) == :accept
  end

  test "F-2: a bare Pid cannot be used where a GenServer is expected" do
    defs = """
      fn bad() -> Pid = server_pid(MkPid)
    """

    assert verdict(defs) == :reject
  end

  test "F-2c: a whereis consumer that ignores the absent case is non-total" do
    defs = """
      fn bad_use(o: PidOption) -> Pid = match o
        SomePid(p) -> p
    """

    assert verdict(defs) == :reject
  end
end
