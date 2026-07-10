defmodule Cure.Audit.LedgerTest do
  use ExUnit.Case, async: true
  alias Cure.Audit.Ledger

  defp audit(src), do: Ledger.audit_source(src, "Test")

  test "an @extern yields exactly one ffi_postulate with its MFA and rendered type" do
    src = """
    mod Test.One
      @extern(:erlang, :length, 1)
      fn len(xs: List(t)) -> Int
    end
    """

    report = audit(src)
    assert [axiom] = report.axioms
    assert axiom.mfa == {:erlang, :length, 1}
    assert axiom.bucket == :otp
    assert axiom.type == "∀ {a}. List(a) -> Int"
  end

  test "widening the declared type changes the rendered line" do
    narrow = """
    mod Test.Narrow
      @extern(:erlang, :length, 1)
      fn len(xs: List(Int)) -> Int
    end
    """

    wide = """
    mod Test.Wide
      @extern(:erlang, :length, 1)
      fn len(xs: List(t)) -> Int
    end
    """

    [a] = audit(narrow).axioms
    [b] = audit(wide).axioms
    assert a.mfa == b.mfa
    refute a.type == b.type
  end

  test "buckets by target module" do
    assert Ledger.bucket({:erlang, :length, 1}) == :otp
    assert Ledger.bucket({:cure_std_crdt, :or_add, 4}) == :cure_runtime
    assert Ledger.bucket({:"Elixir.Cure.FSM.Builtins", :spawn_fsm, 2}) == :cure_bridge
  end

  test "divergence: builtin_op is an axiom here and invisible to codegen reachability" do
    src = """
    mod Test.Arith
      fn double(x: Int) -> Int = x + x
    end
    """

    {:ok, env} = Cure.Elab.Program.elaborate(src)
    roots = Ledger.roots(env)

    # The ledger counts every builtin operator in the env.
    assert audit(src).builtin_count == 31

    # Codegen's walk deliberately drops them ("never emitted as a function form").
    codegen_reachable = Cure.Elab.Program.reachable_def_names(env, roots)
    builtin_names = for {n, d} <- env.defs, Map.get(d, :builtin_op), do: n
    assert Enum.all?(builtin_names, fn n -> n not in codegen_reachable end)
    refute builtin_names == []
  end

  test "an opaque type is reported; a genuinely empty inductive is not" do
    opaque = """
    mod Test.Opaque
      opaque type Effect
    end
    """

    empty = """
    mod Test.Empty
      type Void =
        |
    end
    """

    assert audit(opaque).opaque == [:Effect]
    assert audit(empty).opaque == []
  end

  test "roots exclude the prelude" do
    src = """
    mod Test.Roots
      fn f(x: Int) -> Int = x
    end
    """

    {:ok, env} = Cure.Elab.Program.elaborate(src)
    assert Ledger.roots(env) == [:f]
  end

  test "prelude externs are not attributed to the audited module" do
    src = """
    mod Test.NoPreludeLeak
      fn f(x: Int) -> Int = x
    end
    """

    assert audit(src).axioms == []
  end

  test "a module that fails to elaborate is recorded as unaudited" do
    report = Ledger.audit_source("mod Test.Broken\n  fn f(x: Int) -> = \nend\n", "Test.Broken")
    assert [{"Test.Broken", _reason}] = report.unaudited
    assert report.axioms == []
  end
end

defmodule Cure.Audit.TargetsTest do
  use ExUnit.Case, async: true
  alias Cure.Audit.Targets

  test "atomvm lacks re, inets, httpc, persistent_term and Registry" do
    for m <- [:re, :inets, :httpc, :persistent_term, :"Elixir.Registry"] do
      assert Targets.unavailable?(:atomvm, {m, :any, 0}), "expected #{m} unavailable"
    end
  end

  test "atomvm has erlang and lists" do
    refute Targets.unavailable?(:atomvm, {:erlang, :length, 1})
    refute Targets.unavailable?(:atomvm, {:lists, :reverse, 1})
  end

  test "an unknown target has nothing unavailable" do
    assert Targets.unavailable(:no_such_vm) == MapSet.new()
  end

  test "atomvm is a known target" do
    assert :atomvm in Targets.known()
  end
end
