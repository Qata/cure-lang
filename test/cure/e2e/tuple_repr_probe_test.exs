defmodule Cure.E2E.TupleReprProbeTest do
  @moduledoc """
  Representability probes for the unified-tuple design (Tuple / Telescope /
  NonDep over a flat BEAM tuple — spec in progress). Each probe answers ONE
  question against the compiler AS IT IS: does the structure elaborate, emit,
  load, and RUN with the correct output on the host BEAM?

  This is a *map*, not a wishlist: the passing assertions pin what already works
  end-to-end; the `{:error, ...}`-pinned probes document the exact gaps (and will
  trip the moment a gap is closed, prompting the pin to flip to a success assert).

  Summary of findings (2026-07-09, merged autopilot/kernel-parity-batch):

    WORKS end-to-end (elaborate → emit → load → run):
      P1   dependent pair, arity-2 Sigma: construct, project .1, run
      P2a  nested-Sigma projection through annotated intermediates (.1 ; .2 then .1)
      P4   GADT indexed by INDUCTIVE VALUES (NonDep over Tele) — indices erased

    GAPS (what the design needs built):
      P2b  flat n-ary tuple %[a,b,c] (arity>2) => :unsupported_expression
             NEED: elaborator clause for non-binary tuple literals (checked+synth),
                   flat-BEAM-tuple emit, and .i projection (i>2) => element(i,t).
      P3   higher-order ctor field (A -> Tele) => parse error at `->`
             NEED: parse_ctor_dom to accept a parenthesized function-type domain
                   (the machinery already exists for type PARAMS like `b: (a)->Type`);
                   plus positivity/erasure for function-typed fields.
      P2a  DIRECT chained projection x.2.1 (no intermediate) => projection_not_a_record
             NEED: infer the inner projection's Sigma type so a 2nd projection fires.
      P5   Type-typed field as a runtime value Ext(Int,..) => :unknown_global
             BY DESIGN: Types are not first-class runtime values; keep `Tele` an
             erased ({0}) index, never reflected at runtime (P4 proves that path).

  Run: mix test test/cure/e2e/tuple_repr_probe_test.exs
  """
  use ExUnit.Case, async: false

  alias Cure.Elab.{Program, Emit}

  defp elab(src) do
    try do
      Program.elaborate(src)
    rescue
      e -> {:raise, Exception.message(e)}
    catch
      k, v -> {:raise, "#{inspect(k)}: #{inspect(v)}"}
    end
  end

  defp build(src, mod, fns) do
    case elab(src) do
      {:ok, env} ->
        try do
          Emit.compile_and_load(env, module: mod, functions: fns)
        rescue
          e -> {:raise, Exception.message(e)}
        catch
          k, v -> {:raise, "#{inspect(k)}: #{inspect(v)}"}
        end

      other ->
        other
    end
  end

  # ================= WORKS =================

  @p1 """
  mod P1
    type Nat = Zero | Suc(Nat)
    type Vector(a: Type) indices (n: Nat)
      empty : Vector(a, Zero)
      prepend : a -> Vector(a, n) -> Vector(a, Suc(n))
    fn twoVec() -> Sigma(n: Nat, Vector(Nat, n)) =
      %[Suc(Suc(Zero())), prepend(Zero(), prepend(Suc(Zero()), empty()))]
    fn theLen() -> Nat = twoVec().1
    fn start() -> Nat = theLen()
  """
  test "P1 dependent pair (arity-2 Sigma): construct, project .1, run" do
    assert {:ok, mod} = build(@p1, :"Cure.P1Probe", [:start, :theLen, :twoVec])
    # length of a 2-vector, projected out of a dependent pair, computed on the BEAM
    assert apply(mod, :start, []) == {:Suc, {:Suc, :Zero}}
  end

  @p2a1 """
  mod P2a1
    fn triple() -> Sigma(a: Int, Sigma(b: Int, Int)) = %[1, %[2, 3]]
    fn one()   -> Int = triple().1
    fn start() -> Int = one()
  """
  @p2a2 """
  mod P2a2
    fn triple() -> Sigma(a: Int, Sigma(b: Int, Int)) = %[1, %[2, 3]]
    fn inner() -> Sigma(b: Int, Int) = triple().2
    fn start() -> Int = inner().1
  """
  test "P2a nested-Sigma 3-tuple projects through annotated intermediates" do
    assert {:ok, m1} = build(@p2a1, :"Cure.P2a1Probe", [:triple, :one, :start])
    assert apply(m1, :one, []) == 1

    assert {:ok, m2} = build(@p2a2, :"Cure.P2a2Probe", [:triple, :inner, :start])
    assert apply(m2, :start, []) == 2
  end

  @p4 """
  mod P4
    type Tele indices ()
      Empty : Tele
      Ext : Type -> Tele -> Tele
    type NonDep indices (shape: Tele)
      NDEmpty : NonDep(Empty)
      NDExt : NonDep(rest) -> NonDep(Ext(A, rest))
    fn w0() -> NonDep(Empty) = NDEmpty()
    fn w1() -> NonDep(Ext(Int, Empty)) = NDExt(NDEmpty())
    fn start() -> NonDep(Ext(Int, Empty)) = w1()
  """
  test "P4 NonDep GADT indexed by Tele VALUES: builds, runs, indices erased" do
    assert {:ok, mod} = build(@p4, :"Cure.P4Probe", [:w0, :w1, :start])
    assert apply(mod, :w0, []) == :NDEmpty
    # NDExt emits {:NDExt, inner} — the A/rest Tele indices are erased, not carried
    assert apply(mod, :w1, []) == {:NDExt, :NDEmpty}
  end

  # ================= GAPS (pinned to current behavior) =================

  # GAP CLOSED (unified-tuple Increment 2): `%[1,2,3]` is now the flat `Tuple3`
  # family and emits a flat BEAM 3-tuple — no longer `:unsupported_expression`. It
  # is a DISTINCT type from the nested pair `Sigma(a:Int, Sigma(b:Int, Int))`
  # (`{1,{2,3}}`), so checking a flat-3 literal against the nested-pair type is a
  # type error, not a coincidental success.
  @p2b """
  mod P2b
    fn triple() -> Tuple(Int, Int, Int) = %[1, 2, 3]
  """
  test "P2b CLOSED: flat n-ary tuple %[1,2,3] elaborates and emits flat" do
    assert {:ok, mod} = build(@p2b, :"Cure.P2bProbe", [:triple])
    assert apply(mod, :triple, []) == {1, 2, 3}
  end

  @p2b_nested """
  mod P2bN
    fn triple() -> Sigma(a: Int, Sigma(b: Int, Int)) = %[1, 2, 3]
  """
  test "P2b distinctness: a flat-3 literal does NOT check against the nested pair" do
    assert {:error, _} = elab(@p2b_nested)
  end

  @p3 """
  mod P3
    type Tele indices ()
      Empty : Tele
      Ext : Type -> Tele -> Tele
      Dep : (A: Type) -> (A -> Tele) -> Tele
    fn dep() -> Tele = Dep(Int, fn(x) -> Empty())
    fn start() -> Tele = dep()
  """
  test "P3 GAP: higher-order ctor field (A -> Tele) fails to parse at the arrow" do
    assert {:error, errs} = elab(@p3)
    assert Enum.any?(errs, &match?({:expected, :rparen, :got, :arrow, _, _}, &1))
  end

  @p5 """
  mod P5
    type Tele indices ()
      Empty : Tele
      Ext : Type -> Tele -> Tele
    fn one() -> Tele = Ext(Int, Empty())
    fn start() -> Tele = one()
  """
  test "P5 BY-DESIGN: Type-typed field as a runtime value => :unknown_global" do
    # Types are not first-class runtime values; `Tele` must stay an erased index.
    assert {:error, :unknown_global} = build(@p5, :"Cure.P5Probe", [:one, :start])
  end
end
