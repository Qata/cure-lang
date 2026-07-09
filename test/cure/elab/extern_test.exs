defmodule Cure.Elab.ExternTest do
  @moduledoc """
  `@extern(:mod, :fn, arity)` FFI in the dependent pipeline (Wave 3). A bodyless
  extern is a typed opaque postulate: its declared Π is asserted (an FFI axiom,
  not kernel-proven — see spec §4 Claim B), it stays an opaque neutral in the
  kernel, and emit lowers it to a direct Erlang remote call. Kernel untouched.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit, TotalityClosure}
  alias Cure.Core.Env

  test "a bodyless @extern declaration elaborates" do
    src = "mod M\n  @extern(:erlang, :length, 1)\n  fn length(xs: List(Int)) -> Int\nend\n"
    assert {:ok, _env} = Program.elaborate(src)
  end

  test "the elaborated extern retains its declared arrow type (signature not discarded)" do
    src = "mod M\n  @extern(:erlang, :length, 1)\n  fn length(xs: List(Int)) -> Int\nend\n"
    {:ok, env} = Program.elaborate(src)
    # The behavioral contract: a def named `length` exists with a Pi type whose
    # codomain is Int. Pin at least that the def is present and not {:hole,_}.
    def_entry = extern_def!(env, :length)
    refute match?({:hole, _}, Map.get(def_entry, :body))
    assert Map.get(def_entry, :type) != nil
  end

  test "TotalityClosure does not certify an extern reached from a type-level index" do
    # `extdec`'s call appears in constructor `mk`'s result index (mirroring the
    # `andd(d1, d2)`-in-result-index precedent in indexed_declarations_test.exs),
    # so seed_globals pulls it into the type-level closure. It is an extern with
    # no Core body to certify — certify_type_level must skip it, never hand its
    # sentinel to Kernel.check.
    src =
      "mod M\n" <>
        "  type Dec = Dcoupled | Causal\n" <>
        "  @extern(:erlang, :abs, 1)\n  fn extdec(x: Dec) -> Dec\n" <>
        "  type Boxed indices (d: Dec)\n" <>
        "    mk : Boxed(extdec(Causal))\n" <>
        "end\n"

    {:ok, env} = Program.elaborate(src)

    # Reachability (falsifiability): :extdec must actually be in the closure,
    # or this test would pass vacuously.
    assert MapSet.member?(TotalityClosure.type_level_fns(env), :extdec)

    # The mechanism: certify_type_level must succeed (not
    # {:error, {:totality_required, :extdec}}), because an extern is skipped.
    assert {:ok, _} = TotalityClosure.certify_type_level(env)
  end

  test "an @extern typechecks AND ships — issues the real remote call" do
    src = "mod M\n  @extern(:erlang, :length, 1)\n  fn length(xs: List(Int)) -> Int\nend\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Extern1", functions: [:length])
    assert apply(mod, :length, [[1, 2, 3]]) == 3
  end

  test "a 0-arity and a 2-arity extern both wire params correctly" do
    src =
      "mod M\n" <>
        "  @extern(:erlang, :max, 2)\n  fn imax(a: Int, b: Int) -> Int\n" <>
        "end\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Extern2", functions: [:imax])
    assert apply(mod, :imax, [3, 7]) == 7

    src0 = "mod M\n  @extern(:erlang, :time, 0)\n  fn now() -> Int\nend\n"
    {:ok, env0} = Program.elaborate(src0)
    {:ok, mod0} = Emit.compile_and_load(env0, module: :"Cure.Extern0", functions: [:now])
    # :erlang.time/0 returns a {H,M,S} tuple; just assert it runs and returns a value.
    assert apply(mod0, :now, []) != nil
  end

  test "an extern mixed with a normal dependent function — whole module elaborates + emits" do
    src =
      "mod M\n" <>
        "  @extern(:erlang, :length, 1)\n  fn length(xs: List(Int)) -> Int\n" <>
        "  fn double(n: Int) -> Int = n + n\n" <>
        "end\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Extern3", functions: [:length, :double])
    assert apply(mod, :length, [[1, 2]]) == 2
    assert apply(mod, :double, [21]) == 42
  end

  defp extern_def!(env, name), do: Env.get_def(env, name) || flunk("no def #{name}")
end
