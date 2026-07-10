defmodule Cure.E2E.FlatTelescopeTest do
  @moduledoc """
  Flat n-ary telescope tuples (unified-tuple design, Option B). `Tuple(T1,…,Tn)`
  is the unit-terminated nested Σ `Sigma(T1, … Sigma(Tn, Unit))`; at CODEGEN it
  lowers to a FLAT BEAM tuple `{a,…,n}` (the `unit` terminator is the marker emit
  keys on, erased before runtime). Positional `.i` and telescope patterns also
  understand the flat lowering. Nesting is opt-in: `Tuple(A, Tuple(B,C))` → `{a,{b,c}}`.

  Every probe is end-to-end: elaborate → emit → load → run on the host BEAM.
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

  @flat3 """
  mod FlatT3
    fn t3() -> Tuple(Int, Int, Int) = %[1, 2, 3]
    fn start() -> Tuple(Int, Int, Int) = t3()
  """
  test "arity-3 telescope value lowers to a FLAT BEAM tuple {1,2,3}" do
    assert {:ok, mod} = build(@flat3, :"Cure.FlatT3", [:t3, :start])
    assert apply(mod, :t3, []) == {1, 2, 3}
  end

  @flat2 """
  mod FlatT2
    fn t2() -> Tuple(Int, Int) = %[1, 2]
    fn start() -> Tuple(Int, Int) = t2()
  """
  test "arity-2 telescope value lowers to a FLAT BEAM tuple {1,2}" do
    assert {:ok, mod} = build(@flat2, :"Cure.FlatT2", [:t2, :start])
    assert apply(mod, :t2, []) == {1, 2}
  end

  @nested """
  mod NestedT
    fn t() -> Tuple(Int, Tuple(Int, Int)) = %[1, %[2, 3]]
    fn start() -> Tuple(Int, Tuple(Int, Int)) = t()
  """
  test "opt-in nesting Tuple(A, Tuple(B,C)) lowers to {a, {b,c}}" do
    assert {:ok, mod} = build(@nested, :"Cure.NestedT", [:t, :start])
    assert apply(mod, :t, []) == {1, {2, 3}}
  end

end
