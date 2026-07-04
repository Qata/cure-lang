defmodule Cure.Compiler.DependentVecCodegenTest do
  @moduledoc """
  End-to-end Cure-language coverage for the currently supported length-indexed
  vector fragment: parse real `.cure` source, elaborate through the dependent
  kernel, erase indices, emit BEAM, and execute the result.
  """
  use ExUnit.Case, async: false

  @src """
  mod VecCg
    type Nat = Z | S(Nat)
    type Vector(a: Type) indices (n: Nat)
      empty : Vector(a, Z)
      prepend : a -> Vector(a, n) -> Vector(a, S(n))
    fn plus(m: Nat, n: Nat) -> Nat = match m
      Z() -> n
      S(k) -> S(plus(k, n))
    fn append({a: Type}, {m: Nat}, {n: Nat}, xs: Vector(a, m), ys: Vector(a, n)) -> Vector(a, plus(m, n)) = match xs
      empty() -> ys
      prepend(x, rest) -> prepend(x, append(rest, ys))
  end
  """

  @stdlib_src File.read!("lib/std/vector.cure")
  @nat_src File.read!("lib/std/nat.cure")

  test "length-indexed Vector append compiles and runs after erasure" do
    assert {:ok, mod} = Cure.Compiler.compile_and_load(@src, emit_events: false)
    assert mod == :"Cure.VecCg"

    xs = {:prepend, 1, {:prepend, 2, :empty}}
    ys = {:prepend, 3, :empty}

    assert apply(mod, :plus, [:Z, {:S, :Z}]) == {:S, :Z}
    assert apply(mod, :plus, [{:S, :Z}, {:S, :Z}]) == {:S, {:S, :Z}}
    assert apply(mod, :append, [:empty, ys]) == ys
    assert apply(mod, :append, [xs, ys]) == {:prepend, 1, {:prepend, 2, {:prepend, 3, :empty}}}
  end

  test "bad Vector append is rejected through the real compiler path" do
    bad =
      String.replace(
        @src,
        "prepend(x, rest) -> prepend(x, append(rest, ys))",
        "prepend(x, rest) -> rest"
      )

    assert {:error, _reason} = Cure.Compiler.compile_and_load(bad, emit_events: false)
  end

  test "Std.Vector is the length-indexed Vector module and runs after erasure" do
    assert {:ok, nat} =
             Cure.Compiler.compile_and_load(@nat_src,
               file: "lib/std/nat.cure",
               emit_events: false
             )

    assert nat == :"Cure.Std.Nat"
    assert function_exported?(nat, :plus, 2)

    assert {:ok, mod} =
             Cure.Compiler.compile_and_load(@stdlib_src,
               file: "lib/std/vector.cure",
               emit_events: false
             )

    assert mod == :"Cure.Std.Vector"
    refute function_exported?(mod, :plus, 2)

    xs = {:prepend, 1, {:prepend, 2, :empty}}
    ys = {:prepend, 3, :empty}

    assert apply(mod, :append, [:empty, ys]) == ys
    assert apply(mod, :append, [xs, ys]) == {:prepend, 1, {:prepend, 2, {:prepend, 3, :empty}}}
  end
end
