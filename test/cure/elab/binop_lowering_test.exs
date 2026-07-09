defmodule Cure.Elab.BinopLoweringTest do
  @moduledoc """
  K2 Phase 2 (spec 2026-07-09-prim-delta-globals + Amendment A1 §1-A): surface
  arithmetic/comparison operators lower to registry-keyed builtin-op GLOBAL
  spines, not `{:prim, op, args}` nodes. Type-directed 4-way `==`/`!=` dispatch:
  Bool → Std.Bool eq/ne (unchanged), Int → int_eq/int_ne, Float →
  float_eq/float_ne, other (ADT/neutral) → struct_eq/struct_ne applied to the
  quoted operand type (A1 — NOT an error; today's structural semantics verbatim).
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Env}
  alias Cure.Elab.{Emit, Program}

  defp seeded, do: Builtins.seed(Env.empty())

  @int2 {:pi, {:int_type}, {:pi, {:int_type}, {:int_type}}}

  # Body of a top-level fn `name`.
  defp body(src, name) do
    {:ok, env} = Program.elaborate("mod M\n  use Std.Bool\n" <> src <> "end\n")
    env.defs[name].body
  end

  defp app2(g, a, b), do: {:app, {:app, {:global, g}, a}, b}
  defp app3(g, ty, a, b), do: {:app, app2(g, ty, a), b}

  # No {:prim, _, _} node anywhere in the term.
  defp no_prim?(t) when is_tuple(t) do
    case t do
      {:prim, _, _} -> false
      _ -> t |> Tuple.to_list() |> Enum.all?(&no_prim?/1)
    end
  end

  defp no_prim?(l) when is_list(l), do: Enum.all?(l, &no_prim?/1)
  defp no_prim?(_), do: true

  test "Int `+` lowers to an int_add global spine, no prim" do
    b = body("  fn f(x: Int) -> Int = x + 1\n", :f)
    assert {:lam, {:int_type}, app2(:int_add, {:var, 0}, {:int_lit, 1})} == b
    assert no_prim?(b)
  end

  test "Float `+` lowers to float_add" do
    b = body("  fn g(x: Float) -> Float = x + 1.0\n", :g)
    assert {:lam, {:float_type}, app2(:float_add, {:var, 0}, {:float_lit, 1.0})} == b
    assert no_prim?(b)
  end

  test "Int `==` lowers to int_eq (guard-position shape)" do
    b = body("  fn eq0(n: Int) -> Bool = n == 0\n", :eq0)
    assert {:lam, {:int_type}, app2(:int_eq, {:var, 0}, {:int_lit, 0})} == b
    assert no_prim?(b)
  end

  test "Int `!=` lowers to int_ne; Float `==` to float_eq" do
    assert {:lam, {:int_type}, app2(:int_ne, {:var, 0}, {:int_lit, 3})} ==
             body("  fn t(n: Int) -> Bool = n != 3\n", :t)

    assert {:lam, {:float_type}, app2(:float_eq, {:var, 0}, {:float_lit, 2.0})} ==
             body("  fn u(x: Float) -> Bool = x == 2.0\n", :u)
  end

  test "A1: ADT `==` lowers to struct_eq applied to the quoted operand type (not prim, not error)" do
    b = body("  fn t(a: Nat, b: Nat) -> Bool = a == b\n", :t)

    assert {:lam, {:data, :Nat, [], []},
            {:lam, {:data, :Nat, [], []},
             app3(:struct_eq, {:data, :Nat, [], []}, {:var, 1}, {:var, 0})}} == b

    assert no_prim?(b)
  end

  test "A1: ADT `!=` lowers to struct_ne" do
    b = body("  fn t(a: Nat, b: Nat) -> Bool = a != b\n", :t)

    assert {:lam, {:data, :Nat, [], []},
            {:lam, {:data, :Nat, [], []},
             app3(:struct_ne, {:data, :Nat, [], []}, {:var, 1}, {:var, 0})}} == b
  end

  test "non-numeric arithmetic still rejects (unchanged from decision 3)" do
    assert {:error, _} =
             Program.elaborate("mod M\n  use Std.Bool\n  fn t(a: Nat, b: Nat) -> Nat = a + b\nend\n")
  end

  describe "emit: first-class builtin-op globals (core-level, spec §1.5 b/c)" do
    # Surface Cure cannot name `int_add` as a value, so the bare-reference and
    # partial-spine emit paths are reachable only from hand-built Core: a lambda
    # applied to the bare global (closure application is curried, one arg at a
    # time), and to a 1-arg partial spine. Pre-retarget the generic global path
    # emits a call to a nonexistent `int_add/0` — compile error (the red).
    test "bare builtin-op global as a value runs via a curried wrapper" do
      body =
        {:app, {:lam, @int2, {:app, {:app, {:var, 0}, {:int_lit, 3}}, {:int_lit, 4}}},
         {:global, :int_add}}

      env = Env.add_def(seeded(), :use_bare, {:int_type}, body, [])
      {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.BopBare", functions: [:use_bare])
      assert apply(mod, :use_bare, []) == 7
    end

    test "1-arg PARTIAL builtin-op spine runs via wrapper + curried application" do
      body =
        {:app, {:lam, {:pi, {:int_type}, {:int_type}}, {:app, {:var, 0}, {:int_lit, 4}}},
         {:app, {:global, :int_add}, {:int_lit, 3}}}

      env = Env.add_def(seeded(), :use_partial, {:int_type}, body, [])

      {:ok, mod} =
        Emit.compile_and_load(env, module: :"Cure.BopPartial", functions: [:use_partial])

      assert apply(mod, :use_partial, []) == 7
    end
  end
end
