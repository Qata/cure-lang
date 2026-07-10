defmodule Antigen.PrimitiveSeedAntibodyTest do
  @moduledoc """
  TCB antibody — seeding the primitive name→node floor (spec 2026-07-10-
  primitive-type-declarations) is INERT with respect to the kernel. It adds a
  surface-resolution table only; it introduces no Core node (the three nodes
  predate it, gated by the #2/#3 batch) and changes no kernel judgement.

  Two properties:
    * EXACTLY-THREE-CANONICAL — the seeded floor is precisely {Int→int_type,
      Float→float_type, Binary→binary_type}: no extra bindings, each mapping to
      the already-gated canonical node. A drifted binding would silently
      repoint a base type.
    * KERNEL-INERT — inference/conversion on the three primitive nodes is
      identical whether or not the primitives floor is present. The floor is a
      resolution convenience, never consulted by the TCB.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Conv, Env, Kernel}

  test "EXACTLY-THREE-CANONICAL: the floor is precisely the three canonical bindings" do
    env = Builtins.seed(Env.empty())

    assert Env.primitive(env, "Int") == {:int_type}
    assert Env.primitive(env, "Float") == {:float_type}
    assert Env.primitive(env, "Binary") == {:binary_type}
    assert map_size(env.primitives) == 3
  end

  test "KERNEL-INERT: primitive-node judgements ignore the floor" do
    with_floor = Builtins.seed(Env.empty())
    without = %{with_floor | primitives: %{}}

    for node <- [{:int_type}, {:float_type}, {:binary_type}] do
      assert Kernel.infer(Context.empty(with_floor), node) ==
               Kernel.infer(Context.empty(without), node),
             "kernel inference on #{inspect(node)} must not depend on the primitives floor"
    end

    # The three nodes stay mutually non-convertible either way (no floor-induced collapse).
    refute Conv.conv?({:int_type}, {:binary_type}, [], 0, with_floor)
    refute Conv.conv?({:float_type}, {:binary_type}, [], 0, with_floor)
  end
end
