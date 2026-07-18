defmodule Cure.Elab.ProofHoleResolutionTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # A LOCAL, UNTAGGED lemma. No @lemma anywhere → the argument-position hole
  # must REACH the resolver (proving it is no longer the raw
  # {:unsupported_expression,...} rejection of before), and the resolver DECLINES
  # (nothing tagged). Under first-class holes (Slice 1), a declined proof hole
  # does NOT abort elaboration: it SURVIVES as a stuck `{:hole, id}` neutral.
  # The enclosing `refine(...)` application evals to a stuck spine and the kernel
  # accepts the hole at the proof goal, so the program type-checks with an
  # inspectable hole that blocks codegen — mirroring a body-level hole, rather
  # than crashing the hole-blind evaluator (which no longer exists) or raising a
  # hard error. This proves resolution is gated on the tag AND that a declined
  # auto-proof is deferrable, not fatal.
  @red """
  mod RedUntagged
    use Std.Proof.Math
    use Std.Refine

    fn untagged_fact({left: Nat}, {right: Nat},
          lp: IsPositive(left), rp: IsPositive(right)) -> IsPositive(multiply(left, right)) =
      multiplying_positive_numbers_is_positive(lp, rp)

    fn demo(left: PositiveNatural, right: PositiveNatural) -> PositiveNatural =
      refine(multiply(refined_value(left), refined_value(right)), ?)
  end
  """

  # Recursively search an elaborated Core term for a surviving hole node.
  defp has_hole?({:hole, _id}), do: true
  defp has_hole?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&has_hole?/1)
  defp has_hole?(l) when is_list(l), do: Enum.any?(l, &has_hole?/1)
  defp has_hole?(m) when is_map(m), do: m |> Map.values() |> Enum.any?(&has_hole?/1)
  defp has_hole?(_), do: false

  test "an untagged proof hole is DECLINED and survives as a first-class hole" do
    assert {:ok, env} = Program.elaborate(@red)

    demo =
      env.defs
      |> Map.values()
      |> Enum.find(fn d -> to_string(d.name) |> String.ends_with?("demo") end)

    assert demo, "demo/2 must be elaborated"

    assert has_hole?(demo.body),
           "a declined proof hole must SURVIVE in the elaborated body, not vanish or error"

    # The surviving hole type-checks but must NOT be emittable: the codegen gate
    # refuses the whole program until the hole is filled.
    assert {:error, {:unfilled_hole, name}} = Program.check_codegen_ready(env)
    assert to_string(name) |> String.contains?("demo")
  end
end
