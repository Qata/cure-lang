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

  # Identical to @red but the local lemma is TAGGED @lemma. Now the hole must be
  # discharged automatically: sub-goals IsPositive(refined_value(left/right))
  # come from the refinement projections of the two PositiveNatural binders.
  #
  # CRITICAL: @green and @reference use the SAME module name (`TaggedDemo`).
  # Global def names are module-qualified, so the LOCAL lemma `tagged_fact` would
  # resolve to a DIFFERENT global atom in each program if the two modules had
  # different names — making `demo_body(green_env) == demo_body(ref_env)`
  # structurally false no matter how correct ProofSearch is. Each `elaborate`
  # builds an independent Env from scratch, so reusing the name is safe.
  @green """
  mod TaggedDemo
    use Std.Proof.Math
    use Std.Refine

    @lemma
    fn tagged_fact({left: Nat}, {right: Nat},
          lp: IsPositive(left), rp: IsPositive(right)) -> IsPositive(multiply(left, right)) =
      multiplying_positive_numbers_is_positive(lp, rp)

    fn demo(left: PositiveNatural, right: PositiveNatural) -> PositiveNatural =
      refine(multiply(refined_value(left), refined_value(right)), ?)
  end
  """

  # Same program, same module name, but the proof is written BY HAND (no hole).
  # Its `demo` body is the reference the resolved term must equal.
  @reference """
  mod TaggedDemo
    use Std.Proof.Math
    use Std.Refine

    @lemma
    fn tagged_fact({left: Nat}, {right: Nat},
          lp: IsPositive(left), rp: IsPositive(right)) -> IsPositive(multiply(left, right)) =
      multiplying_positive_numbers_is_positive(lp, rp)

    fn demo(left: PositiveNatural, right: PositiveNatural) -> PositiveNatural =
      refine(multiply(refined_value(left), refined_value(right)),
             tagged_fact(refinement_proof(left), refinement_proof(right)))
  end
  """

  defp demo_body(env) do
    {_name, %{body: body}} =
      Enum.find(env.defs, fn {name, _} -> Atom.to_string(name) |> String.ends_with?("demo") end)

    body
  end

  test "tagging the lemma discharges the hole and the program passes the codegen gate" do
    assert {:ok, env} = Program.elaborate(@green)
    assert :ok = Program.check_codegen_ready(env)
  end

  test "the found proof term equals the hand-written proof term (same-run differential)" do
    {:ok, green_env} = Program.elaborate(@green)
    {:ok, ref_env} = Program.elaborate(@reference)

    assert demo_body(green_env) == demo_body(ref_env)
  end
end
