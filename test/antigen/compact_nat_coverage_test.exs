defmodule Antigen.CompactNatCoverageTest do
  # Coverage-manifest antibody for the compact-Nat / K2 builtin-op-fold TCB batch
  # (spec 2026-07-09): after that change, kernel line coverage fell from ~97% to
  # 90.2% because the campaign never exercised the compact-literal peel path
  # (`Eval.nat_to_ctor/1`, `nat_to_ctor_if/1`), the nat_lit index-unification
  # bridge (`Kernel.nat_lit_ctor/1`, `rigid_index?`'s nat_lit clause), the
  # `bool_type_value`/`nat_type_value` builtin-type-value readers, or the
  # `struct_eq`/`struct_ne` builtin-op-fold arm (`Normalise.builtin_op_fold/4`).
  # This test proves each of those exact lines is now reached by the real
  # generators (`DepMatch.compact_nat_probes/0`, `Primitive.gen/0`'s new
  # struct_eq/struct_ne shapes, `ElabLiteralTyping.challenges/0`), run through
  # their real assays under `:cover`.
  #
  # `:cover` is node-wide global state, so — like `Antigen.CoverTest` — this
  # suite runs synchronously (`async: false`).
  use ExUnit.Case, async: false

  alias Antigen.{Cover, Runner}
  alias Antigen.Generators.{DepMatch, Primitive, ElabLiteralTyping}
  alias Antigen.Backend.StreamData, as: B

  @eval_targets [168, 169, 175]
  @kernel_targets [1115, 1122, 1123, 1257, 1258, 1268, 1269]
  @normalise_targets [333, 335, 336, 355]

  # Run every challenge through its registered assay (pure — no corpus/seed I/O).
  defp run_all(challenges) do
    for c <- challenges do
      mod = Runner.assay_module_for(c.assay)
      mod.run(c)
    end
  end

  test "the exact compact-Nat / builtin-op-fold cold lines are now covered" do
    cov =
      Cover.with_cover(Cover.cover_modules(), fn ->
        # -- Eval.nat_to_ctor / nat_to_ctor_if + Kernel.nat_lit_ctor /
        # rigid_index?'s nat_lit clause — deterministic DepMatch probes.
        run_all(DepMatch.compact_nat_probes())

        # -- Kernel.bool_type_value / nat_type_value — elaborator-driven literal
        # typing catalog (both assays, deterministic).
        run_all(ElabLiteralTyping.challenges())

        # -- Normalise.builtin_op_fold's struct_eq/struct_ne arm (saturated fold,
        # line 336) and the wrong-arity catch-all (partial application, line
        # 355) — sample Primitive.gen/0 broadly; struct_eq/struct_ne carry
        # frequency weight 5/19 combined, so 400 draws hits all shapes with
        # overwhelming probability.
        run_all(B.interp(Primitive.gen()) |> Enum.take(400))

        Map.new(
          [Cure.Core.Eval, Cure.Core.Kernel, Cure.Core.Normalise],
          fn m -> {m, Cover.line_coverage(m)} end
        )
      end)

    assert Enum.all?(@eval_targets, &(&1 in cov[Cure.Core.Eval].covered)),
           "Eval cold: #{inspect(@eval_targets -- cov[Cure.Core.Eval].covered)}"

    assert Enum.all?(@kernel_targets, &(&1 in cov[Cure.Core.Kernel].covered)),
           "Kernel cold: #{inspect(@kernel_targets -- cov[Cure.Core.Kernel].covered)}"

    assert Enum.all?(@normalise_targets, &(&1 in cov[Cure.Core.Normalise].covered)),
           "Normalise cold: #{inspect(@normalise_targets -- cov[Cure.Core.Normalise].covered)}"
  end
end
