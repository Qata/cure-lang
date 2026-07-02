defmodule Antigen.ElabCompletenessTest do
  @moduledoc """
  Tests for the elaborator completeness + metamorphic vertical. These test the
  VERTICAL (the assay discriminates correctly, challenges are construction-well-
  typed), not that the elaborator is bug-free. The blast-radius survey at the
  bottom is a reporting probe, not a pass/fail gate on the elaborator.
  """
  use ExUnit.Case, async: true

  alias Antigen.Assays.Elab
  alias Antigen.Challenge
  alias Antigen.Generators.ElabComplete
  alias Cure.Elab.Program

  describe "assay discrimination (red-green of the vertical itself)" do
    test "completeness assay is :ok on an accepted well-typed program" do
      src = ElabComplete.source("idx_only/var/rebuild")
      # sanity: this control program really does elaborate today
      assert {:ok, _} = Program.elaborate(src)

      c = Challenge.new(kind: :elab_program, assay: "elab/completeness", label: :well_typed,
                        payload: %{id: "control", src: src})
      assert :ok = Elab.run(c)
    end

    test "completeness assay reports an infection on a rejected well-typed program" do
      # A construction-guaranteed well-typed program the elaborator wrongly
      # rejects is an infection: {:rejected_well_typed, id, _}. (This asserts the
      # assay FIRES on a reject — independent of which shape currently triggers.)
      bad_src = """
      mod P
        type Nat = Z | S(Nat)
        type NV indices (n: Nat)
          vz : NV(Z)
          vs : NV(n) -> NV(S(n))
        fn f({n: Nat}, v: NV(n)) -> Eq(NV(n), v, v) =
          match v
            vz() -> refl(vz())
            vs(s) -> refl(vs(s))
      end
      """

      c = Challenge.new(kind: :elab_program, assay: "elab/completeness", label: :well_typed,
                        payload: %{id: "known_reject", src: bad_src})

      assert {:violation, {:rejected_well_typed, "known_reject", _}} = Elab.run(c)
    end

    test "metamorphic assay is :ok when base and variant agree, fires when they diverge" do
      src = ElabComplete.source("idx_only/var/rebuild")

      agree = Challenge.new(kind: :elab_program, assay: "elab/metamorphic", label: :none,
                            payload: %{id: "x", transform: "identity", base_src: src, variant_src: src})
      assert :ok = Elab.run(agree)

      # Force a divergence: an accepting base vs a deliberately broken variant.
      broken = String.replace(src, "match v", "match nonexistent_var")
      diverge = Challenge.new(kind: :elab_program, assay: "elab/metamorphic", label: :none,
                              payload: %{id: "x", transform: "break", base_src: src, variant_src: broken})
      assert {:violation, {:verdict_not_invariant, "x", "break", _}} = Elab.run(diverge)
    end
  end

  describe "corpus round-trip (serialization parity)" do
    test "an :elab_program challenge survives to_pieces/from_pieces" do
      [c | _] = ElabComplete.completeness_challenges()
      {scaffold, pieces} = Challenge.to_pieces(c)
      back = Challenge.from_pieces(:elab_program, c.assay, c.label, c.seed, c.note, scaffold, pieces)
      assert back.payload == c.payload
      assert back.assay == c.assay
    end
  end

  describe "blast-radius survey (reporting probe, not a gate)" do
    test "map which construction-well-typed goal shapes the elaborator accepts vs rejects" do
      results =
        ElabComplete.completeness_challenges()
        |> Enum.map(fn c ->
          {c.payload.id, Elab.run(c)}
        end)

      IO.puts("\n=== ELABORATOR COMPLETENESS BLAST RADIUS ===")

      Enum.each(results, fn {id, verdict} ->
        tag = if verdict == :ok, do: "ACCEPT ✓", else: "REJECT ✗ (infection)"
        IO.puts("  #{String.pad_trailing(id, 32)} #{tag}")

        case verdict do
          {:violation, {:rejected_well_typed, _, e}} -> IO.puts("      └─ #{inspect(e)}")
          _ -> :ok
        end
      end)

      infections = Enum.reject(results, fn {_id, v} -> v == :ok end)
      IO.puts("  total: #{length(results)} shapes, #{length(infections)} infection(s)\n")

      # Anchor: the index-only control MUST elaborate — if even that regresses,
      # the vertical is mis-built (not a real blast-radius signal).
      assert {"idx_only/var/rebuild", :ok} in results
      # And the computed-INDEX (3a) shape must stay accepted: it isolates that the
      # blast radius is scrutinee-VALUE-in-goal, not computed indices per se.
      assert {"computed_idx/rebuild", :ok} in results
    end
  end

  describe "metamorphic invariance gate (real property — holds today)" do
    test "every catalog base has an invariant verdict under all typing-preserving transforms" do
      violations =
        ElabComplete.metamorphic_challenges()
        |> Enum.map(fn c -> {c.payload.id, c.payload.transform, Elab.run(c)} end)
        |> Enum.reject(fn {_id, _t, v} -> v == :ok end)

      assert violations == [],
             "metamorphic verdict flipped (de Bruijn / binder-framing bug):\n" <>
               Enum.map_join(violations, "\n", &inspect/1)
    end
  end
end
