defmodule Cure.Elab.ErasureRelevanceTest do
  @moduledoc """
  The `{0,ω}` relevance CHECK (M8.3) — the piece that makes erasure *sound*.

  Cure already MARKS binders (implicit `{n: Nat}` fn params and GADT index args
  get quantity `:erased`; `declarations.ex:173`, `erasure_marking_test.exs`) and
  already ERASES them (`erase.ex` drops erased ctor args + erased global-app-spine
  args). What is MISSING is the check that an *erased* binder is never used in a
  runtime-RELEVANT position — without it, `fn f({n: Nat}, v: NV(n)) -> Nat = n`
  type-checks, then erasure drops the `n` slot the body still returns, so the
  emitted BEAM function references a dropped binding. This file characterizes
  that hole (red), pinning the exact error shape A2's `Relevance.check` must emit.

  ## Idris 0/ω grounding (Core/LinearCheck.idr, ω-except-erased slice ONLY)

  Re-read from source (`~/Develop/esp32-beam/reference/idris2/src/Core/LinearCheck.idr`)
  at the top of this task. `lcheck rig erase env term` threads a usage count; a
  binder declared `Rig0` (our `:erased`) must have usage 0 in every RELEVANT
  position. The multiplier is `checkRig = rigf |*| rig` (App case, :288), and
  `erased |*| _ = erased`, so:

    * RELEVANT for a `0` binder (usage counts → violation):
      - RETURNED as the value (the term IS the binder);
      - passed in a `ω` / `:present` argument position (`rigf` present → `checkRig`
        stays `rig`);
      - SCRUTINISED (case discriminant is checked at the ambient `rig`);
      - APPLIED as a function head.
    * EXEMPT (checked at `erased`, usage does NOT count):
      - type / index positions — Pi & Sigma DOMAINS are checked `erased` when the
        binder is inspectable-only (`rig` local, :265-272); the motive likewise;
      - erased ARGUMENT positions (`rigf` erased → `checkRig` erased, :288);
      - `Eq` / proof positions — `Refl`'s argument is `Rig0`; Cure erases
        `{:refl, _}` to `{:ctor, :cure_refl, []}` (arg dropped, `erase.ex:63`),
        so proof-position use is genuinely runtime-free.

  We port the 0/ω slice only (per the manifest caveat: read Idris core as
  ω-except-erased; the linear `1` multiplicity is deliberately out of scope).

  RED STATUS (this commit): probes (a)–(c) currently elaborate `{:ok, _}` — the
  hole. Controls (d)–(e) already pass and must STAY green through A2.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # Nat, the singleton family SNat(n), the indexed family NV(n) (so `v : NV(n)`
  # makes `n` genuinely occur only in a TYPE position in the signature), plus the
  # reflection helpers. Identical shape to value_in_goal_match_test's preamble.
  @preamble """
    type Nat = Z | S(Nat)
    type SNat indices (n: Nat)
      szero : SNat(Z)
      ssuc : SNat(n) -> SNat(S(n))
    type NV indices (n: Nat)
      vz : NV(Z)
      vs : SNat(n) -> NV(S(n))
    fn toS(m: Nat) -> SNat(m) = match m
      Z() -> szero()
      S(j) -> ssuc(toS(j))
  """
  defp mod(b), do: "mod P\n" <> @preamble <> b <> "end\n"

  describe "erased implicit used relevantly — must be rejected (M8.3 hole)" do
    test "(a) body RETURNS the erased implicit `n`" do
      # `n : Nat` is an erased implicit; the body returns it. Erasure will drop
      # the `n` slot, so the emitted function returns a dropped binding.
      src =
        mod("""
          fn f({n: Nat}, v: NV(n)) -> Nat = n
        """)

      assert {:error, {:erased_used_relevantly, _}} = Program.elaborate(src)
    end

    test "(b) erased implicit `n` passed in a PRESENT argument position" do
      # `g` takes a runtime-relevant `Nat`; passing the erased `n` into it is a
      # relevant use even though `n` is never syntactically returned.
      src =
        mod("""
          fn g(m: Nat) -> Nat = m
          fn f({n: Nat}, v: NV(n)) -> Nat = g(n)
        """)

      assert {:error, {:erased_used_relevantly, _}} = Program.elaborate(src)
    end

    test "(c) body SCRUTINISES the erased implicit `n`" do
      # Matching on `n` forces its runtime value — a relevant use.
      src =
        mod("""
          fn f({n: Nat}, v: NV(n)) -> Nat =
            match n
              Z() -> Z()
              S(k) -> Z()
        """)

      assert {:error, {:erased_used_relevantly, _}} = Program.elaborate(src)
    end
  end

  describe "erased implicit used only irrelevantly — must be accepted (controls)" do
    test "(d) erased implicit used only in a TYPE/index position" do
      # `n` appears only inside the types `NV(n)` (param and result); the body
      # returns the runtime-relevant `v`. This is the whole point of erasure and
      # must accept before AND after the check.
      src =
        mod("""
          fn f({n: Nat}, v: NV(n)) -> NV(n) = v
        """)

      assert {:ok, _} = Program.elaborate(src)
    end

    test "(e) erased implicit used only inside an Eq/proof position" do
      # `n` occurs in the return TYPE `Eq(Nat, n, n)` (type position) and inside
      # `refl(n)` (a proof term; `refl`'s argument is erased — `erase.ex:63`
      # drops it to `cure_refl`). No relevant use, so it must accept before AND
      # after the check.
      src =
        mod("""
          fn f({n: Nat}, v: NV(n)) -> Eq(Nat, n, n) = refl(n)
        """)

      assert {:ok, _} = Program.elaborate(src)
    end
  end

end
