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
  # async: false — the seam tests below load a BEAM module (Emit.compile_and_load),
  # which mutates global VM state, so this module must not run concurrently.
  use ExUnit.Case, async: false
  alias Cure.Elab.{Program, Erase, Emit}
  alias Cure.Core.Env

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
      # `n` occurs in the return TYPE `Equivalent(Nat, n, n)` (type position) and inside
      # `reflexive(n)` (a proof term; `refl`'s argument is erased — `erase.ex:63`
      # drops it to `cure_refl`). No relevant use, so it must accept before AND
      # after the check.
      src =
        mod("""
          fn f({n: Nat}, v: NV(n)) -> Equivalent(Nat, n, n) = reflexive(n)
        """)

      assert {:ok, _} = Program.elaborate(src)
    end
  end

  # --- A3: erasure-seam consistency pins ---------------------------------------
  # These pin behaviours that are currently only implementation accidents, so a
  # future refactor cannot silently break the erasure story.

  describe "seam: erased constructor fields are unnameable" do
    @seam_pre """
    mod P
      type Nat = Z | S(Nat)
      type SNat indices (n: Nat)
        szero : SNat(Z)
        ssuc : SNat(n) -> SNat(S(n))
      type NV indices (n: Nat)
        vz : NV(Z)
        vs : SNat(n) -> NV(S(n))
    """

    test "naming the erased index of a matched constructor is an error, not a silent bind" do
      # `vs : SNat(n) -> NV(S(n))` has quantities [:erased (n), :present (SNat)].
      # In `vs(s)` the surface var `s` names the PRESENT field; the erased index
      # `n` gets the unnameable placeholder `"_erased"` (elaborator `branch_scope`).
      # Referencing `n` in the body must NOT resolve to the erased slot — it is
      # simply unbound.
      src = @seam_pre <> "  fn f(v: NV(S(Z))) -> Nat =\n    match v\n      vs(s) -> n\nend\n"
      assert {:error, _} = Program.elaborate(src)
    end

    test "the present field of the same constructor IS nameable (contrast)" do
      src = @seam_pre <> "  fn f(v: NV(S(Z))) -> NV(S(Z)) =\n    match v\n      vs(s) -> vs(s)\nend\n"
      assert {:ok, _} = Program.elaborate(src)
    end
  end

  describe "seam: erased params give consistent emitted head/call-site arities" do
    @arity_src """
    type Dec = Dcoupled | Causal
    type Sig = CSig | ESig
    type SVDesc = SVNil | SVCons(Sig, SVDesc)
    fn andd(x: Dec, y: Dec) -> Dec = x
    type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
      prim : SF(as, bs, Causal)
      seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
    fn compose({as: SVDesc}, {bs: SVDesc}, {cs: SVDesc}, {d1: Dec}, {d2: Dec}, l: SF(as, bs, d1), r: SF(bs, cs, d2)) -> SF(as, cs, andd(d1, d2)) = seq(l, r)
    fn compose3({as: SVDesc}, {bs: SVDesc}, {cs: SVDesc}, {ds: SVDesc}, {d1: Dec}, {d2: Dec}, {d3: Dec}, x: SF(as, bs, d1), y: SF(bs, cs, d2), z: SF(cs, ds, d3)) -> SF(as, ds, andd(andd(d1, d2), d3)) = compose(compose(x, y), z)
    """

    test "erased params drop from the emitted head, and call sites agree end-to-end" do
      {:ok, env} = Program.elaborate(@arity_src)

      arities =
        env
        |> Emit.module_forms(:"Cure.ErasureSeam.Arity", [:compose, :compose3])
        |> Enum.flat_map(fn
          {:function, _, name, arity, _} -> [{name, arity}]
          _ -> []
        end)
        |> Map.new()

      # compose: 5 erased indices + 2 present ⇒ arity 2; compose3: 7 erased + 3 ⇒ 3.
      assert arities[:compose] == 2
      assert arities[:compose3] == 3

      {:ok, mod} =
        Emit.compile_and_load(env,
          module: :"Cure.ErasureSeam.Arity",
          functions: [:compose, :compose3]
        )

      # compose3's body is `compose(compose(x, y), z)`: the emitted call sites pass
      # exactly 2 args to the emitted `compose/2`. A head/call-site arity mismatch
      # would crash `undef` here — a successful nested build IS the arity pin.
      assert apply(mod, :compose3, [:prim, :prim, :prim]) ==
               {:seq, {:seq, :prim, :prim}, :prim}
    end
  end

  describe "seam: proofs are erased (proof irrelevance)" do
    test "two different rewrite proofs erase to the same runtime term" do
      env = Env.empty()
      body = {:ctor, :Causal, []}
      motive = {:lam, {:type, 0}, body}
      r1 = {:rewrite, {:refl, {:ctor, :Dcoupled, []}}, motive, body}
      r2 = {:rewrite, {:refl, {:ctor, :Causal, []}}, motive, body}

      # `rewrite proof motive body ⇝ body` at erase (erase.ex): the proof is
      # dropped, so swapping it changes nothing observable at runtime.
      assert Erase.erase(env, r1) == Erase.erase(env, r2)
      assert Erase.erase(env, r1) == Erase.erase(env, body)
    end

    test "refl and Eq values erase to nullary runtime placeholders" do
      env = Env.empty()
      assert Erase.erase(env, {:refl, {:ctor, :Dcoupled, []}}) == {:ctor, :cure_refl, []}

      assert Erase.erase(env, {:eq, {:data, :Dec, [], []}, {:ctor, :Causal, []}, {:ctor, :Causal, []}}) ==
               {:ctor, :cure_eq, []}
    end
  end
end
