defmodule Cure.Elab.CarriedIndexSiblingTest do
  @moduledoc """
  Phase 2 Step 3b — sibling refinement (the genuine carried equation).

  Step 3a refines each branch's GOAL to the constructor's computed result index
  via the motive (`match v` on `v : F(app(p,q))` gives goal `F(SNil())` in the
  `leaf` branch, `F(app(as,bs))` in `mk`). That is sound and needs no equation.

  But a SIBLING in the context — a second variable `w : F(app(p,q))` that is not
  the scrutinee — is NOT abstracted by the scrutinee's motive, so it keeps its
  original index. In the `leaf` branch the goal is refined to `F(SNil())` while
  `w` still has type `F(app(p,q))`; returning `w` there requires transporting it
  along the branch's stuck equation `app(p,q) = SNil()`. This is exactly Lean's
  opt-in `match h :` equation (`Match.lean:132-143`, gated on `hName?`): the
  equation reconciles the SCRUTINEE index against the branch index at the use
  site, a mechanism distinct from the motive goal refinement of 3a.

  RED until Step 3b carries `Eq(SList, app(p,q), <branch index>)` into the branch
  and transports index-mentioning siblings (capability-B Eq-arrow + `rewrite`,
  generalized value → index). The soundness control returns a sibling of the
  WRONG family index and must stay rejected.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @preamble """
    type SList = SNil | SCons(Nat, SList)
    fn app(xs: SList, ys: SList) -> SList = match xs
      SNil() -> ys
      SCons(h, t) -> SCons(h, app(t, ys))
    type F indices (xs: SList)
      leaf : F(SNil())
      mk : F(as) -> F(bs) -> F(app(as, bs))
    type G indices (xs: SList)
      gwrap : G(cs)
  """

  defp mod(body), do: "mod P\n  type Nat = Z | S(Nat)\n" <> @preamble <> body <> "end\n"

  test "returning a sibling in a refined branch needs the carried index eq (3b)" do
    # `w : F(app(p,q))` is a sibling, not the scrutinee. In the `leaf` branch the
    # 3a-refined goal is `F(SNil())`; `w : F(app(p,q))` type-checks there only if
    # `app(p,q) = SNil()` is carried and `w` transported. Same for the `mk` arm
    # (`app(p,q) = app(as,bs)`). RED until 3b.
    src =
      mod("""
        fn keep({p: SList}, {q: SList}, v: F(app(p, q)), w: F(app(p, q))) -> F(app(p, q)) =
          match v
            leaf() -> w
            mk(l, r) -> w
      """)

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "carried sibling eq does not admit a wrong-family sibling (soundness control)" do
    # `u : G(app(p,q))` DOES mention the carried index, so 3b transports it — in
    # the `leaf` branch to `G(SNil())`. But the goal there is `F(SNil())`, and
    # `G(SNil()) ≢ F(SNil())`: the transport fires yet the kernel still rejects on
    # the family mismatch. This exercises the transport path (not the 3a fallback)
    # and proves it does not launder an ill-typed result.
    src =
      mod("""
        fn bad({p: SList}, {q: SList}, v: F(app(p, q)), u: G(app(p, q))) -> F(app(p, q)) =
          match v
            leaf() -> u
            mk(l, r) -> u
      """)

    assert {:error, _} = Program.elaborate(src)
  end

  test "an unrelated-index sibling is not transported and stays rejected" do
    # `u : F(q)` does not mention `app(p,q)`, so 3b does not fire for it; the plain
    # 3a-refined goal (`F(SNil())` in `leaf`) rejects `u : F(q)`. Guards the
    # detection: a sibling on a different index must not be spuriously refined.
    src =
      mod("""
        fn bad({p: SList}, {q: SList}, v: F(app(p, q)), u: F(q)) -> F(app(p, q)) =
          match v
            leaf() -> u
            mk(l, r) -> u
      """)

    assert {:error, _} = Program.elaborate(src)
  end
end
