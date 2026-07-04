defmodule Antigen.EqInductiveAntibodyTest do
  @moduledoc """
  TCB antibody — retiring the faking-era primitive identity type in favour of a
  genuine inductive `Eq` (spec 2026-07-04-identity-type-as-inductive) keeps the
  kernel SOUND and TERMINATING.

  Guards the coordinated change that seeds `Eq : (a:Type) -> a -> a -> Type` with
  the single erased-witness constructor `refl : {w:a} -> Eq(a,w,w)` as an ordinary
  builtin inductive, retargets surface `Eq`/`refl`, and WIDENS the two rewrite
  transport consumers — `Cure.Core.Kernel.ensure_eq/1` and the elaborator's
  `eq_parts/1` — to accept the inductive `{:vdata, :Eq, [ty, a, b]}` value
  alongside the retiring primitive `{:veq, ty, a, b}`.

  Two load-bearing soundness properties, each pinned with an INDEPENDENT oracle
  that never consults the machinery under test:

    * REFL-IS-REFLEXIVE — a `refl` proof inhabits `Eq(ty, x, y)` **iff** `x` and
      `y` are convertible. The independent oracle is `Cure.Core.Conv.conv_within?`
      (deep conversion, no refl-check involvement). A violation would let a proof
      of a FALSE equation be manufactured, and rewrite/transport along it would
      coerce between distinct normal forms — the classic identity-type unsoundness.

    * ENSURE_EQ-IS-Eq-PRECISE — the widened consumer treats a value as an equality
      **iff** it is genuinely the `Eq` family, and extracts its endpoints in the
      right order (`a` then `b`). Pinned by transporting through a `{:rewrite}`
      node with an ENDPOINT-DISTINGUISHING motive: the result type must be
      `motive @ b`, never `motive @ a`. A same-shaped decoy family (`Fake`, 1
      parameter + 2 indices) must be REJECTED — proving the clause keys on the
      `:Eq` atom, not on the 3-element arity.

  Plus TERMINATION under a bounded Task harness. If any construction violates a
  SOUNDNESS assertion, the retarget is unsound: STOP — do not weaken the assertion.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Kernel, Context, Conv, Eval}
  alias Cure.Elab.Program

  @fuel 100_000

  # Default signature: every program's env seeds the builtin inductives, incl. the
  # new `Eq`/`refl` and `Nat`/`Bool` used below.
  defp base_sig do
    {:ok, sig} = Program.elaborate("mod M\nend\n")
    sig
  end

  # A signature that ALSO declares a decoy family `Fake(a) indices (x,y)` — the
  # exact 1-param/2-index shape of `Eq`, so a `{:vdata, :Fake, [ty,a,b]}` value is
  # byte-shaped like an `Eq` value but is NOT the identity type.
  defp fake_sig do
    {:ok, sig} =
      Program.elaborate("mod M\n  type Fake(a: Type) indices (x: a, y: a)\nend\n")

    sig
  end

  # ---- term helpers (closed Core) -------------------------------------------
  @nat {:data, :Nat, [], []}
  @bool {:data, :Bool, [], []}
  defp z, do: {:ctor, :Z, []}
  defp s(n), do: {:ctor, :S, [n]}
  defp nat_lit(0), do: z()
  defp nat_lit(n), do: s(nat_lit(n - 1))
  defp tru, do: {:ctor, :True, []}
  defp fls, do: {:ctor, :False, []}

  defp eq_ty(sig, ty, a, b), do: Eval.eval({:data, :Eq, [ty], [a, b]}, Context.env(Context.empty(sig)))

  # ---- SOUNDNESS: refl inhabits Eq(ty,x,y) IFF conv?(x,y) --------------------

  test "refl proves Eq(ty,x,y) iff x and y are genuinely convertible (independent Conv oracle)" do
    sig = base_sig()
    ctx = Context.empty(sig)

    # {label, ty, x, y}. Mixed equal / distinct pairs over two builtin types.
    scenarios = [
      {"Z = Z", @nat, z(), z()},
      {"S Z = S Z", @nat, s(z()), s(z())},
      {"2 = 2", @nat, nat_lit(2), nat_lit(2)},
      {"Z = S Z", @nat, z(), s(z())},
      {"S Z = Z", @nat, s(z()), z()},
      {"S Z = 2", @nat, s(z()), nat_lit(2)},
      {"2 = 3", @nat, nat_lit(2), nat_lit(3)},
      {"True = True", @bool, tru(), tru()},
      {"False = False", @bool, fls(), fls()},
      {"True = False", @bool, tru(), fls()},
      {"False = True", @bool, fls(), tru()}
    ]

    for {label, ty, x, y} <- scenarios do
      # Kernel judgement: does `refl x` check at `Eq ty x y`?
      accepts = Kernel.check(ctx, {:ctor, :refl, [x]}, eq_ty(sig, ty, x, y)) == :ok

      # Independent oracle: are the two endpoints convertible? (No refl involved.)
      # conv_within? takes Core terms and evaluates them itself.
      convertible = match?({:ok, true}, Conv.conv_within?(x, y, [], 0, sig, @fuel))

      assert accepts == convertible,
             "REFL-IS-REFLEXIVE VIOLATION for #{label}: kernel accepts refl=#{accepts} but " <>
               "endpoints convertible=#{convertible}. A refl proof must inhabit Eq(ty,x,y) " <>
               "iff x≡y — otherwise a false equation is provable and transport is unsound."
    end
  end

  # ---- ENSURE_EQ endpoint fidelity via an endpoint-distinguishing rewrite ----

  test "rewrite over an inductive Eq(Nat,Z,S Z) hypothesis transports to motive @ b (not motive @ a)" do
    sig = base_sig()

    # Hypothesis h : Eq(Nat, Z, S Z) in context (a hypothetical, possibly-false
    # equation — the kernel never needs it to be TRUE to type the transport, only
    # to extract the correct endpoints).
    ctx = Context.extend(Context.empty(sig), eq_ty(sig, @nat, z(), s(z())))

    # Endpoint-distinguishing motive:  λ x:Nat. Eq(Nat, x, Z)
    #   motive @ Z    = Eq(Nat, Z,   Z)
    #   motive @ S Z  = Eq(Nat, S Z, Z)
    motive = {:lam, @nat, {:data, :Eq, [@nat], [{:var, 0}, z()]}}

    # rewrite (h : Eq Nat Z (S Z))  at motive  in (refl Z : motive @ Z).
    # body is checked at motive @ a = Eq(Nat,Z,Z); result must be motive @ b.
    node = {:rewrite, {:var, 0}, motive, {:ctor, :refl, [z()]}}

    result = Kernel.infer(ctx, node)

    expected_b = eq_ty(sig, @nat, s(z()), z())
    expected_a = eq_ty(sig, @nat, z(), z())

    assert {:ok, ^expected_b} = result,
           "ENDPOINT FIDELITY VIOLATION: rewrite result was #{inspect(result)}, expected " <>
             "motive @ b = #{inspect(expected_b)}. If it were motive @ a = #{inspect(expected_a)}, " <>
             "ensure_eq swapped the endpoints."

    refute match?({:ok, ^expected_a}, result),
           "rewrite transported to motive @ a — endpoints extracted in the wrong order"
  end

  # ---- ENSURE_EQ is :Eq-precise: a same-shaped decoy family is NOT an equality -

  test "a rewrite whose proof has a same-shaped non-Eq family type is rejected" do
    sig = fake_sig()

    # h : Fake(Nat, Z, Z) — byte-shaped exactly like Eq(Nat,Z,Z) as a {:vdata,...}
    # value, but a DIFFERENT family. ensure_eq/eq_parts must not treat it as an
    # equality (they key on the :Eq atom, not the 3-element arity).
    fake_val = Eval.eval({:data, :Fake, [@nat], [z(), z()]}, Context.env(Context.empty(sig)))
    ctx = Context.extend(Context.empty(sig), fake_val)

    node = {:rewrite, {:var, 0}, {:lam, @nat, @nat}, z()}

    assert {:error, _} = Kernel.infer(ctx, node),
           "SOUNDNESS VIOLATION: rewrite accepted a proof of the non-Eq family Fake — " <>
             "ensure_eq must recognise ONLY the genuine Eq family as an equality."

    # Positive control on the SAME signature: a real Eq hypothesis IS accepted.
    ctx_eq = Context.extend(Context.empty(sig), eq_ty(sig, @nat, z(), z()))
    assert {:ok, _} = Kernel.infer(ctx_eq, {:rewrite, {:var, 0}, {:lam, @nat, @nat}, z()}),
           "a genuine Eq hypothesis should transport"
  end

  # ---- TERMINATION -----------------------------------------------------------

  test "refl-check and rewrite-infer over inductive Eq halt (bounded)" do
    sig = base_sig()
    ctx = Context.empty(sig)
    ctx_h = Context.extend(ctx, eq_ty(sig, @nat, z(), z()))

    jobs = [
      fn -> Kernel.check(ctx, {:ctor, :refl, [nat_lit(3)]}, eq_ty(sig, @nat, nat_lit(3), nat_lit(3))) end,
      fn -> Kernel.check(ctx, {:ctor, :refl, [z()]}, eq_ty(sig, @nat, z(), s(z()))) end,
      fn -> Kernel.infer(ctx_h, {:rewrite, {:var, 0}, {:lam, @nat, @nat}, z()}) end
    ]

    for {job, i} <- Enum.with_index(jobs) do
      task = Task.async(job)
      assert Task.yield(task, 5_000) || Task.shutdown(task),
             "job #{i} (inductive Eq refl/rewrite) did not return within budget"
    end
  end
end
