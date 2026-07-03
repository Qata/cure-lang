defmodule Antigen.Assays.ElabSoundnessTest do
  use ExUnit.Case, async: true
  alias Antigen.{Assays.Elab, Challenge}
  alias Cure.Core.{Env, Builtins}

  @bool {:data, :Bool, [], []}
  @nat {:data, :Nat, [], []}

  defp prog(src), do: Challenge.new(kind: :elab_program, assay: "elab/soundness",
                       label: :well_typed, payload: %{id: 1, src: src}, seed: 1)

  # A seeded env (Bool/Nat families present) so infer/eval resolve @bool/@nat.
  # NOTE: `Builtins.seed/2`'s 2nd arg is a MapSet (families to SKIP seeding),
  # not a list — `seed(Env.empty(), [])` crashes `MapSet.member?/2` with
  # FunctionClauseError (verified). Call the 1-arity form (uses the `MapSet.new()`
  # default) so every test below actually reaches the assay instead of crashing
  # in the fixture.
  defp seeded, do: Builtins.seed(Env.empty())

  # An op-map identical to @real_kernel EXCEPT `elaborate`, which returns a
  # synthetic env — the only way to feed the decision procedure a chosen env.defs.
  defp kernel_with_env(env) do
    %{elaborate: fn _src -> {:ok, env} end,
      infer: &Cure.Core.Kernel.infer/2, check: &Cure.Core.Kernel.check/3,
      conv: &Cure.Core.Conv.conv_values?/4, eval: &Cure.Core.Eval.eval/2}
  end

  test "baseline: a genuinely well-typed program re-checks sound (:ok)" do
    # id : Nat -> Nat = fn x -> x ; emitted core body {:lam,Nat,{:var,0}} infers cleanly.
    assert Elab.run(prog("mod P\nfn id(x: Nat) -> Nat = x\nend")) == :ok
  end

  test "type_annotation_wrong: body checkable but at a different type" do
    # def `bad`: body is Bool->Bool identity, DECLARED Nat->Nat. infer=vpi Bool Bool,
    # eval(declared)=vpi Nat Nat -> not convertible -> type_annotation_wrong.
    env = seeded()
          |> Env.add_def(:bad, {:pi, @nat, @nat}, {:lam, @bool, {:var, 0}})
    assert {:violation, {:type_annotation_wrong, :bad, _}} =
             Elab.run(prog("ignored"), kernel_with_env(env))
  end

  test "reject is NOT a V3 infection (belongs to elab/completeness)" do
    # A program the elaborator rejects -> {:error,_} from elaborate -> :ok here.
    assert Elab.run(prog("mod P\nfn oops(x: Nat) -> Nat = nonexistent_fn(x)\nend")) == :ok
  end

  test "elaborator crash is an infection" do
    k = %{elaborate: fn _ -> raise "boom" end, infer: &Cure.Core.Kernel.infer/2,
          check: &Cure.Core.Kernel.check/3, conv: &Cure.Core.Conv.conv_values?/4,
          eval: &Cure.Core.Eval.eval/2}
    assert {:violation, {:elaborator_raised, 1, _}} = Elab.run(prog("x"), k)
  end

  test "hole-bearing def is skipped, not infected" do
    # body has a hole; kernel would accept, but we skip it -> whole run :ok.
    env = seeded() |> Env.add_def(:h, {:pi, @nat, @nat}, {:lam, @nat, {:hole, :g}})
    assert Elab.run(prog("ignored"), kernel_with_env(env)) == :ok
  end

  test "run/2 with the real op-map is byte-identical to run/1" do
    c = prog("mod P\nfn id(x: Nat) -> Nat = x\nend")
    assert Elab.run(c) == Elab.run(c, Elab.__real_kernel__())
  end

  describe "constructor bodies (checking-mode fallback)" do
    # `Option(T)` is parameter-bearing; `Some(v)` bodies are inferable only in
    # checking mode. Kernel.infer returns {:error, {:ctor_requires_checking_mode, _}}.
    # Build the family + a sound and an unsound def directly in a seeded env.
    defp option_env do
      # A minimal parameter-bearing family F(a: Type) with ctor Mk(x: a) : F(a).
      #
      # Two details are load-bearing, verified against Kernel.check's `{:ctor,...}`
      # clause (which re-derives `actual = {:vdata, family, actual_params ++
      # actual_indices}` from `result_params`/`result_indices` and Conv-compares it
      # to the expected `{:vdata,...}}`):
      #   1. `declare/3`'s 3rd arg is `[ctor()]` (a LIST) — `declare(fam, ctor)`
      #      (bare map) makes `Enum.reduce` inside `declare/3` iterate the ctor
      #      MAP's `{key, value}` pairs instead of the ctor itself, crashing with
      #      MatchError on `%{name: cname} = c`.
      #   2. `result_params` must be `[{:var, 1}]` (mirrors Kernel's own
      #      `check_uniform_params/5` formula `{:var, num_args + (num_params - 1 -
      #      p)}` for Mk's 1 arg / F's 1 param), NOT `[]`. With `[]`, `check/3`
      #      re-derives `actual = {:vdata, :F, []}` (param dropped) instead of
      #      `{:vdata, :F, [Nat]}`, so `Conv.conv_values?`'s spine-length check
      #      fails `conv_spine?` even for the intentionally-SOUND `ok_mk` case
      #      below (0-length actual spine vs 1-length expected) — the "sound"
      #      test would falsely report a `{:core_ill_typed, ...}}` violation
      #      instead of `:ok`.
      fam = Cure.Core.Inductive.family(:F, [{:a, {:type, 0}}], [], 0)
      ctor = Cure.Core.Inductive.ctor(:Mk, [{:x, {:var, 0}}], [], [:present], [{:var, 1}])
      seeded() |> Cure.Core.Inductive.declare(fam, [ctor])
    end

    test "sound parameter-bearing constructor body re-checks :ok (uses check, not infer)" do
      # def ok_mk : F(Nat) = Mk(Z)   — well typed; infer alone would misreport it.
      env = option_env()
            |> Env.add_def(:ok_mk, {:data, :F, [@nat], []}, {:ctor, :Mk, [{:ctor, :Z, []}]})
      assert Elab.run(prog("ignored"), kernel_with_env(env)) == :ok
    end

    test "mismatched constructor body still infects" do
      # def bad_mk : F(Bool) = Mk(Z)  — Z:Nat, but F(Bool) expects x:Bool -> reject.
      env = option_env()
            |> Env.add_def(:bad_mk, {:data, :F, [@bool], []}, {:ctor, :Mk, [{:ctor, :Z, []}]})
      assert {:violation, {:core_ill_typed, :bad_mk, _}} =
               Elab.run(prog("ignored"), kernel_with_env(env))
    end
  end
end
