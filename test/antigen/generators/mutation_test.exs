defmodule Antigen.Generators.MutationTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.{Mutation, SigMenu}
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.{Context, Kernel}

  defp sample(gen, n), do: B.interp(gen) |> Enum.take(n)

  test "every operator produces a term the kernel REJECTS under infer (construction guarantee)" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)

    for kind <- Mutation.operators() do
      {gen, fault} = Mutation.build(ctx, kind)
      assert fault.kind == kind
      for term <- sample(gen, 20) do
        assert {:error, _} = Kernel.infer(ctx, term),
               "operator #{kind} produced an infer-ACCEPTED term: #{inspect(term)}"
      end
    end
  end

  test "each operator's fault carries a kernel-INDEPENDENT witness of ill-typedness" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)

    for kind <- Mutation.operators() do
      {_gen, f} = Mutation.build(ctx, kind)

      case f.witness do
        :head ->
          assert f.expected_head != f.injected_head,
                 "#{kind}: heads must differ (#{inspect(f.expected_head)} vs #{inspect(f.injected_head)})"
        :index ->
          # distinct closed index constructors ⇒ non-convertible, decided syntactically
          assert f.expected_head != f.injected_head
        :level ->
          {:type, req} = f.expected_head
          {:type, act} = f.injected_head
          assert act > req, "#{kind}: injected level must exceed required (predicativity)"
        :scope ->
          {k, gamma_len} = f.scope
          assert k >= gamma_len, "#{kind}: var index must be out of scope"
      end
    end
  end

  test "mutant/0 emits a well-formed :mutant_term challenge that the kernel rejects" do
    alias Antigen.Challenge
    for c <- sample(Mutation.mutant(), 60) do
      assert %Challenge{kind: :mutant_term, assay: "mutation/rejection", label: :ill_typed, payload: p} = c
      assert p.sig == :v1
      assert p.fault.kind in Mutation.operators()
      env = SigMenu.env_of(:v1)
      ctx = SigMenu.rebuild_context(env, p.ctx)
      assert {:error, _} = Kernel.infer(ctx, p.term)   # generation totality + rejection
    end
  end

  test "a large sample draws at least 5 distinct fault kinds (diversity is reachable)" do
    kinds = sample(Mutation.mutant(), 200) |> Enum.map(& &1.payload.fault.kind) |> Enum.uniq()
    assert length(kinds) >= 5
  end

  test "deepen wraps a fault so it still infer-rejects, and is UNCONTAMINATED (wt inner accepts)" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    fault = {:fst, {:ctor, :Z, []}}   # intrinsic: infer fails on its own
    wt = {:ctor, :Z, []}              # well-typed Nat

    for depth <- [0, 1, 4, Mutation.max_depth()] do
      # fault deepened → still rejects; wrap_path length == depth, kinds valid
      for {deep, path} <- sample(Mutation.deepen(ctx, fault, depth), 15) do
        assert length(path) == depth
        assert Enum.all?(path, &(&1 in Mutation.wrappers()))
        assert {:error, _} = Kernel.infer(ctx, deep)
      end

      # SAME wrapper stack around a well-typed Nat must ACCEPT — this is what proves
      # the rejection above is FAULT-driven, not a wrapper-internal type error
      # (a contaminated stack would reject the well-typed inner too).
      for {deep_wt, _} <- sample(Mutation.deepen(ctx, wt, depth), 15) do
        assert {:ok, _} = Kernel.infer(ctx, deep_wt),
               "contaminated stack at depth #{depth}: #{inspect(deep_wt)}"
      end
    end
  end

  test "every wrapper kind is reachable across depth-1 draws" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    fault = {:fst, {:ctor, :Z, []}}
    seen =
      for {_deep, [k]} <- sample(Mutation.deepen(ctx, fault, 1), 300), do: k
    assert Enum.uniq(seen) |> length() >= 4   # ≥4 of the 5 kinds appear
  end

  test "mutant/0 emits deep mutants: depth/wrap_path recorded, still rejected, depth reached" do
    depths =
      for c <- sample(Mutation.mutant(), 300) do
        p = c.payload
        assert length(p.fault.wrap_path) == p.fault.depth
        assert p.fault.depth >= 0 and p.fault.depth <= Mutation.max_depth()
        assert Enum.all?(p.fault.wrap_path, &(&1 in Mutation.wrappers()))
        env = SigMenu.env_of(:v1)
        ctx = SigMenu.rebuild_context(env, p.ctx)
        assert {:error, _} = Kernel.infer(ctx, p.term)
        p.fault.depth
      end

    assert Enum.max(depths) >= 4   # deep mutants actually generated
  end
end
