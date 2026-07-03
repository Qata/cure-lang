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

  test "each wrapper is non-contaminating and fault-driven (deterministic, fixed filler)" do
    ctx = Context.empty(SigMenu.env_of(:v1))
    wt = {:ctor, :Z, []}                 # well-typed Nat
    fault = {:fst, {:ctor, :Z, []}}      # intrinsically ill-typed

    for kind <- Mutation.wrappers() do
      assert {:ok, _} = Kernel.infer(ctx, Mutation.wrap(wt, kind, wt)),
             "wrapper #{kind} contaminated a well-typed inner"
      assert {:error, _} = Kernel.infer(ctx, Mutation.wrap(fault, kind, wt)),
             "wrapper #{kind} did not propagate the inner fault"
    end
  end

  test "a fixed deep wrapper stack stays well-typed and propagates a fault (composition)" do
    ctx = Context.empty(SigMenu.env_of(:v1))
    wt = {:ctor, :Z, []}
    fault = {:fst, {:ctor, :Z, []}}
    # fold every wrapper kind, innermost-first, with a fixed Nat filler
    stack = fn inner -> Enum.reduce(Mutation.wrappers(), inner, fn k, acc -> Mutation.wrap(acc, k, wt) end) end

    assert {:ok, _} = Kernel.infer(ctx, stack.(wt)), "deep fixed stack contaminated a well-typed inner"
    assert {:error, _} = Kernel.infer(ctx, stack.(fault)), "deep fixed stack swallowed the fault"
  end

  test "every operator and every wrapper kind is reachable by construction (deterministic)" do
    ctx = Context.empty(SigMenu.env_of(:v1))
    # each operator's build deterministically records its own fault kind
    kinds = Enum.map(Mutation.operators(), fn op -> elem(Mutation.build(ctx, op), 1).kind end)
    assert Enum.sort(kinds) == Enum.sort(Mutation.operators())
    # each wrapper kind applies without error and yields a distinct well-formed term
    # (inner != filler: :case_scrut's branch body ignores the filler and :case_branch's
    # scrutinee ignores the inner, so inner == filler would make those two wrapper
    # outputs byte-identical and collapse the uniq count to 4 — verified by direct
    # run with inner = filler = {:ctor,:Z,[]})
    terms = Enum.map(Mutation.wrappers(), fn k -> Mutation.wrap({:ctor, :Z, []}, k, {:ctor, :S, [{:ctor, :Z, []}]}) end)
    assert length(Enum.uniq(terms)) == length(Mutation.wrappers())
    assert Enum.all?(terms, &Cure.Core.Term.term?/1)
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
