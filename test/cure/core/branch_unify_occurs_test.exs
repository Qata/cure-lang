defmodule Cure.Core.BranchUnifyOccursTest do
  @moduledoc """
  Named occurs-check/cycle antibody (pre-port banking spec §4 W3; roadmap A2/#23).

  In well-formed signatures a ctor's result indices are closed over its own
  telescope (vars < arity), so a cyclic solve cannot arise from elaborator
  output — the kernel's occurs check (`bind_index` → `:undecided`) is a
  DEFENSIVE rule against adversarial signatures, reachable through the public
  `Kernel.branch_unify/4`. This test constructs exactly that adversary: a ctor
  whose result index references a variable OUTSIDE its telescope, producing the
  equation `MkWr(x) ~ x` whose only solve is the cyclic `x := MkWr(x)`. Pinned
  behavior: the kernel neither loops nor fabricates the solve — the equation
  degrades and the verdict is `:trivial` (no refinement), never `{:solved, _}`.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Env, Eval, Inductive, Kernel}

  @dec {:data, :Dec, [], []}
  @wr {:data, :Wr, [], []}

  test "a cyclic index equation degrades (occurs check): :trivial, never a solve, never a loop" do
    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [
        Inductive.ctor(:Dcoupled, [], []),
        Inductive.ctor(:Causal, [], [])
      ])
      |> Inductive.declare(Inductive.family(:Wr, [], [], 0), [
        Inductive.ctor(:MkWr, [{:d, @dec}], [])
      ])
      # adversarial: result index {:ctor, :MkWr, [{:var, 1}]} references var 1,
      # OUTSIDE the 1-slot telescope (arity 1 ⇒ own vars are < 1)
      |> Inductive.declare(Inductive.family(:IW, [], [{:w, @wr}], 0), [
        Inductive.ctor(:iw, [{:p, @dec}], [{:ctor, :MkWr, [{:var, 1}]}])
      ])

    ctx = Context.empty(env) |> Context.extend(Eval.eval(@wr, []))
    # scrutinee index value: the neutral outer variable x itself
    scrut_index = {:vneutral, {:nvar, 0}}

    assert :trivial = Kernel.branch_unify(ctx, :IW, :iw, [scrut_index])
  end
end
