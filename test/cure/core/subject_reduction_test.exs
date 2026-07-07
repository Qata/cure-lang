defmodule Cure.Core.SubjectReductionTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{MetaCheck, Context}

  # Seed corpus of closed, well-typed, *inferable* terms, each exercising a
  # reduction (or already normal). Grows per wave. Every entry is closed and
  # global-free so it needs no def env. NB: bare `{:pair, …}` is check-only (the
  # kernel has no infer rule for it), so sigma terms are excluded until a later
  # wave adds an inferable eliminator corpus.
  @corpus [
    {:app, {:lam, {:type, 0}, {:var, 0}}, {:int_type}},        # beta -> {:int_type}
    {:app, {:lam, {:int_type}, {:var, 0}}, {:int_lit, 7}},     # beta -> {:int_lit, 7}
    {:type, 0}                                                 # already normal
  ]

  test "the harness rejects an ill-typed term (detection works)" do
    # applying a type to a type is ill-typed -> not type-preserved
    refute MetaCheck.type_preserved?(Context.empty(), {:app, {:type, 0}, {:type, 0}})
  end

  test "every corpus term preserves its type under normalization (#638)" do
    for term <- @corpus do
      assert MetaCheck.type_preserved?(Context.empty(), term), "not type-preserved: #{inspect(term)}"
    end
  end
end
