defmodule Cure.Core.ProgressTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{MetaCheck, Context}

  # Closed, well-typed, inferable terms; each normalizes to a canonical head.
  @corpus [
    {:app, {:lam, {:type, 0}, {:var, 0}}, {:int_type}},    # -> {:int_type} (canonical)
    {:app, {:lam, {:int_type}, {:var, 0}}, {:int_lit, 7}}, # -> {:int_lit, 7}
    {:lam, {:type, 0}, {:var, 0}}                          # already canonical (lam head)
  ]

  test "the harness rejects an ill-typed term (detection works)" do
    refute MetaCheck.progresses?(Context.empty(), {:app, {:type, 0}, {:type, 0}})
  end

  test "every closed well-typed corpus term reaches a canonical head (#639)" do
    for term <- @corpus do
      assert MetaCheck.progresses?(Context.empty(), term), "stuck / no progress: #{inspect(term)}"
    end
  end
end
