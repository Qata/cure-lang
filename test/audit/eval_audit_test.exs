defmodule Cure.Audit.EvalTest do
  @moduledoc """
  Audit findings for `lib/cure/core/eval.ex` (the trusted NbE evaluator).

  Each test below is a specific, currently-RED executable claim about
  behavior the audit believes is correct. See the comment above each test
  for the bug, why it is wrong, and what the reference implementations
  (Agda/Lean/Idris) do instead. Do not run this file automatically as part
  of the trusted-suite gate — it documents open findings, not yet-fixed
  regressions.
  """
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Core.Eval

  # E1: eval's :case handler has TWO ι-sites for constructor-shaped
  # scrutinees that reach `eval({:case, ...})`: the generic `{:vctor, cname,
  # args}` arm (eval.ex ~71-79) and a separate `{:vbounded, _}` arm
  # (eval.ex ~85-89) for compact `Bounded` literals. The `:vctor` arm looks
  # up the matching branch via `Enum.find/2` and, on `nil` (no branch for
  # this constructor), raises a descriptive
  # `"ι: no branch for constructor ... (coverage violation / ill-typed case
  # reached eval)"` error — exactly the fail-loud discipline this file uses
  # everywhere else for ill-typed input (see also `Eval.apply/2`'s
  # non-function raise at eval.ex ~114-115).
  #
  # The `:vbounded` arm does NOT reuse that lookup. It hand-rolls the same
  # three lines that `reduce_branch_body/4` already implements (the file's
  # own moduledoc for `reduce_branch_body` calls it "the SINGLE owner of
  # that invariant ... [so] the three sites [don't] drift" — this is
  # actually a fourth, undocumented site), and its `Enum.find/2` result is
  # destructured directly (`{_cname, arity, body} = Enum.find(...)`) with no
  # `nil` guard. When the branches list does not cover the scrutinee's
  # peeled constructor, this crashes with an uncontrolled `MatchError`
  # instead of the module's own descriptive coverage-violation error.
  #
  # Agda/Idris/Lean's evaluators do not distinguish "which built-in family"
  # a stuck/malformed elimination came from when reporting an impossible
  # reduction — the failure mode is uniform. Cure's own `:vctor` arm already
  # sets that bar; the `:vbounded` arm should clear it too, ideally by
  # calling `reduce_branch_body/4` directly instead of duplicating it.
  test "E1: case-ι on a Bounded scrutinee with no matching branch raises the same descriptive coverage error as the constructor path, not a bare MatchError" do
    # bounded_lit 1 peels to the :Next constructor; branches only cover :First.
    case_term = {:case, {:bounded_lit, 1}, {:type, 0}, [{:First, 1, {:bounded_lit, 42}}]}

    assert_raise RuntimeError, ~r/ι: no branch for constructor/, fn ->
      Eval.eval(case_term, [])
    end
  end

  # E2: every other ill-formed/ill-typed input this module can encounter
  # raises loudly and descriptively: `Eval.apply/2` on a non-function value
  # (eval.ex ~114-115: "is not a function (over-application / ill-typed
  # term)"), a `:case` whose scrutinee is not data (eval.ex ~96-97: "non-data
  # scrutinee ... reached eval"), a `:case` with no matching branch
  # (eval.ex ~76-78, see E1). `eval({:var, k}, env)` is the one exception:
  # when `k >= length(env)` (an out-of-scope / malformed variable
  # reference), it does not raise — it manufactures
  # `{:vneutral, {:nvar, k}}` (eval.ex ~24-28), silently reusing the de
  # Bruijn *index* `k` as if it were a de Bruijn *level*.
  #
  # That distinction is load-bearing elsewhere in the kernel: `value.ex`
  # documents `{:nvar, level}` as carrying "a de Bruijn *level*", and
  # `Quote.reify`'s neutral read-back (quote.ex ~94) converts a stored level
  # back to a source index via `depth - level - 1` — a formula that assumes
  # the stored number really is a level relative to the *ambient* context
  # depth, not a raw index from whatever (possibly truncated/malformed) `env`
  # `eval` happened to be called with. Laundering an out-of-range index
  # through this path produces a value that type-checks as a well-formed
  # neutral (`Value.neutral?/1` only checks `is_integer(level) and level >=
  # 0`) but does not actually correspond to any variable in scope — exactly
  # the kind of "plausible but wrong" value a trusted-kernel evaluator should
  # never fabricate for malformed input. Idris/Agda/Lean's evaluators avoid
  # this failure mode entirely because their environments are always built
  # to be exactly context-sized; a defensive TCB evaluator that cannot rely
  # on that invariant should fail the same way it does everywhere else in
  # this file, rather than synthesize a lookalike value.
  test "E2: eval({:var, k}, env) with an out-of-range index fails loud instead of silently reusing the index as a de Bruijn level" do
    assert_raise RuntimeError, fn ->
      Eval.eval({:var, 3}, [])
    end
  end
end
