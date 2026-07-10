defmodule Cure.Audit.ValidatorTest do
  @moduledoc """
  Audit findings for `lib/cure/core/validator.ex` (the Final-Core
  grammar-boundary scanner — Wave 0 / K11a).

  Each test below is a specific, currently-RED executable claim about
  behavior the audit believes is correct. See the comment above each test
  for the bug and why it is wrong. Do not run this file automatically as
  part of the trusted-suite gate — it documents open findings, not yet-fixed
  regressions.
  """

  # async: false — V1 calls `Application.put_env(:cure, :final_core_config,
  # …)`, the same process-independent GLOBAL key `Kernel.check_def/2` reads
  # (every other `test/cure/core/` suite calls `check_def` too). This mirrors
  # `test/cure/core/validator_test.exs`'s own documented rationale for
  # keeping that whole file serial rather than risking a spurious
  # cross-file rejection while the override is live.
  use ExUnit.Case, async: false
  @moduletag :audit

  alias Cure.Core.{Env, Kernel, Validator}

  # V1: `Kernel.check_def/2` (kernel.ex ~419-436) has TWO admission branches.
  # The generic branch (`%{type: type_term, body: body_term} -> …`) runs
  # `infer_sort`, `check`, AND `run_final_core_validator(type_term,
  # body_term)` — the Final-Core grammar scan covers the declared TYPE, which
  # `test/cure/core/validator_test.exs`'s "a violating node in the declared
  # TYPE is caught too" test exists specifically to pin.
  #
  # The BUILTIN-OP branch (`%{builtin_op: op, type: type_term} when not
  # is_nil(op) -> with {:ok, _level} <- infer_sort(Context.empty(env),
  # type_term), do: :ok`) checks ONLY that the declared type is a valid sort
  # — it never calls `run_final_core_validator` at all, on the type or
  # anything else. A builtin-op def's declared TYPE is therefore completely
  # invisible to the Final-Core grammar boundary: any clause configured to
  # `:reject` (including ones already `:reject` in `release_config/0`, and
  # any future clause a caller flips on via `Application.put_env(:cure,
  # :final_core_config, …)`) is silently never enforced for this admission
  # path. This is exactly the trust-boundary gap the validator exists to
  # close — "Wave 0 runs as pure instrumentation... [catching] a legacy node
  # in a signature [a]s much a checklist hit as one in the body" (kernel.ex
  # ~439-441) is true for the generic branch and false for the builtin-op
  # one.
  #
  # Reproduced with a `qualified_syms` violation (a bare-atom `{:global, _}`
  # reference) rather than a hole, because a hole in a TYPE position does not
  # kernel-typecheck at all (`Kernel.infer/2` has no `{:hole, _}` clause,
  # only `check/3` does) — the violation must be one that legitimately
  # kernel-typechecks so the bypass, not an unrelated kernel rejection, is
  # what is being demonstrated.
  test "V1: a builtin-op def's declared TYPE bypasses the Final-Core validator entirely" do
    {:ok, env0} = Cure.Elab.Program.elaborate("mod M\nend\n")

    env =
      env0
      |> Env.add_def(:natty, {:type, 0}, {:data, :Nat, [], []})
      |> Env.add_def(:myop, {:global, :natty}, nil)
      |> Env.register_builtin_op(:myop, :some_op)

    cfg = Map.put(Validator.wave0_config(), :qualified_syms, :reject)
    Application.put_env(:cure, :final_core_config, cfg)
    on_exit(fn -> Application.delete_env(:cure, :final_core_config) end)

    # Sanity: the SAME type term, scanned directly by the validator under this
    # config, IS flagged — proving the clause exists and fires; the gap is
    # `check_def`'s wiring, not an inert predicate.
    assert {:error, direct} = Validator.validate({:global, :natty}, cfg)
    assert Enum.any?(direct, &(&1.clause == :qualified_syms))

    # `check_def` on the builtin-op def must surface the same violation, not
    # silently admit it.
    assert {:error, {:final_core_violation, rejections}} = Kernel.check_def(env, :myop)
    assert Enum.any?(rejections, &(&1.clause == :qualified_syms))
  end

  # V2: `children/1`'s documented purpose for its fallback clause (validator.ex
  # ~140-153) is to "descend CONSERVATIVELY into every element that is itself
  # a term-tuple or a list of them, so a forbidden node buried in an unknown
  # wrapper cannot escape the walker (fail-closed)". `test/cure/core/
  # validator_unknown_node_test.exs` proves this holds for a node whose
  # subterm sits directly in a list (one level of list nesting, e.g. a graded
  # 4-tuple `:app`).
  #
  # But `term_children/1`'s list clause (validator.ex ~152) is
  # `Enum.filter(xs, &is_tuple/1)` — it keeps only elements of `xs` that are
  # THEMSELVES tuples. An element that is itself a LIST (list-of-lists, one
  # level deeper than the tested case) is not a tuple, so it is filtered OUT
  # instead of being descended into. Any unrecognized future node shape whose
  # field is a list of lists of subterms therefore hides everything inside
  # that inner list from the walker completely — the exact "fail-open"
  # failure mode `validator_unknown_node_test.exs` was written to close, one
  # nesting level deeper than that fix actually reaches. This directly
  # contradicts the fallback's own "cannot escape the walker" comment.
  test "V2: a hole nested two lists deep inside an unrecognized node escapes the fail-closed fallback walker" do
    node = {:futuretag, [[{:hole, :h}]]}

    assert {:error, diags} = Validator.validate(node, Validator.release_config())

    assert Enum.any?(diags, &(&1.clause == :no_hole)),
           "the doubly-nested hole must be discovered and rejected; got #{inspect(diags)}"
  end
end
