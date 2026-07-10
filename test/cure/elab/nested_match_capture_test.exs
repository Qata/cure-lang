defmodule Cure.Elab.NestedMatchCaptureTest do
  @moduledoc """
  Two nested `match`es, each scrutinising a value with a NESTED constructor
  pattern (`Some(Y(x, r))`), where the innermost body references a variable
  bound by the OUTER match's nested pattern, must elaborate.

  The nested-pattern desugarer (`compile_group`/`split_ctor_arms`) lowered a
  nested pattern to a tree of single-level matches over FRESH scrutinee names
  derived deterministically from the outer constructor: `Some(Y(x, r))` became
  `Some($nSome1) -> match $nSome1 | Y($nSome1_Y1, $nSome1_Y2) -> …`, renaming
  `x` to `$nSome1_Y1` in the body. Because the names were seeded only from the
  constructor (not made unique per invocation), the INNER match — desugared
  independently — regenerated the SAME `$nSome1_Y1` for its own binder and
  shadowed the outer one. The outer `x` reference was captured by the inner
  binder (a different type), so the body failed `:branch_type`.

  Giving each desugaring invocation a unique seed removes the capture. This is
  the residual blocker that kept `Std.Iter` (`zip_with`) off the dependent
  pipeline.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "inner match body references outer nested-pattern binder" do
    src = """
    mod M
      use Std.Option
      type W(a) = Y(a, a)
      fn f(a: Option(W(t)), b: Option(W(u))) -> Option(t) =
        match a
          None() -> None()
          Some(Y(x, ra)) ->
            match b
              None() -> None()
              Some(Y(y, rb)) -> Some(x)
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "let-bound nested-match lambda referencing outer binder (Std.Iter zip_with shape, non-curried)" do
    # The `let next = fn(_) -> nested match … outer-bound var …` shape used
    # throughout Std.Iter. (The fully-curried `f(x)(y)` direct-ctor variant is
    # blocked on a separate ctor-arg lambda bug — see the
    # direct-ctor-field-lambda finding — so this pins the capture fix on the
    # let-bound form that iter actually relies on.)
    src = """
    mod M
      use Std.Option
      type StepToken = Step
      type Iter(a) = Iter(StepToken -> Option(IterStep(a)))
      type IterStep(a) = Yield(a, Iter(a))
      local fn step(it: Iter(t)) -> Option(IterStep(t)) =
        match it
          Iter(next) -> next(Step())
      fn zip_first(a: Iter(t), b: Iter(u)) -> Iter(t) =
        let next = fn(_) ->
          match step(a)
            None() -> None()
            Some(Yield(x, rest_a)) ->
              match step(b)
                None() -> None()
                Some(Yield(y, rest_b)) -> Some(Yield(x, zip_first(rest_a, rest_b)))
        Iter(next)
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
