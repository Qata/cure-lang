defmodule Cure.Elab.LambdaArgumentOrderTest do
  @moduledoc """
  A known, open elaborator gap, pinned so it stays loud and so its edge is documented.

  An unannotated lambda argument declared BEFORE the argument that fixes its domain cannot be
  elaborated: the lambda's domain metavariable is only solved by the later argument, and
  arguments are elaborated left to right with no retry.

      fn app2(g: a -> b, xs: List(a)) -> List(b) = lmap(xs, g)
      fn bump(xs: List(Int)) -> List(Int) = app2(fn(x) -> x + 10, xs)   # fails

  Swapping the two parameters makes it elaborate. Nothing about interfaces is involved — this
  first surfaced through a higher-kinded `fmap(g, container)` whose parameters were declared in
  that order, which is why it was mistaken for a dispatch-head bug. `Resolve.head_param_index/2`
  now locates the `f(a)`-typed parameter wherever it is declared (`resolve_head_param_order_test`),
  and what remains is this.

  The fix belongs in the elaborator's argument machinery: either elaborate arguments in
  dependency order, or postpone a lambda argument until its domain metavariable is solved and
  revisit it — Idris 2's retry queue in `Core/Unify.idr`, Agda's postponed type-checking
  constraints. `resolve_deferred_slots` already does a narrow version of this for a deferred
  argument's own domain metavariable.

  Until then the contract these tests hold is: it FAILS, and it fails loudly. Nothing is
  silently mis-elaborated. If one of the failing tests starts passing, the gap is closed —
  delete the test rather than weaken it.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @lmap """
    fn lmap(xs: List(a), g: a -> b) -> List(b) =
      match xs
        [] -> []
        [h | t] -> [g(h) | lmap(t, g)]
  """

  defp elaborate(decls), do: Program.elaborate("mod M\n" <> @lmap <> decls <> "end\n")

  test "a lambda argument AFTER the argument that fixes its domain elaborates" do
    decls = """
      fn app2(xs: List(a), g: a -> b) -> List(b) = lmap(xs, g)
      fn bump(xs: List(Int)) -> List(Int) = app2(xs, fn(x) -> x + 10)
    """

    assert {:ok, _env} = elaborate(decls)
  end

  test "a lambda argument BEFORE the argument that fixes its domain fails, loudly" do
    decls = """
      fn app2(g: a -> b, xs: List(a)) -> List(b) = lmap(xs, g)
      fn bump(xs: List(Int)) -> List(Int) = app2(fn(x) -> x + 10, xs)
    """

    assert {:error, _reason} = elaborate(decls)
  end

  test "the same gap through a higher-kinded interface method — not a dispatch bug" do
    src = """
    mod M
    #{@lmap}  interface Functor(f)
        fn fmap(g: a -> b, container: f(a)) -> f(b)
      implementation Functor for List
        fn fmap(g: a -> b, container: List(a)) -> List(b) = lmap(container, g)
      fn bump(xs: List(Int)) -> List(Int) = fmap(fn(x) -> x + 10, xs)
    end
    """

    # `:unsolved_metavariables` — the dispatch head was found; the lambda's domain was not.
    assert {:error, {:unsolved_metavariables, :deferred_argument}} = Program.elaborate(src)
  end

  # DISTINCT from the pinned gap above. Here the lambda's domain type has a SINGLE
  # type parameter that a LATER argument fully determines (`g: (a) -> a`, with `x: a`
  # fixing `a`) — so once the metavariable is solved the domain is fully concrete
  # `(a) -> a`, with NOTHING left to infer from the lambda body. This is exactly the
  # `set = over(o, fn(_) -> new, x)` shape in `Std.Optic`, which had to fall back to a
  # curried `const` helper. Unlike the `a -> b` cases, this is not the ordering
  # limitation — the deferred re-check simply mis-shifted the solved domain's de Bruijn
  # levels under the arrow binder (a `conversion_failure {:var,3} {:var,2}`), which is a
  # bug, not an inherent gap. With that fixed, the inline lambda elaborates.
  test "a lambda whose monomorphic domain a later argument fully fixes elaborates" do
    src = """
    mod M
    fn over2({a: Type}, g: (a) -> a, x: a) -> a = g(x)
    fn set3({a: Type}, new: a, x: a) -> a = over2(fn(ignored) -> new, x)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  # The same monomorphic `(a) -> a` lambda, but with its domain fixed by an EARLIER
  # argument (`x: a` before `g`), so the metavariable is already solved when the lambda
  # slot is reached — the "domain fully known" branch, a DIFFERENT code path than the
  # deferred one above. Both had the same de Bruijn mis-shift when the solved domain
  # carried free variables. This is the exact shape of `Std.Optic`'s
  # `set = over(o, fn(_) -> new, x)`, whose `over(o, g, x)` fixes the lambda's `a` from
  # the earlier `o : Optic(s, a, k)`.
  test "a lambda whose monomorphic domain an earlier argument fixes elaborates" do
    src = """
    mod M
    fn over3({a: Type}, x: a, g: (a) -> a) -> a = g(x)
    fn set4({a: Type}, new: a, x: a) -> a = over3(x, fn(ignored) -> new)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
