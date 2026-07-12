defmodule Cure.Elab.EffectErasureTest do
  # §5.3 of the effect-type-former design: an `Effect`-typed binder may not be
  # `:erased`. Erasure deletes erased binders from the runtime term, so an erased
  # `Effect(T)` binder would silently drop a computation the type says must run —
  # unsound. The check walks the def's final Pi spine and rejects an erased binder
  # whose domain is `Effect`-headed. A PRESENT (ω) effect binder is fine (an
  # un-run effect value, like an unused `IO` action in Haskell); an erased
  # NON-effect binder is fine (the ordinary erased-implicit case).
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "an erased implicit Effect binder is rejected" do
    src = """
    mod M
      fn f({e: Effect(Int)}) -> Int = 3
    end
    """

    assert {:error, err} = Program.elaborate(src)

    assert match?({:effect_binder_erased, :f}, err) or
             (is_tuple(err) and elem(err, 0) == :effect_binder_erased),
           "expected :effect_binder_erased, got #{inspect(err)}"
  end

  test "a PRESENT (omega) Effect binder is accepted (un-run effect value)" do
    src = """
    mod M
      fn g(e: Effect(Int)) -> Int = 3
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "an erased NON-effect implicit binder is still accepted (ordinary case)" do
    src = """
    mod M
      fn h({x: Int}) -> Int = 3
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
