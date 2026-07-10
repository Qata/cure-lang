defmodule :cure_std_test_test do
  use ExUnit.Case, async: true

  # `Std.Test.forall_shrunk/3` was declared `-> t` while returning the atom
  # `:ok` on success and raising `{:property_failed_with_shrunk, _}` on failure.
  # Neither branch inhabited `t`: at `t = Int` a caller was promised an integer
  # and handed `:ok`. The @extern postulate asserted a type the implementation
  # does not have, and asserted totality of a function that raises.
  #
  # It is now `-> Result(Atom, t)`, erasing to `{:ok, :ok}` on success and
  # `{:error, counterexample}` on failure. Total, and true of its type.
  #
  # The tags are LOWERCASE because the classic pipeline — which is what compiles
  # `lib/std/test.cure` — erases `Ok(v)` to `{:ok, v}`. The dependent pipeline
  # erases the same constructor to `{:Ok, v}`. The two disagree; every sibling
  # shim uses the lowercase form. `test/cure/stdlib/result_destructure_test.exs`
  # pins that classic Cure can actually destructure what this returns.
  #
  # The two tests this file used to hold asserted the old contract (`:ok`, and
  # a rescue of ErlangError). They were correct about the old behaviour; the
  # behaviour is what changed.

  test "forall_shrunk returns Ok when the property holds" do
    gen = fn _ -> 1 end
    property = fn n -> n > 0 end
    assert {:ok, :ok} = :cure_std_test.forall_shrunk(gen, property, 10)
  end

  test "forall_shrunk returns Error carrying the shrunk counterexample" do
    gen = fn _ -> 100 end
    # Property: "n is less than 50" -- fails for 100, shrinks toward 50.
    property = fn n -> n < 50 end

    assert {:error, value} = :cure_std_test.forall_shrunk(gen, property, 5)
    # Shrinker must converge to a value at least as small as the original.
    assert value <= 100
  end

  test "forall_shrunk is total: a failing property is a value, not a raise" do
    gen = fn _ -> 100 end
    property = fn n -> n < 50 end

    # The old contract raised here. Totality is the point of the repair.
    assert {:error, _} = :cure_std_test.forall_shrunk(gen, property, 5)
  end

  test "forall_shrunk inhabits Result(Atom, t) at t = Int" do
    # The original defect, stated as a test: every returned value must be a
    # well-formed Result, and the counterexample must be a `t`.
    pass = :cure_std_test.forall_shrunk(fn _ -> 7 end, fn _ -> true end, 3)
    fail = :cure_std_test.forall_shrunk(fn _ -> 7 end, fn _ -> false end, 3)

    for r <- [pass, fail] do
      assert match?({:ok, _}, r) or match?({:error, _}, r), "not a Result: #{inspect(r)}"
    end

    assert {:error, cx} = fail
    assert is_integer(cx), "counterexample must be a `t` (Int here), got #{inspect(cx)}"
  end

  test "zero runs vacuously passes" do
    assert {:ok, :ok} = :cure_std_test.forall_shrunk(fn _ -> 1 end, fn _ -> false end, 0)
  end
end
