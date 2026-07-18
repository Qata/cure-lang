defmodule Cure.Compiler.OperatorFlipTest do
  @moduledoc """
  Phase 3: operators parse via the declaration-driven `FixityTable`, not the
  static `Precedence` table. Word operators (`and`/`or`/`not`) and user-declared
  symbolic operators bind by their `precedencegroup`, and an overloadable
  operator desugars to a call on a function named by its lexeme.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Emit, Program}

  # -- real evaluation harness (mirrors the Phase-2 differential test) --------

  defp run(src, fname) do
    {:ok, env} = Program.elaborate(src)
    fns = Program.reachable_def_names(env, [fname])
    out = :"Cure.OpFlip#{System.unique_integer([:positive])}"
    {:ok, m} = Emit.compile_and_load(env, module: out, functions: fns)
    apply(m, fname, [])
  end

  defp eval(expr), do: run("mod E\n  fn go() -> Bool = #{expr}\nend\n", :go)

  defp eval_in(src, call) do
    fname = call |> String.trim_trailing("()") |> String.to_atom()
    run(src, fname)
  end

  # An error tag surfaces from `Program.elaborate/1` either bare (elaboration
  # errors are single tuples) or inside the parser's error LIST (parse errors).
  # Match either wrapping while pinning the tag — the intent, not the envelope.
  defp assert_error_tag(src, tag) do
    assert {:error, payload} = Program.elaborate(src)

    found =
      case payload do
        list when is_list(list) -> Enum.find(list, &match?({^tag, _, _}, &1)) || Enum.find(list, &match?({^tag, _}, &1))
        other -> if match?({^tag, _, _}, other) or match?({^tag, _}, other), do: other
      end

    assert found, "expected an #{inspect(tag)} error, got: #{inspect(payload)}"
    found
  end

  test "word operators resolve to their functions" do
    assert eval("true and false") == false
    assert eval("not true") == false
  end

  test "a user-declared operator dispatches to its function" do
    src = """
    mod M
      use Std.Operators
      precedencegroup Custom
        associativity: left
        higher_than: Additive
      infix `<?>` : Custom
      fn `<?>`(a: Int, b: Int) -> Int = Std.Builtin.int_add(a, b)
      fn go() -> Int = 1 <?> 2 <?> 3
    end
    """

    assert eval_in(src, "go()") == 6
  end

  test "incomparable operators without parens are rejected" do
    src = """
    mod M
      use Std.Operators
      precedencegroup GroupA
        associativity: left
      precedencegroup GroupB
        associativity: left
      infix `<?>` : GroupA
      infix `<!>` : GroupB
      fn `<?>`(a: Int, b: Int) -> Int = a
      fn `<!>`(a: Int, b: Int) -> Int = b
      fn bad() -> Int = 1 <?> 2 <!> 3
    end
    """

    assert_error_tag(src, :ambiguous_precedence)
  end

  test "a fixity declaration with no function errors at use" do
    src = """
    mod M
      use Std.Operators
      infix `<@>` : Additive
      fn nope() -> Int = 1 <@> 2
    end
    """

    assert_error_tag(src, :no_operator_meaning)
  end
end
