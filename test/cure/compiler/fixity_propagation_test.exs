defmodule Cure.Compiler.FixityPropagationTest do
  use ExUnit.Case, async: false
  alias Cure.Compiler.{Lexer, Parser}

  setup do
    dir = Path.join(System.tmp_dir!(), "fp_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    prev = Process.get(:cure_source_roots, [])
    Process.put(:cure_source_roots, [dir])
    on_exit(fn -> Process.put(:cure_source_roots, prev); File.rm_rf!(dir) end)
    {:ok, dir: dir}
  end

  defp parse(src, opts \\ []) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    Parser.parse(tokens, [emit_events: false] ++ opts)
  end

  test "a module that uses A can parse A's operator; assembly succeeds", %{dir: dir} do
    File.write!(Path.join(dir, "a.cure"), """
    mod A
      precedencegroup G
        associativity: left
      infix `<?>` : G
      fn `<?>`(a: Int, b: Int) -> Int = a
    end
    """)

    src = "mod B\n  use A\n  fn go() -> Int = 1 <?> 2\nend\n"
    assert {:ok, _ast} = parse(src)
  end

  test "conflicting fixity across two used modules is a parse error", %{dir: dir} do
    File.write!(Path.join(dir, "a.cure"), "mod A\n  precedencegroup Ga\n    associativity: left\n  infix `<?>` : Ga\nend\n")
    File.write!(Path.join(dir, "b.cure"), "mod B\n  precedencegroup Gb\n    associativity: left\n  infix `<?>` : Gb\nend\n")

    src = "mod C\n  use A\n  use B\nend\n"
    assert {:error, errors} = parse(src)
    assert Enum.any?(errors, &match?({:conflicting_operator_fixity, {"<?>", _, _}}, &1))
  end

  test "single-file parse with no source universe still binds core operators" do
    # No :cure_source_roots entries resolve; the built-in prelude still applies.
    Process.put(:cure_source_roots, [])
    src = "mod M\n  fn f(a: Int, b: Int) -> Int = a + b * 2\nend\n"
    assert {:ok, _ast} = parse(src)
  end
end
