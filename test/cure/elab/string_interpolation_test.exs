defmodule Cure.Elab.StringInterpolationTest do
  @moduledoc """
  String interpolation `"a\#{e}b"` in the dependent pipeline, for String-valued
  holes. It desugars (in the elaborator, before Core) to a right fold of
  `Std.Binary.str_concat` over the segments — literal chunks become their
  `List(Char)` desugaring and each hole is elaborated in check mode against
  `List(Char)`. Nothing new reaches the kernel; `str_concat` is auto-preluded, so
  no import is needed.

  Scope: holes must already be `String` (`List(Char)`). Interpolating a non-string
  value (`"n=\#{count}"` with `count : Int`) is a type error here — automatic
  `show`-based conversion waits on the Show interface (#21). This mirrors the
  narrow-then-extend shape of the other batch ports.

  Part of the pre-#18 surface-construct port batch (see
  memory pre18-surface-construct-gaps).
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Emit, Program}

  defp compile!(fn_name, fn_src, mod) do
    src = "mod M\n" <> fn_src <> "\nend\n"
    assert {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, emit_events: false)
    assert {:ok, env} = Program.elaborate(src)
    origins = Program.import_origins(ast)

    assert {:ok, m} =
             Emit.compile_and_load(env, module: mod, functions: [fn_name], origins: origins)

    m
  end

  test "interpolation splices a String hole between literal chunks" do
    m =
      compile!(
        :greet,
        ~S|  fn greet(name: List(Char)) -> List(Char) = "hi #{name}!"|,
        :"Cure.Test.Interp"
      )

    assert apply(m, :greet, [~c"bob"]) == ~c"hi bob!"
  end

  test "interpolation with two holes folds all segments" do
    m =
      compile!(
        :pair,
        ~S|  fn pair(a: List(Char), b: List(Char)) -> List(Char) = "#{a}-#{b}"|,
        :"Cure.Test.Interp2"
      )

    assert apply(m, :pair, [~c"x", ~c"y"]) == ~c"x-y"
  end

  test "a non-String hole is a type error until Show lands" do
    src = ~S"""
    mod M
      fn f(count: Int) -> List(Char) = "n=#{count}"
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end
end
