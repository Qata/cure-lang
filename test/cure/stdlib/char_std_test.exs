defmodule Cure.Stdlib.CharStdTest do
  @moduledoc """
  `Std.Char` gives the `Char` type a visible, documented home — the value-surface
  code-point type (`Bounded(0x110000)`). Previously `Char` was a typealias buried
  inside `Std.Binary`; `use Std.Char` was a silently-tolerated no-op resolving to
  nothing. This pins that `Std.Char` is a real module that owns the alias, and
  `use Std.Char` now brings `Char` into scope through it.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @char_body {:data, :Bounded, [], [nat_lit: 1114112]}

  test "Std.Char elaborates and owns the Char alias" do
    assert {:ok, env} = Program.elaborate(File.read!("lib/std/char.cure"))
    assert %{type: {:type, 0}, body: @char_body} = Map.get(env.defs, :Char)
  end

  test "use Std.Char brings Char into scope as Bounded(0x110000)" do
    src = "mod M\n  use Std.Char\n  fn f(c: Char) -> Char = c\nend\n"
    {:ok, env} = Program.elaborate(src)
    assert %{body: @char_body} = Map.get(env.defs, :Char)
  end

  test "Std.Binary re-uses Std.Char rather than redefining Char" do
    # binary.cure must NOT carry its own `typealias Char`; it imports Std.Char.
    src = File.read!("lib/std/binary.cure")
    refute src =~ ~r/typealias\s+Char\b/
    assert src =~ ~r/use\s+Std\.Char\b/
  end
end
