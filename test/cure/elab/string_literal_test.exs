defmodule Cure.Elab.StringLiteralTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  # A string literal is `List(Char)` (Char = Bounded(0x110000)); Char erases to a
  # native integer and List to a BEAM list, so `"abc"` runs to the charlist
  # `[97, 98, 99]`.
  # `Char` is not yet a prelude type (that lands with the Std.String migration,
  # #29), so — as in the char-literal tests — the module brings `Bounded` into
  # scope and aliases `Char` locally.
  defp run(body) do
    src = """
    mod S
      use Std.Bounded
      typealias Char = Bounded(1114112)
      fn t() -> List(Char) = #{body}
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.S", functions: [:t])
    apply(m, :t, [])
  end

  test ~s|"abc" elaborates to a List(Char) charlist and runs to [97, 98, 99]| do
    assert run(~s|"abc"|) == [97, 98, 99]
  end

  test ~s|the empty string "" is the empty charlist []| do
    assert run(~s|""|) == []
  end

  test ~s|"abc" is definitionally the char-literal list ['a', 'b', 'c']| do
    assert run(~s|"abc"|) == run(~s|['a', 'b', 'c']|)
  end

  test "a multi-byte UTF-8 string decodes by Unicode codepoint" do
    # é = U+00E9 = 233, 😀 = U+1F600 = 128512 — one Char each, not their UTF-8 bytes.
    assert run(~s|"é😀"|) == [233, 128_512]
  end
end
