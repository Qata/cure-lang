defmodule :cure_std_char do
  @moduledoc """
  Runtime helper for `Std.Char`.

  Target of the `@extern` bridge in `lib/std/char.cure`. A `Char` is
  `Bounded(0x110000)`, which erases to a native integer (its Unicode code
  point), so exposing the code point as an `Int` is the identity at run time.
  The bridge exists purely to give that type-level `Char -> Int` coercion a
  name (`Std.Char.code_point`, the Lean `Fin.val` analog), which `Std.Comparable`'s
  `Char`/`String` instances use to compare code points. The name is
  `code_point`, not `to_int`, because `Std.String` also exposes a `to_int`
  (parse) and the dependent pipeline resolves globals by bare name.
  """

  @doc "Code point of a Char. Char erases to its integer code point, so this is `id`."
  def code_point(cp) when is_integer(cp), do: cp
end
