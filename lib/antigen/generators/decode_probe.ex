defmodule Antigen.Generators.DecodeProbe do
  @moduledoc """
  Known-label generator for the `serialize/decode` robustness vertical
  (`Antigen.Assays.Serialization`, `:decode_probe` clause): raw S-expression
  strings fed straight to `Cure.Core.Serialize.decode/1`, which must be TOTAL —
  a well-formed leaf/string decodes to `{:ok, _}`; malformed input returns
  `{:error, _}` and never crashes or loops.

  This reaches `Serialize`'s decode EDGE/ERROR paths that the term-roundtrip
  vertical cannot: bare-leaf `build` (int/float/atom/str, top level), the string
  tokenizer (`take_string` + `tokenize`'s `?"` clause), and the `parse` / `build`
  error branches (`:unexpected_eof` / `:unexpected_rparen` / `:unterminated_list`
  / `:malformed`). The challenge carries a raw string (no Core term), so
  `Coverage.terms_of/1` returns `[]` and the runner's well-formedness gate keeps it.
  """
  alias Antigen.{Gen, Challenge}

  # Decode to {:ok, _}: bare int/float/atom leaves + quoted strings (incl. an
  # escaped quote, for take_string's escape clause).
  @valid ["5", "-3", "0", "1.5", "-2.0", "foo", "Nat", "\"hi\"", "\"a\\\"b\""]

  # Decode to {:error, _}: unbalanced / non-atom-headed / truncated S-expressions.
  @invalid ["", ")", "(", "(foo", "(5 6)", "(int", "( )", "((", "))"]

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.frequency([
      {2, probe(@valid, :valid_sexp)},
      {3, probe(@invalid, :invalid_sexp)}
    ])
  end

  defp probe(pool, label) do
    Gen.bind(Gen.member_of(pool), fn s ->
      Gen.return(
        Challenge.new(
          kind: :decode_probe,
          assay: "serialize/decode",
          label: label,
          payload: %{input: s},
          note: "decode probe (#{label})"
        )
      )
    end)
  end
end
