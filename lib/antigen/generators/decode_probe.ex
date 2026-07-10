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

  @doc """
  Coverage-manifest cells (`Antigen.CoverManifest`): the two decode outcomes the
  probe asserts — a well-formed leaf/string that must decode `{:ok, _}` and a
  malformed input that must return `{:error, _}` (never crash/loop).
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    for cell <- [:valid_sexp, :invalid_sexp], do: {"serialize/decode", cell}
  end

  # Decode to {:ok, _}: bare int/float/atom leaves + quoted strings (incl. an
  # escaped quote, for take_string's escape clause) + the two structured leaves
  # `hole`/`absurd` (tuple terms → the assay re-encodes them, reaching enc's
  # hole/absurd clauses that the well_formed? gate keeps out of the roundtrip gen).
  @valid ["5", "-3", "0", "1.5", "-2.0", "foo", "Nat", "\"hi\"", "\"a\\\"b\"",
          "(hole \"h\")", "(absurd)"]

  # Decode to {:error, _}: unbalanced / non-atom-headed / truncated S-expressions,
  # trailing tokens, an unterminated string, an unknown node head, and case/ctor
  # bodies whose sub-terms fail to build (build_all / build_branches error paths).
  @invalid ["", ")", "(", "(foo", "(5 6)", "(int", "( )", "((", "))",
            "5 6", "\"abc", "(zzz)", "(ctor Foo (zzz))",
            "(case (var 0) (var 0) foo)", "(case (var 0) (var 0) (branch Z 0 (zzz)))"]

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
          cover_tag: label,
          payload: %{input: s},
          note: "decode probe (#{label})"
        )
      )
    end)
  end
end
