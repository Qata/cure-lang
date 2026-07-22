defmodule Cure.Stdlib.CharStringBehaviorTest do
  use ExUnit.Case, async: false

  alias Antigen.Backend.StreamData, as: Property
  alias Antigen.Gen

  @char :"Cure.Std.Char"
  @string :"Cure.Std.String"
  @runs [max_runs: 500, max_run_time: :infinity]

  defp char(name, args), do: apply(@char, name, args)
  defp string(name, args), do: apply(@string, name, args)

  defp scalar_gen do
    Gen.bind(Gen.integer(0, 0x10FFFF), fn cp ->
      Gen.return(if cp in 0xD800..0xDFFF, do: 0xFFFD, else: cp)
    end)
  end

  defp chars_gen(0), do: Gen.return([])

  defp chars_gen(size) do
    Gen.bind(Gen.member_of(~c"aBéß٣ _-"), fn head ->
      Gen.bind(chars_gen(size - 1), fn tail -> Gen.return([head | tail]) end)
    end)
  end

  defp string_case_gen do
    Gen.bind(Gen.integer(0, 12), fn size ->
      Gen.bind(chars_gen(size), fn chars ->
        Gen.bind(Gen.integer(-2, 15), fn count -> Gen.return({chars, count}) end)
      end)
    end)
  end

  test "character classification covers Unicode category families" do
    assert char(:is_ascii, [?A])
    refute char(:is_ascii, [?é])
    assert char(:ascii_value, [?A]) == {:some, 65}
    assert char(:ascii_value, [?é]) == :none

    assert char(:is_letter, [?é])
    assert char(:is_punctuation, [?!])
    assert char(:is_newline, [0x2028])
    assert char(:is_whitespace, [0xA0])
    assert char(:is_horizontal_space, [0x2007])
    refute char(:is_horizontal_space, [0x2028])
    assert char(:is_vertical_space, [0x2028])
    refute char(:is_vertical_space, [0x2007])
    assert char(:is_symbol, [?©])
    assert char(:is_math_symbol, [?+])
    assert char(:is_currency_symbol, [?€])
    assert char(:is_cased, [?ǅ])
    assert char(:is_uppercase, [?É])
    assert char(:is_lowercase, [?é])
  end

  test "character casing is Unicode-aware and permits expansion" do
    assert char(:lowercased, [?É]) == ~c"é"
    assert char(:uppercased, [?ß]) == ~c"SS"
    assert char(:ascii_lowercased, [?A]) == ?a
    assert char(:ascii_lowercased, [?É]) == ?É
  end

  test "numbers, hexadecimal values, equality, and scalar ordering" do
    assert char(:is_number, [?½])
    refute char(:is_whole_number, [?½])
    assert char(:whole_number_value, [?½]) == :none
    assert char(:is_whole_number, [?Ⅻ])
    assert char(:whole_number_value, [?Ⅻ]) == {:some, 12}
    assert char(:whole_number_value, [?٣]) == {:some, 3}

    assert char(:is_hex_digit, [?Ｆ])
    assert char(:hex_digit_value, [?Ｆ]) == {:some, 15}
    assert char(:hex_digit_value, [?g]) == :none

    assert char(:same, [?a, ?a])
    refute char(:same, [?a, ?b])
    assert char(:less_than, [?a, ?b])
    assert char(:between, [?m, ?a, ?z])
    refute char(:between, [?A, ?a, ?z])
  end

  test "Swift-style string conveniences handle boundaries and Unicode" do
    assert string(:lowercased, [~c"CAFÉ"]) == ~c"café"
    assert string(:uppercased, [~c"straße"]) == ~c"STRASSE"
    assert string(:has_prefix, [~c"cure", ~c"cu"])
    assert string(:has_suffix, [~c"cure", ~c"re"])
    assert string(:contains, [~c"café", ?é])
    assert string(:first, [~c"cure"]) == {:some, ?c}
    assert string(:last, [~c"cure"]) == {:some, ?e}
    assert string(:first, [[]]) == :none
    assert string(:last, [[]]) == :none
    assert string(:prefix, [~c"cure", 2]) == ~c"cu"
    assert string(:suffix, [~c"cure", 2]) == ~c"re"
    assert string(:drop_first, [~c"cure", 2]) == ~c"re"
    assert string(:drop_last, [~c"cure", 2]) == ~c"cu"
    assert string(:prefix, [~c"cure", -1]) == []
    assert string(:drop_first, [~c"cure", -1]) == ~c"cure"
    assert string(:split_on, [~c",a,,b,", ?,]) == [~c"a", ~c"b"]
  end

  test "character functions agree with the Unicode reference over generated scalars" do
    assert :ok =
             Property.check_all(scalar_gen(), @runs, fn cp ->
               properties = Unicode.properties(cp)
               category = Unicode.category(cp)
               ascii_value = char(:ascii_value, [cp])
               whole_value = char(:whole_number_value, [cp])
               hex_value = char(:hex_digit_value, [cp])
               expected_space = cp in [9, 10, 11, 12, 13, 0x85] or category in [:Zs, :Zl, :Zp]
               expected_horizontal =
                 cp in [0x0009, 0x0020, 0x00A0, 0x1680, 0x180E, 0x202F, 0x205F, 0x3000] or
                   cp in 0x2000..0x200A
               expected_vertical = cp in [0x000A, 0x000B, 0x000C, 0x000D, 0x0085, 0x2028, 0x2029]

               char(:same, [cp, cp]) and
                 char(:is_ascii, [cp]) == (cp <= 0x7F) and
                 ascii_value == if(cp <= 0x7F, do: {:some, cp}, else: :none) and
                 char(:less_than, [cp, 0x10FFFF]) == (cp < 0x10FFFF) and
                 char(:between, [cp, 0, 0x10FFFF]) and
                 char(:lowercased, [cp]) == :string.lowercase([cp]) and
                 char(:uppercased, [cp]) == :string.uppercase([cp]) and
                 char(:is_letter, [cp]) == (:alphabetic in properties) and
                 char(:is_punctuation, [cp]) == (category in [:Pc, :Pd, :Pe, :Pf, :Pi, :Po, :Ps]) and
                 char(:is_newline, [cp]) == (cp in [10, 11, 12, 13, 0x85, 0x2028, 0x2029]) and
                 char(:is_whitespace, [cp]) == expected_space and
                 char(:is_horizontal_space, [cp]) == expected_horizontal and
                 char(:is_vertical_space, [cp]) == expected_vertical and
                 char(:is_symbol, [cp]) == (category in [:Sc, :Sk, :Sm, :So]) and
                 char(:is_math_symbol, [cp]) == (:math in properties) and
                 char(:is_currency_symbol, [cp]) == (category == :Sc) and
                 char(:is_cased, [cp]) == (:cased in properties) and
                 char(:is_uppercase, [cp]) == (:uppercase in properties) and
                 char(:is_lowercase, [cp]) == (:lowercase in properties) and
                 char(:is_number, [cp]) == (category in [:Nd, :Nl, :No]) and
                 char(:is_whole_number, [cp]) == match?({:some, _}, whole_value) and
                 char(:is_hex_digit, [cp]) == (:hex_digit in properties) and
                 match?({:some, value} when value in 0..15, hex_value) == (:hex_digit in properties)
             end)
  end

  test "string slicing obeys prefix/drop and suffix/drop decomposition laws" do
    assert :ok =
             Property.check_all(string_case_gen(), @runs, fn {chars, count} ->
               prefix = string(:prefix, [chars, count])
               suffix = string(:suffix, [chars, count])
               first_rest = string(:drop_first, [chars, count])
               last_rest = string(:drop_last, [chars, count])
               expected_first = if(chars == [], do: :none, else: {:some, hd(chars)})
               expected_last = if(chars == [], do: :none, else: {:some, List.last(chars)})

               string(:concat, [prefix, first_rest]) == chars and
                 string(:concat, [last_rest, suffix]) == chars and
                 string(:has_prefix, [chars, prefix]) and
                 string(:has_suffix, [chars, suffix]) and
                 string(:first, [chars]) == expected_first and
                 string(:last, [chars]) == expected_last and
                 string(:lowercased, [chars]) == :string.lowercase(chars) and
                 string(:uppercased, [chars]) == :string.uppercase(chars)
             end)
  end
end
