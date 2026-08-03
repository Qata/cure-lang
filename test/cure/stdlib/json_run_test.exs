defmodule Cure.Stdlib.JsonRunTest do
  use ExUnit.Case, async: true

  @json :"Cure.Std.Json"

  test "decodes objects, arrays, exact decimals, and surrogate pairs in Cure" do
    source = ~c"{\"n\":-1.2300e+4,\"s\":\"\\uD83D\\uDE00\",\"a\":[true,null]}"

    assert {:ok,
            {:Object,
             [
               {:ObjectMember, ~c"n", {:Number, {:DecimalNumber, {:DecimalLiteral, ~c"-1.2300e+4"}}}},
               {:ObjectMember, ~c"s", {:String, [0x1F600]}},
               {:ObjectMember, ~c"a", {:Array, [{:Boolean, true}, :Null]}}
             ]}} = apply(@json, :decode, [source])
  end

  test "keeps the three JSON number categories distinct" do
    assert {:ok, {:Number, {:NaturalNumber, {:NaturalLiteral, ~c"12", 12}}}} =
             apply(@json, :decode, [~c"12"])

    assert {:ok, {:Number, {:IntegerNumber, {:IntegerLiteral, ~c"-12", -12}}}} =
             apply(@json, :decode, [~c"-12"])

    assert {:ok, {:Number, {:DecimalNumber, {:DecimalLiteral, ~c"12.00"}}}} =
             apply(@json, :decode, [~c"12.00"])
  end

  test "rejects malformed numbers and trailing input" do
    for source <- [~c"01", ~c"1.", ~c"1e", ~c"1 true"] do
      assert {:error, _reason} = apply(@json, :decode, [source])
    end
  end

  test "encodes the full-name Value representation without the Elixir shim" do
    value =
      {:Object,
       [
         {:ObjectMember, ~c"message", {:String, ~c"a\n\"b"}},
         {:ObjectMember, ~c"number", {:Number, {:DecimalNumber, {:DecimalLiteral, ~c"1.2300"}}}}
       ]}

    assert ~c"{\"message\":\"a\\n\\\"b\",\"number\":1.2300}" = apply(@json, :encode, [value])
  end

  test "Decimal decoding routes exact JSON numbers through literal protocols" do
    source = """
    mod TypedJsonDecimal
      use Std.Json
      use Std.Decimal
      use Std.Result

      fn value() -> Result(Decimal, DecodeError) =
        assert_type decode_as("1.2300") : Result(Decimal, DecodeError)
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert {:ok, {:Finite, {:FiniteDecimal, :Positive, 12300, -4}}} = apply(module, :value, [])
  end
end
