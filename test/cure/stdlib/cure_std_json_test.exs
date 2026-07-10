defmodule :cure_std_json_test do
  use ExUnit.Case, async: true

  # Runtime shapes are the DEPENDENT-pipeline erasure of `Std.Json.Value`
  # (`Null | Bool(Bool) | Num(Float) | Str(String) | Arr(List(Value)) |
  # Obj(List(JsonPair))`): a constructor `C(a)` is `{:C, a}`, the nullary
  # `Null()` is the bare atom `:Null`, and `rec JsonPair(key, value)` is
  # `{:JsonPair, key, value}`.

  describe "encode/1" do
    test "encodes scalars" do
      assert :cure_std_json.encode(:Null) == "null"
      assert :cure_std_json.encode({:Bool, true}) == "true"
      assert :cure_std_json.encode({:Bool, false}) == "false"
      assert :cure_std_json.encode({:Num, 1.0}) == "1.0"
      assert :cure_std_json.encode({:Str, "hi"}) == ~s("hi")
    end

    test "encodes arrays and objects" do
      assert :cure_std_json.encode({:Arr, [{:Num, 1.0}, {:Num, 2.0}]}) == "[1.0,2.0]"
      assert :cure_std_json.encode({:Obj, [{:JsonPair, "a", {:Num, 1.0}}]}) == ~s({"a":1.0})
    end

    test "encodes a non-whole float" do
      # Regression: `float_to_string` passed `{:compact, []}` to
      # `:erlang.float_to_binary/2`, whose valid option is the bare atom
      # `:compact`. Any fractional Num raised ArgumentError. Whole-number floats
      # took the other branch, so it went unnoticed.
      assert :cure_std_json.encode({:Num, 1.5}) == "1.5"
    end

    test "encodes large and tiny floats without crashing, round-trip exact" do
      # The fixed-decimal formatting (`{:decimals, N}`) both CRASHED for large
      # magnitudes (|f| >= ~1e254) and silently lost precision (fixed digits
      # after the point, not significant digits). `[:short]` is crash-free and
      # round-trips exactly.
      for f <- [1.0e300, 1.7976931348623157e308, 1.0e-16, 5.0e-324,
                0.30000000000000004, 1.0000000000000002] do
        s = :cure_std_json.encode({:Num, f})
        assert is_binary(s)
        # `decode(encode(f))` must recover the same float.
        assert {:Ok, {:Num, ^f}} = :cure_std_json.decode(s)
      end
    end
  end

  describe "decode/1" do
    test "parses valid JSON into the Value ADT" do
      assert {:Ok, {:Obj, _}} = :cure_std_json.decode(~s({"a":1,"b":[true, null, "s"]}))
    end

    test "returns an error string on bad input" do
      assert {:Error, _msg} = :cure_std_json.decode("{bogus")
    end

    test "null decodes to the nullary Null(), the bare atom :Null" do
      # `Null` is a nullary Cure constructor and erases to the bare atom `:Null`
      # on the dependent pipeline. Returning a bare `:null` (lowercase) or a
      # tuple would produce a `Value` Cure could not pattern-match.
      assert {:Ok, :Null} = :cure_std_json.decode("null")
      assert :cure_std_json.encode(:Null) == "null"
    end

    test "an object decodes to JsonPair-tagged pairs" do
      assert {:Ok, {:Obj, [{:JsonPair, "a", {:Num, 1.0}}]}} = :cure_std_json.decode(~s({"a":1}))
    end
  end

  describe "num_of_int/1" do
    test "widens an integer to a Num Value" do
      assert {:Num, 5.0} = :cure_std_json.num_of_int(5)
    end
  end
end
