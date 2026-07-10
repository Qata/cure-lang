defmodule :cure_std_json do
  @moduledoc """
  Runtime helpers for `Std.Json` (v0.23.0).

  These Erlang-style functions are the targets of the `@extern` bridges
  in `lib/std/json.cure`. Every function here is pure and stateless.

  Runtime shapes are the DEPENDENT-pipeline erasure of `Std.Json.Value`
  (`Null | Bool(Bool) | Num(Float) | Str(String) | Arr(List(Value)) |
  Obj(List(JsonPair))`). A constructor `C(a)` erases to `{:C, a}`, the nullary
  `Null()` to the bare atom `:Null`, and `rec JsonPair(key, value)` to
  `{:JsonPair, key, value}`:

    * `:Null`, `{:Bool, b}`, `{:Num, f}`, `{:Str, s}`
    * `{:Arr, values}`, `{:Obj, [{:JsonPair, key, value}, …]}`
    * `decode` returns `Result(Value, String)` → `{:Ok, value}` / `{:Error, msg}`
  """

  # -- Encoder -----------------------------------------------------------------

  @doc "Encode a `Std.Json.Value` to a JSON string."
  def encode(:Null), do: "null"
  def encode({:Bool, true}), do: "true"
  def encode({:Bool, false}), do: "false"
  def encode({:Num, f}) when is_float(f), do: float_to_string(f)
  def encode({:Num, i}) when is_integer(i), do: Integer.to_string(i)
  def encode({:Str, s}) when is_binary(s), do: Cure.Project.Json.encode(s)

  def encode({:Arr, xs}) when is_list(xs) do
    inner = Enum.map_join(xs, ",", &encode/1)
    "[" <> inner <> "]"
  end

  def encode({:Obj, pairs}) when is_list(pairs) do
    inner =
      Enum.map_join(pairs, ",", fn {:JsonPair, k, v} ->
        Cure.Project.Json.encode(k) <> ":" <> encode(v)
      end)

    "{" <> inner <> "}"
  end

  def encode(other), do: raise(ArgumentError, "cannot encode: #{inspect(other)}")

  # -- Decoder -----------------------------------------------------------------

  @doc "Decode a JSON string into a `Std.Json.Value`."
  def decode(src) when is_binary(src) do
    # `{:ok, …}` / `{:error, …}` here are `Cure.Project.Json`'s own results.
    case Cure.Project.Json.decode(src) do
      {:ok, term} -> {:Ok, to_value(term)}
      {:error, {reason, pos}} -> {:Error, :erlang.iolist_to_binary(~c"#{reason} at offset #{pos}")}
    end
  end

  defp to_value(nil), do: :Null
  defp to_value(true), do: {:Bool, true}
  defp to_value(false), do: {:Bool, false}
  defp to_value(n) when is_integer(n), do: {:Num, n * 1.0}
  defp to_value(n) when is_float(n), do: {:Num, n}
  defp to_value(s) when is_binary(s), do: {:Str, s}

  defp to_value(list) when is_list(list) do
    {:Arr, Enum.map(list, &to_value/1)}
  end

  defp to_value(map) when is_map(map) do
    {:Obj, Enum.map(map, fn {k, v} -> {:JsonPair, k, to_value(v)} end)}
  end

  # -- Construction helpers ---------------------------------------------------

  @doc "Widen a Cure Int into a JSON number Value."
  def num_of_int(n) when is_integer(n), do: {:Num, n * 1.0}

  # -- Private ----------------------------------------------------------------

  defp float_to_string(f) when is_float(f) do
    cond do
      f == trunc(f) -> :erlang.float_to_binary(f, [{:decimals, 1}])
      # `:compact` is a bare-atom option; `{:compact, []}` is invalid and raises.
      true -> :erlang.float_to_binary(f, [:compact, {:decimals, 15}])
    end
  end
end
