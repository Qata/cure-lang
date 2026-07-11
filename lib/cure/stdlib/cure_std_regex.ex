defmodule :cure_std_regex do
  @moduledoc """
  Runtime helpers for `Std.Regex` (v0.27.0).

  Wraps OTP's `:re` module.

  Runtime shapes are the DEPENDENT-pipeline erasure. A constructor `C(a, b)`
  erases to `{:C, a, b}`, a nullary `C()` to the bare atom `:C`, and a record
  `rec R` to `{:R, field1, …}` in declaration order:

    * `Result(Regex, RegexError)` → `{:Ok, regex}` / `{:Error, {:InvalidPattern, msg}}`
    * `Option(Matched)`           → `{:Some, matched}` / `:None`
    * `rec Matched(whole, groups)` → `{:Matched, whole, groups}`

  The compiled `Regex` is opaque — Cure never pattern-matches it, only threads
  it back into these entry points — so it stays an internal struct map. Match
  entry points also accept a raw pattern string, compiled on every call.
  """

  @struct_key :__struct__

  # -- Compile ----------------------------------------------------------------

  def compile(pattern) when is_binary(pattern) do
    # `{:ok, re}` here is `:re.compile/2`'s own result, not a Cure Result.
    case :re.compile(pattern, [:unicode]) do
      {:ok, re} -> {:Ok, new_regex(re)}
      {:error, reason} -> {:Error, {:InvalidPattern, format_reason(reason)}}
    end
  end

  def compile(_), do: {:Error, {:InvalidPattern, "pattern must be a string"}}

  def compile_bang(pattern) when is_binary(pattern) do
    case compile(pattern) do
      {:Ok, regex} -> regex
      {:Error, {:InvalidPattern, msg}} -> raise ArgumentError, "invalid regex: #{msg}"
    end
  end

  # -- Predicates -------------------------------------------------------------

  def is_match(regex, input) do
    case resolve(regex) do
      {:ok, re} -> do_is_match(re, input)
      :error -> false
    end
  end

  defp do_is_match(re, input) when is_binary(input) do
    case :re.run(input, re, [{:capture, :none}]) do
      :match -> true
      :nomatch -> false
    end
  end

  defp do_is_match(_, _), do: false

  # -- Single match -----------------------------------------------------------

  def run(regex, input) when is_binary(input) do
    case resolve(regex) do
      {:ok, re} ->
        # `{:match, …}` / `:nomatch` are `:re.run/3`'s own results.
        case :re.run(input, re, [{:capture, :all, :binary}]) do
          {:match, [whole | groups]} ->
            {:Some, new_match(whole, groups)}

          {:match, []} ->
            :None

          :nomatch ->
            :None
        end

      :error ->
        :None
    end
  end

  def run(_, _), do: :None

  # -- All matches ------------------------------------------------------------

  def scan(regex, input) when is_binary(input) do
    case resolve(regex) do
      {:ok, re} ->
        case :re.run(input, re, [:global, {:capture, :all, :binary}]) do
          {:match, matches} ->
            Enum.map(matches, fn
              [whole | groups] -> new_match(whole, groups)
              [] -> new_match("", [])
            end)

          :nomatch ->
            []
        end

      :error ->
        []
    end
  end

  def scan(_, _), do: []

  # -- Replace ----------------------------------------------------------------

  def replace(regex, input, replacement)
      when is_binary(input) and is_binary(replacement) do
    case resolve(regex) do
      {:ok, re} ->
        :re.replace(input, re, replacement, [:global, {:return, :binary}])

      :error ->
        input
    end
  end

  def replace(_, input, _) when is_binary(input), do: input

  # -- Split ------------------------------------------------------------------

  def split(regex, input) when is_binary(input) do
    case resolve(regex) do
      {:ok, re} ->
        :re.split(input, re, [{:return, :binary}])

      :error ->
        [input]
    end
  end

  # -- Internals --------------------------------------------------------------

  defp new_regex(compiled) do
    %{@struct_key => :regex, handle: compiled}
  end

  # `rec Matched(whole, groups)` → `{:Matched, whole, groups}` in field order.
  defp new_match(whole, groups) when is_binary(whole) and is_list(groups) do
    {:Matched, whole, groups}
  end

  defp resolve(%{@struct_key => :regex, handle: re}), do: {:ok, re}

  defp resolve(pattern) when is_binary(pattern) do
    case :re.compile(pattern, [:unicode]) do
      {:ok, re} -> {:ok, re}
      {:error, _} -> :error
    end
  end

  defp resolve(_), do: :error

  # `:re.compile/2` only reports compile errors as `{reason_string,
  # position}` tuples, so that is the only shape we need to format.
  defp format_reason({reason, _position}), do: to_string(reason)
end
