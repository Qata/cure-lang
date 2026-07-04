defmodule Antigen.Assays.Serialization do
  @moduledoc """
  `serialize/roundtrip` — a metamorphic vertical. `Cure.Core.Serialize` must be
  LOSSLESS: `decode(encode(t)) == {:ok, t}` for every well-formed term. A mismatch
  (or a decode error) is an infection — the corpus/replay pipeline would silently
  corrupt or drop that term. Exercises the full encode AND decode path in-process
  (the coverage campaign banks but never replays, so decode is otherwise cold).
  """
  alias Antigen.Challenge
  alias Cure.Core.Serialize

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :serialize, payload: %{term: t}}) do
    encoded = Serialize.encode(t)

    case Serialize.decode(encoded) do
      {:ok, ^t} -> :ok
      {:ok, other} -> {:violation, {:roundtrip_mismatch, t, other}}
      {:error, reason} -> {:violation, {:decode_failed, t, reason}}
    end
  end

  # Decode robustness: `decode` must be total — well-formed input decodes,
  # malformed input errors cleanly (never crashes/loops).
  def run(%Challenge{kind: :decode_probe, label: label, payload: %{input: s}}) do
    case {label, Serialize.decode(s)} do
      {:valid_sexp, {:ok, _}} -> :ok
      {:invalid_sexp, {:error, _}} -> :ok
      {_, got} -> {:violation, {:decode_probe, label, s, got}}
    end
  end
end
