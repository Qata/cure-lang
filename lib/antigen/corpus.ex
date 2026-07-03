defmodule Antigen.Corpus do
  @moduledoc "Committed, never-pruned, generator-independent stores (spec §7). Replay runs the kernel, not the generator."
  alias Antigen.{Challenge, Coverage}
  alias Cure.Core.Serialize

  @marker "antigen-record"

  @doc "Encode a challenge to a one-line record, storing its antibody dedup key."
  @spec encode_record(Challenge.t()) :: String.t()
  def encode_record(%Challenge{} = c), do: encode_record(c, dedup_key(c, :antibody))

  @doc """
  Encode a challenge, storing `key` verbatim in the `key=` field. `append/3`
  passes the exact key it dedups on, so seeds (coverage key) and antibodies
  (assay+terms key) both round-trip their own dedup identity — see the `seen?`
  path.
  """
  @spec encode_record(Challenge.t(), String.t()) :: String.t()
  def encode_record(%Challenge{} = c, key) do
    {scaffold, pieces} = Challenge.to_pieces(c)

    piece_str =
      pieces
      |> Enum.map(fn {id, t} -> "#{id}::#{Serialize.encode(t)}" end)
      |> Enum.join(";;")

    Enum.join(
      [
        @marker,
        "kind=#{c.kind}",
        "assay=#{c.assay}",
        "label=#{c.label}",
        "seed=#{c.seed || "-"}",
        "note=#{enc_note(c.note)}",
        "scaffold=#{encode_scaffold(scaffold)}",
        "key=#{Base.encode64(key)}",
        "pieces=#{piece_str}"
      ],
      "\t"
    )
  end

  @spec decode_record(String.t()) :: {:ok, Challenge.t()} | {:error, term()}
  def decode_record(line) do
    # Force-intern the closed kind/label/name set BEFORE `decode_pieces` runs
    # `Serialize.decode` (which calls `String.to_existing_atom` on family/ctor
    # names like `:Dec`/`:Causal`). Loading `Challenge` interns every literal in
    # its `@known_atoms`; without this, a replay in a process that has not yet
    # loaded `Challenge` (async suite ordering) fails to decode. See spec §7.
    _ = Challenge.__known_atoms__()

    with [@marker | fields] <- String.split(String.trim_trailing(line, "\n"), "\t"),
         m <- Map.new(fields, fn f -> List.to_tuple(String.split(f, "=", parts: 2)) end),
         {:ok, pieces} <- decode_pieces(m["pieces"]) do
      kind = String.to_existing_atom(m["kind"])
      label = String.to_existing_atom(m["label"])
      seed = if m["seed"] == "-", do: nil, else: String.to_integer(m["seed"])
      scaffold = decode_scaffold(m["scaffold"] || "-")
      note = if legacy_record?(m["pieces"]), do: dec_opt(m["note"]), else: dec_note(m["note"])
      {:ok, Challenge.from_pieces(kind, m["assay"], label, seed, note, scaffold, pieces)}
    else
      other -> {:error, {:bad_record, other}}
    end
  rescue
    e -> {:error, e}
  end

  @doc "Encode arbitrary (non-Term) challenge metadata for the `scaffold=` field. `%{}` → `\"-\"`."
  @spec encode_scaffold(map()) :: String.t()
  def encode_scaffold(scaffold) when scaffold == %{}, do: "-"
  def encode_scaffold(scaffold), do: Base.encode64(:erlang.term_to_binary(scaffold))

  @doc "Decode the `scaffold=` field. `:safe` refuses to mint new atoms on decode — see the safety note in the plan."
  @spec decode_scaffold(String.t()) :: map()
  def decode_scaffold("-"), do: %{}
  def decode_scaffold(b64), do: :erlang.binary_to_term(Base.decode64!(b64), [:safe])

  @spec append(String.t(), Challenge.t(), String.t()) :: :appended | :duplicate
  def append(path, %Challenge{} = c, dedup_key) do
    File.mkdir_p!(Path.dirname(path))

    if seen?(path, dedup_key) do
      :duplicate
    else
      # single append syscall — atomic per record (spec §7.1)
      File.write!(path, encode_record(c, dedup_key) <> "\n", [:append])
      :appended
    end
  end

  @spec stream(String.t()) :: Enumerable.t()
  def stream(path) do
    if File.exists?(path) do
      path
      |> File.stream!()
      |> Stream.map(fn line ->
        case decode_record(line) do
          {:ok, c} -> {:ok, c}
          {:error, reason} -> {:decode_error, String.trim(line), reason}
        end
      end)
    else
      []
    end
  end

  @spec dedup_key(Challenge.t(), :antibody | :seed) :: String.t()
  def dedup_key(%Challenge{} = c, :seed), do: Coverage.key_string(Coverage.key(c))

  def dedup_key(%Challenge{assay: a} = c, :antibody) do
    {_s, pieces} = Challenge.to_pieces(c)
    a <> "|" <> (pieces |> Enum.map(fn {id, t} -> id <> Serialize.encode(t) end) |> Enum.join("|"))
  end

  defp seen?(path, key) do
    File.exists?(path) and
      (path |> File.stream!() |> Enum.any?(fn line -> extract_key(line) == key end))
  end

  defp extract_key(line) do
    line
    |> String.split("\t")
    |> Enum.find_value(fn f ->
      case String.split(f, "=", parts: 2) do
        ["key", b64] -> Base.decode64!(String.trim(b64))
        _ -> nil
      end
    end)
  rescue
    _ -> nil
  end

  defp decode_pieces(nil), do: {:error, :no_pieces}
  defp decode_pieces(""), do: {:ok, []}

  defp decode_pieces(str) do
    str
    |> String.split(";;")
    |> Enum.reduce_while({:ok, []}, fn piece, {:ok, acc} ->
      case String.split(piece, "::", parts: 2) do
        [id, body] ->
          decoded =
            case body do
              "(" <> _ -> Serialize.decode(body)                       # new: inline s-expr
              _ -> Serialize.decode(Base.decode64!(body))              # legacy: Base64-wrapped
            end

          case decoded do
            {:ok, t} -> {:cont, {:ok, [{id, t} | acc]}}
            err -> {:halt, err}
          end

        _ ->
          {:halt, {:error, {:bad_piece, piece}}}
      end
    end)
    |> case do
      {:ok, ps} -> {:ok, Enum.reverse(ps)}
      err -> err
    end
  end

  # dec_opt: legacy Base64 note decode (still used by the legacy-record branch).
  defp dec_opt("-"), do: nil
  defp dec_opt(b64), do: Base.decode64!(b64)

  # A record is legacy iff its (first) piece body is Base64, i.e. does not start
  # with "(" — every Serialize.encode output starts with "(", Base64 never does.
  # Empty/absent pieces ⇒ treat as new-format (plaintext note); real records
  # always carry ≥1 term piece, so this default is not exercised by live data.
  defp legacy_record?(nil), do: false
  defp legacy_record?(""), do: false
  defp legacy_record?(pieces_str) do
    case String.split(pieces_str, ";;", parts: 2) do
      [first | _] ->
        case String.split(first, "::", parts: 2) do
          [_id, "(" <> _] -> false
          [_id, _body] -> true
          _ -> false
        end
    end
  end

  # note: nil -> "-"; a literal "-" -> "%2D"; else percent-escape %/tab/newline.
  # `%` MUST be escaped first (its own escape introduces further `%`).
  defp enc_note(nil), do: "-"
  defp enc_note("-"), do: "%2D"
  defp enc_note(s) do
    s
    |> String.replace("%", "%25")
    |> String.replace("\t", "%09")
    |> String.replace("\n", "%0A")
  end

  defp dec_note("-"), do: nil
  defp dec_note(s) do
    s
    |> String.replace("%2D", "-")
    |> String.replace("%09", "\t")
    |> String.replace("%0A", "\n")
    |> String.replace("%25", "%")
  end
end
