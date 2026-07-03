defmodule Antigen.CorpusTest do
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Corpus}

  @tmp "tmp/antigen_test"

  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  test "encode → decode round-trips a stub challenge identically (C2 stability)" do
    c =
      Challenge.new(
        kind: :stub,
        assay: "stub",
        label: :none,
        payload: %{term: {:app, {:lam, {:type, 0}, {:var, 0}}, {:type, 0}}},
        seed: 42,
        note: "hi"
      )

    line = Corpus.encode_record(c)
    refute String.contains?(line, "\n")
    assert {:ok, c2} = Corpus.decode_record(line)
    assert c2.payload.term == c.payload.term
    assert c2.assay == "stub" and c2.seed == 42 and c2.note == "hi"
  end

  test "append is idempotent on the dedup key" do
    path = Path.join(@tmp, "corpus.sexp")
    c = Challenge.stub({:type, 0})
    key = Corpus.dedup_key(c, :antibody)
    assert :appended == Corpus.append(path, c, key)
    assert :duplicate == Corpus.append(path, c, key)
    assert File.read!(path) |> String.split("\n", trim: true) |> length() == 1
  end

  test "stream surfaces a decode error as a distinct entry and keeps going" do
    path = Path.join(@tmp, "corpus.sexp")
    Corpus.append(path, Challenge.stub({:type, 0}), Corpus.dedup_key(Challenge.stub({:type, 0}), :antibody))
    File.write!(path, File.read!(path) <> "this-is-not-a-record\n")
    results = Corpus.stream(path) |> Enum.to_list()
    assert Enum.any?(results, &match?({:ok, %Challenge{}}, &1))
    assert Enum.any?(results, &match?({:decode_error, _, _}, &1))
  end

  test "scaffold round-trips non-Term metadata through the record line (proves Phase-2 def_group/family carry-through)" do
    scaffold = %{"focus" => ["f", "g"], "arity" => 2}
    line = Corpus.encode_scaffold(scaffold)
    refute String.contains?(line, "\t") or String.contains?(line, "\n")
    assert Corpus.decode_scaffold(line) == scaffold
  end

  test "an empty scaffold encodes to the `-` sentinel and decodes back to an empty map" do
    assert Corpus.encode_scaffold(%{}) == "-"
    assert Corpus.decode_scaffold("-") == %{}
  end

  alias Cure.Core.Serialize

  test "term pieces are stored as readable s-expressions, not Base64" do
    c =
      Challenge.new(
        kind: :stub, assay: "stub", label: :none,
        payload: %{term: {:ctor, :vcons, [{:ctor, :Z, []}, {:ctor, :Z, []}, {:ctor, :vnil, []}]}},
        seed: 7, note: "n"
      )

    line = Corpus.encode_record(c)
    # the piece is the literal Serialize s-expr, inline in the line
    assert line =~ "term::(ctor vcons (ctor Z) (ctor Z) (ctor vnil))"
    refute line =~ "term::" <> Base.encode64(Serialize.encode(c.payload.term))
    assert {:ok, c2} = Corpus.decode_record(line)
    assert c2.payload.term == c.payload.term
  end

  test "decode_record still reads a legacy Base64 piece (dual-read)" do
    term = {:app, {:lam, {:type, 0}, {:var, 0}}, {:type, 0}}
    # hand-build a legacy record: pieces = id::Base64(Serialize.encode(term))
    legacy =
      Enum.join(
        [
          "antigen-record", "kind=stub", "assay=stub", "label=none", "seed=1",
          "note=aGk=", "scaffold=-", "key=" <> Base.encode64("k"),
          "pieces=term::" <> Base.encode64(Serialize.encode(term))
        ],
        "\t"
      )

    assert {:ok, c} = Corpus.decode_record(legacy)
    assert c.payload.term == term
  end

  test "note is stored as readable plaintext and round-trips special chars" do
    for note <- ["negative occurrence: Bad left of an arrow", "has\ttab and % and\nnewline", "-", "plain", nil] do
      c = Challenge.new(kind: :stub, assay: "stub", label: :none,
                        payload: %{term: {:type, 0}}, seed: 1, note: note)
      line = Corpus.encode_record(c)
      refute String.contains?(line, "\n"), "record must stay one line for note=#{inspect(note)}"
      assert {:ok, c2} = Corpus.decode_record(line)
      assert c2.note == note
    end
  end

  test "a real (non-nil) note is human-readable in the line (not Base64)" do
    c = Challenge.new(kind: :stub, assay: "stub", label: :none,
                      payload: %{term: {:type, 0}}, seed: 1, note: "negative occurrence")
    line = Corpus.encode_record(c)
    assert line =~ "note=negative occurrence"
    refute line =~ "note=" <> Base.encode64("negative occurrence")
  end

  test "legacy Base64 note decodes to the original text (format inferred from Base64 pieces)" do
    term = {:type, 0}
    legacy =
      Enum.join(
        ["antigen-record", "kind=stub", "assay=stub", "label=none", "seed=1",
         "note=" <> Base.encode64("hello world"), "scaffold=-", "key=" <> Base.encode64("k"),
         "pieces=term::" <> Base.encode64(Serialize.encode(term))],
        "\t"
      )

    assert {:ok, c} = Corpus.decode_record(legacy)
    assert c.note == "hello world"
    assert c.payload.term == term
  end
end
