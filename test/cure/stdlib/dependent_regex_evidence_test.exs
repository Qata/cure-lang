defmodule Cure.Stdlib.DependentRegexEvidenceTest do
  use ExUnit.Case, async: false

  setup_all do
    source = """
    mod RegexEvidenceRuntime
      use Std.Regex

      fn same(expected: Char) -> Char -> Bool =
        fn(actual) -> Std.Char.same(expected, actual)

      fn atom(char: Char) -> Pattern(CharC) = PatternPredicate(same(char))
      fn ab() -> Pattern(PairC(CharC, CharC)) = PatternConcat(atom('a'), atom('b'))
      fn ambiguous() -> Pattern(ChoiceC(CharC, CharC)) = PatternAlternate(atom('a'), atom('a'))
      fn many() -> Pattern(ListC(CharC)) = PatternRepeat(atom('a'))
      fn greedy_pair() -> Pattern(PairC(ListC(CharC), CharC)) = PatternConcat(many(), atom('a'))
      fn grouped() -> Pattern(StringC) = PatternGroup(ab())
      fn nested_group() -> Pattern(StringC) = PatternGroup(PatternGroup(ab()))

      fn pair_evidence() -> Option(List(Evidence)) = pattern_evidence(ab(), "ab")
      fn ambiguous_evidence() -> Option(List(Evidence)) = pattern_evidence(ambiguous(), "a")
      fn list_evidence() -> Option(List(Evidence)) = pattern_evidence(many(), "aa")
      fn greedy_evidence() -> Option(List(Evidence)) = pattern_evidence(greedy_pair(), "aa")
      fn group_evidence() -> Option(List(Evidence)) = pattern_evidence(grouped(), "ab")
      fn nested_group_evidence() -> Option(List(Evidence)) = pattern_evidence(nested_group(), "ab")
      fn failed_evidence() -> Option(List(Evidence)) = pattern_evidence(ab(), "aa")
      fn shortest_prefix() -> Option(EvidencePrefix) = pattern_prefix_evidence(many(), "aaab", false)
      fn longest_prefix() -> Option(EvidencePrefix) = pattern_prefix_evidence(many(), "aaab", true)
      fn parsed_pair() -> Option(Tuple(Char, Char)) = parse_pattern_full(ab(), "ab")
      fn parsed_left() -> Option(Choice(Char, Char)) = parse_pattern_full(ambiguous(), "a")
      fn parsed_list() -> Option(List(Char)) = parse_pattern_full(many(), "aaa")
      fn parsed_group() -> Option(String) = parse_pattern_full(grouped(), "ab")
      fn malformed_pair_encoding() -> Option(Tuple(Char, Char)) =
        extract_complete_encoding(
          decode_pattern_encoding(ab(), [PairEvidence(), CharacterEvidence('b')])
        )
      fn trailing_pair_encoding() -> Option(Tuple(Char, Char)) =
        extract_complete_encoding(
          decode_pattern_encoding(ab(), [PairEvidence(), CharacterEvidence('b'), CharacterEvidence('a'), UnitEvidence()])
        )

    end
    """

    assert {:ok, runtime_module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: runtime_module}
  end

  test "concatenation emits postfix pair evidence", %{runtime_module: module} do
    assert apply(module, :pair_evidence, []) ==
             {:some, [:PairEvidence, {:CharacterEvidence, ?b}, {:CharacterEvidence, ?a}]}
  end

  test "ordered deduplication retains the left alternative's evidence", %{runtime_module: module} do
    assert apply(module, :ambiguous_evidence, []) ==
             {:some, [:LeftEvidence, {:CharacterEvidence, ?a}]}
  end

  test "repetition emits balanced list evidence", %{runtime_module: module} do
    assert apply(module, :list_evidence, []) ==
             {:some,
              [
                :EndListEvidence,
                {:CharacterEvidence, ?a},
                {:CharacterEvidence, ?a},
                :BeginListEvidence
              ]}
  end

  test "greedy repetition keeps the consuming path needed by a following atom", %{runtime_module: module} do
    assert apply(module, :greedy_evidence, []) ==
             {:some,
              [
                :PairEvidence,
                {:CharacterEvidence, ?a},
                :EndListEvidence,
                {:CharacterEvidence, ?a},
                :BeginListEvidence
              ]}
  end

  test "groups replace child evidence with the exact consumed extent", %{runtime_module: module} do
    assert apply(module, :group_evidence, []) == {:some, [{:StringEvidence, ~c"ab"}]}
    assert apply(module, :nested_group_evidence, []) == {:some, [{:StringEvidence, ~c"ab"}]}
  end

  test "failed full matches produce no evidence", %{runtime_module: module} do
    assert apply(module, :failed_evidence, []) == :none
  end

  test "prefix modes choose the first or last accepting extent", %{runtime_module: module} do
    assert apply(module, :shortest_prefix, []) ==
             {:some, {:EvidencePrefix, [:EndListEvidence, :BeginListEvidence], ~c"aaab"}}

    assert apply(module, :longest_prefix, []) ==
             {:some,
              {:EvidencePrefix,
               [
                 :EndListEvidence,
                 {:CharacterEvidence, ?a},
                 {:CharacterEvidence, ?a},
                 {:CharacterEvidence, ?a},
                 :BeginListEvidence
               ], ~c"b"}}
  end

  test "shape-indexed extraction returns Pattern values without runtime casts", %{runtime_module: module} do
    assert apply(module, :parsed_pair, []) == {:some, {?a, ?b}}
    assert apply(module, :parsed_left, []) == {:some, {:ChoseLeft, ?a}}
    assert apply(module, :parsed_list, []) == {:some, ~c"aaa"}
    assert apply(module, :parsed_group, []) == {:some, ~c"ab"}
  end

  test "the certified decoder rejects malformed and trailing evidence", %{runtime_module: module} do
    assert apply(module, :malformed_pair_encoding, []) == :none
    assert apply(module, :trailing_pair_encoding, []) == :none
  end

  test "shape certificates are erased from emitted decoder functions" do
    module = :"Cure.Std.Regex"

    {:ok, set} =
      Cure.Compiler.Artifacts.open_verified_set(
        kind: :stdlib,
        candidates: Cure.Stdlib.Paths.beam_dirs()
      )

    artifact =
      set.modules["Std.Regex"].artifacts
      |> Enum.find(&(&1.module == Atom.to_string(module)))

    beam = File.read!(Path.join(set.artifact_root, artifact.path))
    {:beam_file, ^module, _exports, _attrs, _info, functions} = :beam_disasm.file(beam)

    decoder_names = [
      :decode_atomic_evidence,
      :decode_many_prior,
      :decode_pattern_encoding,
      :extract_complete_decoding
    ]

    decoder_code =
      for {:function, name, _arity, _label, instructions} <- functions,
          name in decoder_names,
          do: instructions

    binary = :erlang.term_to_binary(decoder_code)
    refute binary =~ "Encodes"
    refute binary =~ "EvidenceAppend"
  end
end
