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
end
