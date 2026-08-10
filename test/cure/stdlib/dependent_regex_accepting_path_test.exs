defmodule Cure.Stdlib.DependentRegexAcceptingPathTest do
  use ExUnit.Case, async: true

  alias Cure.Core.Env
  alias Cure.Elab.Program

  @source """
  mod RegexAcceptingPath
    use Std.Regex
    use Std.Regex.Proof

    fn one_next(_state: Bounded(1), char: Char) -> List(MachineState(1)) =
      [Accepted([EmitChar(char)], [])]

    fn one_machine() -> PatternMachine(1) =
      MkPatternMachine([Active(0, [], [])], one_next)

    fn start_state() -> ThreadState(1) = ThreadActive(0)

    fn one_step() -> AcceptingFrom(
      1,
      one_machine(),
      Cons('a', Nil()),
      Nil(),
      start_state(),
      Nil(),
      Nil(),
      Cons(CharacterEvidence('a'), Nil()),
      Cons(Observe('a'), Cons(Regular(EmitChar('a')), Nil()))
    ) =
      AcceptingNextAccepted(
        [EmitChar('a')],
        [],
        [CharacterEvidence('a')],
        [],
        [],
        ListMemberHere(),
        RoutineStep(
          EmitChar('a'),
          RoutineDone()
        ),
        AcceptingNow()
      )

    fn erase_path(@erased _path: AcceptingFrom(1, one_machine(), Cons('a', Nil()), Nil(), start_state(), Nil(), Nil(), Cons(CharacterEvidence('a'), Nil()), Cons(Observe('a'), Cons(Regular(EmitChar('a')), Nil())))) -> Unit = ()

    fn one_step_erased() -> Unit = erase_path(one_step())

    fn searched() -> AcceptingSearch(1, one_machine(), Cons('a', Nil()), Nil(), start_state(), Nil(), Nil()) =
      search_accepting_from(1, one_machine(), ['a'], [], start_state(), [], [])

    fn searched_machine() -> MachineAcceptingSearch(1, one_machine(), subject_initial_position(), Cons('a', Nil()), Nil()) =
      search_machine_acceptance(1, one_machine(), subject_initial_position(), ['a'], [])

    fn searched_empty() -> AcceptingSearch(1, one_machine(), Nil(), Nil(), start_state(), Nil(), Nil()) =
      search_accepting_from(1, one_machine(), [], [], start_state(), [], [])

    fn nullable_machine() -> PatternMachine(1) =
      MkPatternMachine(
        [Accepted([EmitUnit()], []), Active(0, [], [])],
        one_next
      )

    fn shortest_prefix() -> CertifiedPrefixSearch(1, nullable_machine(), subject_initial_position()) =
      search_first_machine_prefix(1, nullable_machine(), subject_initial_position(), ['a'])

    fn longest_prefix() -> CertifiedPrefixSearch(1, nullable_machine(), subject_initial_position()) =
      search_last_machine_prefix(1, nullable_machine(), subject_initial_position(), ['a'])

    fn zero_next(_state: Bounded(0), _char: Char) -> List(MachineState(0)) = []

    fn accepts_a(char: Char) -> Bool = char == 'a'

    fn predicate_extended_routine_case(
      prior: List(Evidence),
      captures: List(CaptureFrame),
      {output: List(Evidence)},
      {output_captures: List(CaptureFrame)},
      execution: ExtendedEvidenceRoutineExecution(
        transition_routine('a', Cons(EmitChar('a'), Nil())),
        prior,
        captures,
        output,
        output_captures
      )
    ) -> Encodes(CharC, output, prior) =
      predicate_transition_routine_encodes('a', execution)

    fn predicate_path_routine_case(
      prior: List(Evidence),
      captures: List(CaptureFrame),
      {path_evidence: List(Evidence)},
      {path_captures: List(CaptureFrame)},
      {path_final_evidence: List(Evidence)},
      {routine: List(ExtendedInstruction)},
      {output: List(Evidence)},
      {output_captures: List(CaptureFrame)},
      path: AcceptingFrom(1, predicate_pattern_machine(accepts_a), Cons('a', Nil()), Nil(), predicate_machine_thread(), path_evidence, path_captures, path_final_evidence, routine),
      execution: ExtendedEvidenceRoutineExecution(routine, prior, captures, output, output_captures)
    ) -> Encodes(CharC, output, prior) =
      predicate_path_routine_encodes(accepts_a, 'a', [], prior, captures, path, execution)

    fn empty_acceptance_case(
      prior: List(Evidence),
      captures: List(CaptureFrame),
      {final_evidence: List(Evidence)},
      {routine: List(ExtendedInstruction)},
      {output: List(Evidence)},
      {output_captures: List(CaptureFrame)},
      acceptance: MachineAcceptance(0, empty_pattern_machine(), subject_initial_position(), Nil(), Nil(), final_evidence, routine),
      execution: ExtendedEvidenceRoutineExecution(routine, prior, captures, output, output_captures)
    ) -> Encodes(UnitC, output, prior) =
      empty_machine_acceptance_encodes(subject_initial_position(), [], prior, captures, acceptance, execution)

    fn boundary_acceptance_case(
      constraint: BoundaryConstraint,
      position: InitialPosition,
      after_input: List(Char),
      @erased final_evidence: List(Evidence),
      @erased routine: List(ExtendedInstruction),
      acceptance: MachineAcceptance(0, boundary_pattern_machine(constraint), position, empty_characters(), after_input, final_evidence, routine)
    ) -> Encodes(UnitC, final_evidence, empty_evidence()) =
      boundary_machine_acceptance_encodes(constraint, position, after_input, final_evidence, routine, acceptance)

    fn predicate_acceptance_case(
      @erased final_evidence: List(Evidence),
      @erased routine: List(ExtendedInstruction),
      acceptance: MachineAcceptance(1, predicate_pattern_machine(accepts_a), subject_initial_position(), Cons('a', empty_characters()), empty_characters(), final_evidence, routine)
    ) -> Encodes(CharC, final_evidence, empty_evidence()) =
      predicate_machine_acceptance_encodes(accepts_a, 'a', empty_characters(), subject_initial_position(), final_evidence, routine, acceptance)

    fn end_machine() -> PatternMachine(0) =
      MkPatternMachine([Accepted([EmitUnit()], [subject_end_constraint()])], zero_next)

    fn end_before_suffix() -> MachineAcceptingSearch(0, end_machine(), subject_initial_position(), Nil(), Cons('a', Nil())) =
      search_machine_acceptance(0, end_machine(), subject_initial_position(), [], ['a'])

    fn end_at_subject_end() -> MachineAcceptingSearch(0, end_machine(), subject_initial_position(), Nil(), Nil()) =
      search_machine_acceptance(0, end_machine(), subject_initial_position(), [], [])

    fn extended_regular() -> ExtendedExecution =
      execute_extended_routine(regular_routine([EmitUnit()]), None(), [], [])

    fn extended_capture() -> ExtendedExecution =
      match execute_extended_routine(regular_routine([BeginCapture()]), None(), [], [])
        ExtendedExecution(current, evidence, captures) ->
          execute_extended_routine(transition_routine('a', [EmitChar('a'), EndCapture()]), current, evidence, captures)

    fn erase_extended_certificate(@erased _certificate: ExtendedRoutineExecution(Cons(Regular(EmitUnit()), Nil()), None(), Nil(), Nil(), None(), Cons(UnitEvidence(), Nil()), Nil())) -> Unit = ()

    fn extended_certificate_erased() -> Unit =
      erase_extended_certificate(certify_extended_routine([Regular(EmitUnit())], None(), [], []))
  """

  test "an accepting path fixes the winning thread's evidence in its result index" do
    assert {:ok, env} = Program.elaborate(@source)

    assert Env.get_def(env, :one_step)
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :one_step))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :predicate_extended_routine_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :predicate_path_routine_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :empty_acceptance_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :boundary_acceptance_case))
    assert Env.certified?(env, Env.resolve_key(env, env.defs, :predicate_acceptance_case))
  end

  test "the path proof is erased from the emitted runtime" do
    assert {:ok, module} = Cure.Compiler.compile_and_load(@source, emit_events: false)
    assert apply(module, :one_step_erased, []) == :unit
  end

  test "execution produces an accepting certificate with the winning evidence" do
    assert {:ok, module} = Cure.Compiler.compile_and_load(@source, emit_events: false)

    assert apply(module, :searched_machine, []) ==
             {:MachineAcceptingPath, [{:CharacterEvidence, ?a}], [{:Observe, ?a}, {:Regular, {:EmitChar, ?a}}]}

    assert apply(module, :searched_empty, []) == :NoAcceptingPath
  end

  test "certified prefix search preserves shortest and longest choices" do
    assert {:ok, module} = Cure.Compiler.compile_and_load(@source, emit_events: false)

    assert apply(module, :shortest_prefix, []) ==
             {:CertifiedPrefixPath, [], [?a], [:UnitEvidence], [{:Regular, :EmitUnit}]}

    assert apply(module, :longest_prefix, []) ==
             {:CertifiedPrefixPath, [?a], [], [{:CharacterEvidence, ?a}], [{:Observe, ?a}, {:Regular, {:EmitChar, ?a}}]}
  end

  test "a prefix certificate evaluates end anchors against the trailing subject" do
    assert {:ok, module} = Cure.Compiler.compile_and_load(@source, emit_events: false)

    assert apply(module, :end_before_suffix, []) == :MachineNoAcceptingPath

    assert apply(module, :end_at_subject_end, []) ==
             {:MachineAcceptingPath, [:UnitEvidence], [{:Regular, :EmitUnit}]}
  end

  test "extended routines preserve VM chunks and observe capture input" do
    assert {:ok, module} = Cure.Compiler.compile_and_load(@source, emit_events: false)

    assert apply(module, :extended_regular, []) ==
             {:ExtendedExecution, :none, [:UnitEvidence], []}

    assert apply(module, :extended_capture, []) ==
             {:ExtendedExecution, {:some, ?a}, [{:StringEvidence, {:String, [?a]}}], []}

    assert apply(module, :extended_certificate_erased, []) == :unit
  end
end
