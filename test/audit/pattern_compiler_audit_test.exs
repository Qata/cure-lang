defmodule Cure.Audit.PatternCompilerTest do
  @moduledoc """
  Audit findings for `lib/cure/compiler/pattern_compiler.ex` (the classic
  MetaAST-pattern -> Erlang-abstract-form compiler used by `match`, `let`,
  multi-clause function heads, comprehension generators, and catch arms via
  `Cure.Compiler.Codegen`'s `compile_pattern/2` delegate).

  PC2-PC4 compile real Cure source through the exact
  Lexer -> Parser -> Codegen -> BeamWriter pipeline that
  `test/audit/codegen_audit_test.exs` already established as this project's
  idiom for a full compile-and-run round trip (`eval_module_main!/1,3`,
  itself copied from `test/cure/compiler/bin_segment_test.exs`); this file's
  `compile_module!/1` is the same round trip stopping short of the final
  `apply/3`, needed because several findings call more than one exported
  function on the loaded module. PC1 additionally needs the type checker in
  the loop (it asserts the
  checker *rejects* a program), so it goes through the full
  `Cure.Compiler.compile_and_load/1` orchestrator instead (also an
  established idiom, see `test/cure/compiler/integration_test.exs`). PC5
  calls `Cure.Compiler.PatternCompiler.compile/2` directly, the unit-level
  idiom already used throughout `test/cure/compiler/pattern_compiler_test.exs`.

  Every test asserts the value/behavior the source *should* produce per
  `docs/MATCH.md` / `docs/PATTERNS.md`; today each one is RED.

  Do not run this file automatically as part of the trusted-suite gate; it
  documents open findings, not yet-fixed regressions.
  """
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Compiler.{Lexer, Parser, Codegen, BeamWriter, PatternCompiler}

  # ==========================================================================
  # PC1 / PC2: a bare PascalCase identifier in pattern position (no `()`) is
  # documented as a hard *syntax error* -- `docs/MATCH.md` §21 "Non-Goals":
  # "Implicit constructor conjuration... a bare PascalCase identifier in
  # pattern position is *not* a nullary constructor; it is a syntax error.
  # Nullary constructors require explicit empty parentheses." The dedicated
  # diagnostic even exists and is fully written up:
  # `lib/cure/compiler/errors.ex:846` ("E074: Bare Nullary Constructor in
  # Pattern (E-MATCH-NULLARY-NEEDS-PARENS)"), example `None` -> "write
  # None()". But `grep -rn E074 lib/` finds exactly one hit -- the errors.ex
  # catalog entry itself. No stage of the pipeline (parser, `Types.Checker`,
  # `Types.PatternChecker`, or `PatternCompiler`) ever raises it.
  #
  # In `PatternCompiler.do_compile/2` (pattern_compiler.ex:90-91), the
  # dispatch clause for ANY `{:variable, _meta, name}` node --
  # unconditionally, regardless of case -- calls
  # `compile_variable_pattern/2` (pattern_compiler.ex:207-227), which just
  # binds a fresh Erlang variable that matches anything. There is no
  # `constructor?/1` check on this path at all. Contrast this with
  # `Codegen.compile_variable/2` (codegen.ex:1093-1110), which handles the
  # exact same bare-PascalCase-identifier shape in EXPRESSION position and
  # explicitly special-cases it: "A bare PascalCase identifier in expression
  # position is a reference to a nullary ADT constructor" -- the pattern
  # side has no analogous check, an outright omission, not a deliberate
  # asymmetry.
  #
  # Idris2/Agda/Lean sidestep this ambiguity lexically: constructors live in
  # a namespace disjoint from local bindings, so a bare `Nil`/`None` in
  # pattern position is unambiguously the zero-arity constructor -- no
  # parens required. Cure chose the opposite, explicit design (require
  # `()`) specifically *because* its pattern grammar cannot tell a
  # capitalized binder from a capitalized constructor otherwise -- but never
  # implemented the enforcement that design requires, so it silently falls
  # back to "capitalized name binds a variable", the one interpretation the
  # spec calls out by name as forbidden.
  test "PC1: `None` (no parens) in pattern position is rejected at compile time (E074), not silently accepted" do
    source = """
    mod NullaryBug1
      type Opt = Some(Int) | None

      fn describe(o: Opt) -> Int =
        match o
          None -> 0
          Some(x) -> x
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source)
  end

  test "PC2: pattern_compiler.ex must not compile a bare nullary-constructor pattern to an unconditional wildcard that shadows every later arm" do
    source = """
    mod NullaryBug2
      type Opt = Some(Int) | None

      fn mk_some(x: Int) -> Opt = Some(x)

      fn describe(o: Opt) -> Int =
        match o
          None -> 0
          Some(x) -> x
    """

    module = compile_module!(source)
    some_5 = module.mk_some(5)

    # `Some(5) -> x` is the only arm whose head shape actually matches a
    # `Some` value; the bare `None` arm compiles today to
    # `compile_variable_pattern("None", state)` -- a plain variable binder
    # -- so it wins unconditionally as the FIRST arm and `describe` always
    # returns 0, never reaching the `Some(x)` clause.
    assert module.describe(some_5) == 5
  end

  # ==========================================================================
  # PC3: as-patterns (`name @ pattern`) have no handler anywhere in
  # `PatternCompiler.do_compile/2`. The parser produces
  # `{:as_pattern, meta, [name, inner]}` for this surface form
  # (parser.ex:2027-2038, `maybe_wrap_as/2`) both at a match arm's top level
  # and nested inside constructor arguments; the dependent-elaborator
  # pathway (`elab/elaborator.ex:2452-2493`, `desugar_as_patterns/1` /
  # `strip_as_patterns/1`) explicitly understands and strips this node, and
  # the differential oracle suite pins its runtime semantics
  # (`test/oracle/match/verdicts.json` "mt11_as_pattern" /
  # "mt12_nested_as_pattern"). The CLASSIC pipeline's `PatternCompiler`,
  # however, has no `:as_pattern` clause in its `case` dispatch
  # (pattern_compiler.ex:78-141) at all, so it falls through to the final
  # catch-all:
  #
  #     _other -> {{:var, state.line, :_}, state}
  #
  # This drops the ENTIRE pattern -- both the outer as-binding and the
  # inner sub-pattern (`Some(x)` here) are never compiled at all, so the
  # arm becomes an unconditional wildcard that matches every scrutinee
  # value, not just ones shaped like the inner pattern.
  #
  # In Idris2/Agda/Lean, an as-pattern (`x@p` / Idris `x@p`) always
  # (a) binds the whole scrutinee to the named variable AND (b) compiles
  # the wrapped pattern `p` exactly as if it had appeared bare -- Maranget's
  # algorithm treats an as-binding as a let-around-the-column, never as an
  # opaque node that disables matching on that column.
  test "PC3: an as-pattern (`whole @ Some(x)`) must still match only Some-shaped values, not every value" do
    source = """
    mod AsPatternBug
      type Opt = Some(Int) | None

      fn mk_none() -> Opt = None()

      fn classify(o: Opt) -> Int =
        match o
          whole @ Some(x) -> 1
          None() -> 0
    """

    module = compile_module!(source)
    none_value = module.mk_none()

    # `None()` should fall through the first arm (it isn't `Some`-shaped)
    # and hit the second arm, returning 0. Because `whole @ Some(x)`
    # compiles to a bare wildcard today, it swallows the None() value too.
    assert module.classify(none_value) == 0
  end

  # ==========================================================================
  # PC4: range patterns (`1..10 -> ...`) are documented as rejected outright
  # -- `docs/PATTERNS.md` "What is not supported (yet)": "Range patterns
  # (`1..10 -> ...`). Compile-time rejected." and `docs/MATCH.md` §21:
  # "Pattern-level effects... [range patterns] MAY be added in minor
  # revisions" (i.e. not yet present as a real pattern shape). Nothing in
  # `Types.Checker`, `Types.PatternChecker`, or `PatternCompiler` actually
  # rejects a `{:range, ...}` node reaching pattern position (grep for
  # `range_in_pattern` / an equivalent guard across `lib/cure/` turns up
  # nothing). Because match-arm patterns are parsed with the general
  # expression parser (`parse_match_arm/1`, parser.ex:2020-2025, calls
  # `parse_expr/2` directly -- the same mechanism that lets `whole @ ...`
  # as-patterns and bare constructors reach pattern position), `1..10`
  # parses cleanly into a `{:range, meta, [from, to]}` pattern node.
  #
  # `PatternCompiler.do_compile/2`'s dedicated clause for this shape
  # (pattern_compiler.ex:132-136) says, in its own comment, "Best effort:
  # compile as wildcard and let the type checker flag it" -- but the type
  # checker never flags it, so the "best effort" fallback is the only
  # thing that actually runs: an unconditional wildcard that matches every
  # value, in range or not.
  test "PC4: a range pattern (`1..10 -> ...`) must not match values outside the range" do
    source = """
    mod RangeBug
      fn classify(x: Int) -> Int =
        match x
          1..10 -> 1
          _ -> 0
    """

    module = compile_module!(source)

    # 50 is well outside 1..10, so the second (wildcard) arm should fire.
    assert module.classify(50) == 0
  end

  # ==========================================================================
  # PC5: `compile_call_pattern/4` (pattern_compiler.ex:348-364) dispatches a
  # `{:function_call, meta, args}` pattern node to
  # `compile_constructor_pattern/4` only when `constructor?(name)` is true
  # -- a heuristic that solely checks whether the first character is
  # uppercase (pattern_compiler.ex:547-554, duplicated verbatim in
  # `Types.PatternChecker` at pattern_checker.ex:414-421, in `Types.Checker`
  # at checker.ex:2325-2332, and in `Codegen` at codegen.ex:2040). Any
  # OTHER call-shaped pattern -- e.g. a typo'd lowercase constructor name
  # like `some(x)` instead of `Some(x)`, which the general expression
  # parser (see PC4's comment on `parse_match_arm/1`) happily parses into
  # the exact same `{:function_call, ...}` AST shape -- falls to the final
  # branch:
  #
  #     true -> {{:var, line, :_}, state}
  #
  # silently discarding the whole call (including its argument `x`, which
  # is never bound) and replacing it with a bind-everything wildcard,
  # instead of surfacing that the pattern shape is unrecognized. Maranget's
  # algorithm (and Idris2/Lean's pattern elaborators) operate over a
  # *closed* set of recognized head shapes per specialization step; an
  # input outside that set is a hard compile error, never silently
  # defaulted to a wildcard row -- a wildcard row is only ever introduced
  # deliberately, from an actual `_`/variable pattern in the source.
  test "PC5: a lowercase, non-record function_call pattern (e.g. a typo `some(x)` for `Some(x)`) must not silently compile to a bind-everything wildcard" do
    # `some(x)` -- lowercase first letter, `record: false` -- is neither a
    # record pattern nor recognized as a constructor by `constructor?/1`.
    ast = {:function_call, [name: "some", line: 1], [{:variable, [], "x"}]}

    {form, _state} = PatternCompiler.compile(ast, %Codegen{})

    # Today `form` is `{:var, _, :_}` -- the input shape leaves no trace at
    # all in the compiled output.
    refute match?({:var, _, :_}, form)
  end

  # -- Helpers ---------------------------------------------------------------
  # Same pipeline as `eval_module_main!/1,3` in `test/audit/codegen_audit_test.exs`
  # (itself copied from `test/cure/compiler/bin_segment_test.exs`), the
  # established idiom for a full compile-and-run round trip through the
  # classic codegen pipeline with the type checker out of the loop -- just
  # returning the loaded module instead of immediately `apply/3`-ing one
  # function, since several findings here call more than one exported
  # function on the loaded module.

  defp compile_module!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    {:ok, forms, _warnings} = Codegen.compile_module(ast, emit_events: false)
    {:ok, module} = BeamWriter.compile_and_load(forms)
    module
  end
end
