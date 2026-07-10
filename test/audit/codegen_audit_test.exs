defmodule Cure.Audit.CodegenTest do
  @moduledoc """
  Audit findings for `lib/cure/compiler/codegen.ex` (the classic MetaAST ->
  Erlang-abstract-format code generator) and its pattern-lowering delegate
  `lib/cure/compiler/pattern_compiler.ex`.

  Every test below compiles real Cure source through the exact
  Lexer -> Parser -> Codegen -> BeamWriter pipeline used by
  `test/cure/compiler/bin_segment_test.exs` (`eval_module_main!/1`, copied
  verbatim), loads the resulting module, and calls it. Each test asserts the
  value/behavior the source *should* produce; today each one is RED (either
  a wrong value or a runtime crash where the source has no reason to crash).

  Do not run this file automatically as part of the trusted-suite gate; it
  documents open findings, not yet-fixed regressions.
  """
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Compiler.{Lexer, Parser, Codegen, BeamWriter}

  # ==========================================================================
  # CG1 / CG2: variable shadowing (`let x = ...` re-declaring an
  # already-bound name) is silently miscompiled.
  #
  # `compile_assignment/4` (codegen.ex:1391) lowers a `let` binding's LHS
  # through `compile_pattern/2`, which delegates to
  # `PatternCompiler.compile_variable_pattern/2` (pattern_compiler.ex:207).
  # That function has exactly one branch for "name already in state.vars":
  # the branch meant for *non-linear pattern* repeats, e.g. `[x, x]`, where
  # a second occurrence of `x` in the SAME pattern must equal the first
  # (Prolog/Erlang pattern-matching semantics -- correct there). It mints a
  # fresh Erlang variable ("V__dup_<name>_<counter>") and an equality guard,
  # then re-inserts the *original* atom into `state.vars` (pattern_compiler.ex:217).
  #
  # `compile_assignment/4` calls this same path for ordinary sequential
  # `let` shadowing (a completely different source construct: re-binding a
  # name to a NEW value for the rest of the block, which the type checker's
  # `Env.extend/3`-based `bind_pattern_vars` (checker.ex:2025) explicitly
  # permits and expects subsequent references to see). Two bugs compound:
  #
  #   1. `compile_assignment/4` (codegen.ex:1391-1406) unconditionally
  #      clears `state.pattern_guards` both before AND after the pattern
  #      compile, so the equality guard PatternCompiler attached is silently
  #      discarded -- it never gets attached to anything.
  #   2. `state.vars[name]` is left pointing at the OLD atom (the "keep the
  #      original binding" behavior that is correct for `[x, x]` patterns),
  #      so the `let` appears to succeed (it binds a fresh, unused Erlang
  #      variable to the new value) but every later reference to the name
  #      -- compiled by `compile_variable/2` (codegen.ex:1093), which reads
  #      `mangle_var(name)` directly and never consults `state.vars` at all
  #      -- keeps resolving to the FIRST binding.
  #
  # Net effect: `let x = 1; let x = 2; x` computes 1, not 2. And because the
  # fresh-var counter that's supposed to disambiguate repeated dups
  # (`fresh_var_atom/2`, pattern_compiler.ex:229) reads
  # `state.pattern_dup_counter` but that field is declared
  # (codegen.ex:41) and read (pattern_compiler.ex:233) yet NEVER incremented
  # anywhere in the codebase (`grep -rn pattern_dup_counter lib/` finds only
  # the declaration and the two reads), every dup within one function
  # collapses onto the SAME atom "V__dup_x_0". A third shadow of the same
  # name therefore tries to re-match an Erlang variable that is already
  # bound to the *second* shadow's value against the *third* shadow's value
  # -- a `{badmatch, _}` crash.
  test "CG1: `let x = 1; let x = 2; x` evaluates to the shadowed value 2, not the stale first binding" do
    assert eval_module_main!("""
           mod ShadowLetStale
             fn main() -> Int =
               let x = 1
               let x = 2
               x
           """) == 2
  end

  test "CG2: a third `let` shadow of the same name does not crash with badmatch" do
    assert eval_module_main!("""
           mod ShadowLetTripleCrash
             fn main() -> Int =
               let x = 1
               let x = 2
               let x = 3
               x
           """) == 3
  end

  # ==========================================================================
  # CG3: augmented assignment (`x += 1`) always crashes with `{badmatch, _}`
  # instead of incrementing the binding.
  #
  # `compile_augmented_assignment/5` (codegen.ex:1410-1421) compiles the LHS
  # variable reference through `do_compile_expr/2` -> `compile_variable/2`
  # (codegen.ex:1093), which deterministically produces `{:var, Line, V_x}`
  # for the name "x" (it does NOT mint a fresh Erlang variable). It then
  # builds `RHS = {:op, Line, ErlOp, {:var,_,V_x}, ValForm}` and emits
  # `{:match, Line, {:var,_,V_x}, RHS}` -- i.e. Erlang source
  # `V_x = V_x + 1`. Because `V_x` was already bound by the preceding
  # `let x = ...`, this is a re-match against an already-bound Erlang
  # variable, not a rebinding: Erlang requires the freshly computed RHS to
  # be term-identical to the EXISTING value of V_x, which is never true for
  # any nontrivial augmented assignment (`X = X + 1` requires old-X ==
  # new-X, i.e. old-X == old-X + 1, impossible for integers). Every `+=`/
  # `-=`/`*=`/`/=` on a previously-bound variable therefore raises
  # `{badmatch, NewValue}` at runtime instead of updating the binding.
  test "CG3: `x += 1` increments x instead of crashing with badmatch" do
    assert eval_module_main!("""
           mod AugAssignCrash
             fn main() -> Int =
               let x = 1
               x += 1
               x
           """) == 2
  end

  # ==========================================================================
  # CG4: `/` unconditionally lowers to Erlang's `div` operator regardless of
  # operand type, crashing with `{badarith, _}` on Float operands.
  #
  # `cure_op_to_erlang/1` (codegen.ex:2025) maps Cure's `:/ ` to Erlang's
  # `:div` unconditionally. `Types.Checker.do_infer/2` for `:binary_op`
  # (checker.ex:1000-1021, `:arithmetic` category) accepts ANY pair of
  # numeric operands for `/` -- `Type.numeric?/1` covers both Int and
  # Float, and the result type is `Type.join(lt, rt)`, so `Float / Float`
  # (and mixed Int/Float) type-checks and is expected to produce a Float
  # quotient. Erlang's `div/2` BIF requires both operands to be integers
  # and raises `error:badarith` for any Float operand (unlike `+`/`-`/`*`,
  # which Erlang overloads for both Int and Float and which codegen passes
  # through unchanged via `cure_op_to_erlang(op), do: op`). So any
  # well-typed Cure program that divides two Floats crashes instead of
  # computing a quotient.
  test "CG4: `3.0 / 2.0` computes the Float quotient 1.5 instead of crashing with badarith" do
    assert eval_module_main!("""
           mod FloatDivBadarith
             fn main() -> Float =
               3.0 / 2.0
           """) == 1.5
  end

  # ==========================================================================
  # CG5: `return expr` (early return) always propagates an uncaught
  # `throw({:cure_return, Value})` instead of returning `Value` from the
  # enclosing function.
  #
  # `compile_early_return/4` (codegen.ex:1824-1832) lowers `return expr` to
  # `throw({:cure_return, ExprForm})`. Searching the entire `lib/` tree for
  # the literal atom `cure_return` (`grep -rn cure_return lib/`) finds
  # exactly one hit: this emission site. No function-form wrapper, no
  # top-level `try ... catch {:cure_return, V} -> V end`, and no other
  # compiler pass installs a catch for this tag anywhere in the pipeline.
  # A `return` that isn't already inside an explicit, user-written `try`
  # block (a normal, idiomatic early exit from an `if`/`match` arm) is
  # therefore an unconditionally uncaught exception: it unwinds straight
  # through the enclosing function's caller instead of making that function
  # return the early value.
  test "CG5: `if x > 0 then return 1 else 0` returns 1 from the function instead of raising an uncaught throw" do
    assert eval_module_main!(
             """
             mod EarlyReturnUncaught
               fn classify(x: Int) -> Int = if x > 0 then return 1 else 0
             """,
             :classify,
             [5]
           ) == 1
  end

  # -- Helpers ---------------------------------------------------------------
  # Copied verbatim from test/cure/compiler/bin_segment_test.exs, which
  # already establishes this as the project's idiom for a full
  # compile-and-run round trip through the classic codegen pipeline.

  defp eval_module_main!(source), do: eval_module_main!(source, :main, [])

  defp eval_module_main!(source, fun, args) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    {:ok, forms, _warnings} = Codegen.compile_module(ast, emit_events: false)
    {:ok, module} = BeamWriter.compile_and_load(forms)
    apply(module, fun, args)
  end
end
