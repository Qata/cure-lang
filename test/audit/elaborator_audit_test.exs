defmodule Cure.Audit.ElaboratorTest do
  @moduledoc """
  Audit findings for `lib/cure/elab/elaborator.ex` (the bidirectional
  elaborator: surface Cure AST -> `Cure.Core` terms). The elaborator is NOT
  the TCB — `Cure.Core.Kernel.check/3` re-checks every assembled top-level
  function body (`declarations.ex` `elaborate_body(...) ; Kernel.check(ctx,
  body_term, return_value)`) — so most elaborator bugs degrade to spurious
  rejections or crashes, not proofs of False. The finding below (EL1/EL2) is
  the dangerous exception: a case where the kernel happily TYPE-CHECKS the
  malformed term, because the bug doesn't produce an ill-typed term, it
  produces a *differently-typed-but-still-well-typed* term than the source
  actually denotes — a silent semantic-drift accept, exactly the worst-case
  category this audit is chartered to find.

  Cleared (traced, not bugs):
    * `elaborate_match/6` and `elaborate_with/8` never call `Kernel.check`
      internally — but every caller path bottoms out in `declarations.ex`'s
      single top-level `Kernel.check` after `elaborate_body`, which
      recursively re-verifies the whole assembled term (standard
      check-once-at-the-top bidirectional elaborator design, matching
      Idris2/Lean4). Not a gap.
    * The legacy `Elaborator.elaborate/2` (arity 2) and its private
      `elaborate_expr/3` family (incl. the char-literal clause near the end
      of the file that builds `{:bounded_lit, v}` with no `Bounded`-family
      registration check) are dead code, unreachable from the real
      `Cure.Elab.Program.elaborate/1` pipeline (only exercised by their own
      legacy test file). Noted, not reported as a live finding.
  """
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  # ---------------------------------------------------------------------
  # EL1: `elaborate_let_block/5` desugars `let x = e ⏎ rest` by SURFACE
  # substitution (`subst_surface_var/3`) — `rest[x := e]` — UNLESS a later
  # binder shadows `x`, in which case it falls back to a real bind-once
  # β-redex `(λx:T. rest) e` (elaborator.ex ~3937-3976, the documented
  # "Bind-once β-redex" fix per project history). Shadowing is detected by
  # `binds_any?/2` (elaborator.ex ~4014-4030), which has exactly ONE special
  # case: `{:match_arm, meta, body}` nodes, pulling bound names out of
  # `Keyword.get(meta, :pattern)` when the pattern is a `{:function_call, _,
  # args}` (a plain constructor pattern).
  #
  # `binds_any?` has NO case for `{:lambda, meta, [body]}`. Per the parser
  # (`parser.ex:2657`, confirmed by grep), a lambda's parameter names live in
  # `meta[:params]`, not among its traversed `children` (`[body]`). So
  # `binds_any?` walks straight past a lambda into its body without ever
  # seeing that the lambda's OWN parameter shadows the name being checked.
  # When that lambda parameter has the same name as an outer `let`-bound
  # variable, `binds_any?` returns `false` (wrongly: no shadowing detected),
  # so `elaborate_let_block` takes the blind-substitution branch and
  # `subst_surface_var` (which walks generically into `children`, i.e. into
  # the lambda's body) replaces every occurrence of the name INSIDE the
  # lambda body too — even though those occurrences are the lambda's own
  # bound variable, not the outer `let`'s.
  #
  # Concretely, `let x = Z() ⏎ ap(fn(x) -> S(x), arg)`: the inner `fn(x) ->
  # S(x)` should be `\x. S(x)` (Idris/Lean/Agda: a nested binder always
  # shadows an outer one — capture-avoiding substitution is non-negotiable).
  # Instead the elaborator rewrites the lambda's surface AST to `fn(x) ->
  # S(Z())` before elaborating it, producing a lambda that IGNORES its own
  # argument and always returns `S(Z())`. That lambda is perfectly
  # well-typed (`(Nat) -> Nat`), so the kernel accepts it — the resulting
  # program silently computes the wrong function instead of being rejected
  # or computing the source's actual denotation.
  test "EL1: a lambda parameter that shadows an outer let-bound name is not captured by let's surface substitution" do
    src =
      @nat <>
        "  fn ap(f: (Nat) -> Nat, x: Nat) -> Nat = f(x)\n" <>
        "  fn g() -> Nat =\n    let x = Z()\n    ap(fn(x) -> S(x), S(S(Z())))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Audit.El1", functions: [:ap, :g])

    # fn(x) -> S(x) applied to S(S(Z())) must be S(S(S(Z()))) — the lambda's
    # own parameter, not the outer let's Z(), must flow into its body.
    assert apply(mod, :g, []) == {:S, {:S, {:S, :Z}}}
  end

  # ---------------------------------------------------------------------
  # EL2: the same root cause (`binds_any?`'s match_arm clause recognizes
  # ONLY `{:function_call, _, args}` constructor patterns) also misses the
  # single most basic pattern shape: a bare-variable (catch-all/binding)
  # match arm pattern, e.g. `match e  w -> body` (used throughout this
  # codebase's own tests, e.g. `test/cure/elab/tuple_pattern_test.exs`'s
  # `w -> w`). When that bound name is `w = x` and coincides with an outer
  # `let x = ...`, the arm's pattern is `{:variable, _, "x"}` — which
  # `Keyword.get(meta, :pattern)` sees, but the `case` in `binds_any?`'s
  # match_arm clause only matches `{:function_call, _pmeta, args}`; a bare
  # `{:variable, ...}` pattern falls to the `_ -> []` default, so the arm's
  # own binder is again invisible to shadow detection. `subst_surface_var`
  # then rewrites every `x` in the arm body — including the pattern-bound
  # one — to the outer let's right-hand side, discarding whatever the
  # scrutinee actually matched.
  #
  # This is arguably more dangerous than EL1: a bare catch-all pattern
  # reusing an in-scope name is an extremely ordinary thing to write (it is
  # literally the idiom already exercised by this codebase's own
  # `tuple_pattern_test.exs`), not a contrived edge case.
  test "EL2: a bare-variable match-arm pattern that shadows an outer let-bound name is not captured by let's surface substitution" do
    src =
      @nat <>
        "  fn g() -> Nat =\n    let x = Z()\n    match S(S(Z()))\n      x -> S(x)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Audit.El2", functions: [:g])

    # The catch-all arm binds `x` to the scrutinee S(S(Z())); the body must
    # see THAT `x`, not the outer let's Z() — so the result is S(S(S(Z()))),
    # not S(Z()).
    assert apply(mod, :g, []) == {:S, {:S, {:S, :Z}}}
  end
end
