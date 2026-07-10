defmodule Cure.Audit.DeclarationsTest do
  @moduledoc """
  Red tests from a targeted audit of `lib/cure/elab/declarations.ex`
  (top-level declaration elaboration: data/record/typealias/def/interface
  signatures). Each test encodes one specific, currently-wrong behavior and
  asserts the CORRECT one, per Idris2/Agda/Lean parity. See each test's
  comment for the finding, why it is wrong, and what the reference languages
  do instead.
  """
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.Env
  alias Cure.Elab.{Declarations, Program}

  # Mirrors `test/cure/elab/declarations_test.exs`'s helper: parse `src` and
  # fold every top-level declaration through `Declarations.elaborate/2`
  # directly (no `Program.check_ast` front-end scans), starting from
  # `Env.empty()`.
  defp decls(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)

    case ast do
      {:block, _, items} -> items
      single -> [single]
    end
  end

  defp elaborate_all(src) do
    Enum.reduce_while(decls(src), {:ok, Env.empty()}, fn decl, {:ok, env} ->
      case Declarations.elaborate(decl, env) do
        {:ok, env2} -> {:cont, {:ok, env2}}
        err -> {:halt, err}
      end
    end)
  end

  # --------------------------------------------------------------------------
  # D1: a typealias whose RHS is not a Type is silently accepted.
  #
  # `elaborate({:type_annotation, meta, [rhs]}, env)` (declarations.ex, the
  # `:type_annotation` clause) lowers the RHS to a Core term and installs it
  # UNCHECKED via `Env.add_def(env, name, {:type, 0}, rhs_core, [])` — the
  # declared type is hardcoded to `{:type, 0}` regardless of what `rhs_core`
  # actually is. The only kernel re-check that ever runs is the
  # `maybe_certify/2` call immediately after, which delegates to
  # `Kernel.validate_certificate/2` — but `maybe_certify/2` is:
  #
  #     case Kernel.validate_certificate(env, name) do
  #       {:ok, certified} -> certified
  #       {:error, _} -> env
  #     end
  #
  # For a FUNCTION body (`elaborate_real_body/3`), `Kernel.check/3` runs and
  # its error is PROPAGATED through a `with` before `maybe_certify/2` is ever
  # reached — `maybe_certify` there only turns off future δ-unfolding when the
  # (already well-typed) body merely fails to certify as *total*, which is the
  # documented, legitimate "opaque to δ, never a soundness hole" case.
  #
  # For a typealias, there is no such prior `Kernel.check`: `validate_certificate`
  # IS the first and only type check of `rhs_core`, and any failure it reports —
  # including "the RHS does not even have kind Type" — is swallowed the same way
  # a mere non-termination verdict would be. The bogus def stays registered
  # (uncertified but present), and `Declarations.elaborate/2` reports `{:ok, _}`
  # as if the alias were well-formed.
  #
  # `type Bad = Z` aliases `Bad` to the Nat constructor `Z`, whose type is
  # `Nat`, not `Type` — Idris (`Bad : Type; Bad = Z`) and Lean
  # (`def Bad : Type := Z`) both reject this outright at the declaration site.
  # Cure should too.
  test "D1: a typealias RHS that is not a Type is rejected, not silently kept as an inert alias" do
    src = "type Nat = Z | S(Nat)\ntype Bad = Z\n"
    assert {:error, _} = elaborate_all(src)
  end

  # --------------------------------------------------------------------------
  # D2: an `interface`'s synthesized dictionary record can silently steal (or
  # be stolen by) a same-named ordinary type declaration in the SAME module.
  #
  # `Cure.Elab.Interface.elaborate/2` realises `interface Equatable(a) ...` as
  # a single-constructor record family named `:Equatable` via
  # `Declarations.declare_record/4` (declarations.ex) — an ordinary call into
  # the SAME family/ctor registration machinery (`Inductive.declare/3`) that a
  # `type`/`indexed type`/`rec` declaration uses, and which is a bare
  # `Map.put` with no existence check (`lib/cure/core/inductive.ex`
  # `declare/3`).
  #
  # `Cure.Elab.Program.check_ast/2` runs a front-end, per-module,
  # AST-level duplicate-name scan BEFORE any elaboration
  # (`check_no_duplicate_types` / `check_no_duplicate_ctors`) — but its name
  # extractors only recognize `[:container, :indexed_type, :type_annotation]`
  # declaration tags (`declared_type_names/1`, `ctor_names/1` in
  # `lib/cure/elab/program.ex`). `:interface` is not among them, so an
  # `interface Equatable(a)` contributes NO name to that scan, and a sibling
  # `type Equatable = Foo | Bar` in the same module sails through unchallenged
  # even though both register a family (and, transiently, a constructor) named
  # `:Equatable`.
  #
  # `declarations.ex` itself has no defense of its own here: none of
  # `declare_parameterized_struct/4`, `declare_at_min_level/4`, or
  # `declare_indexed_at_min_level/6` ever check whether `name` (or any
  # constructor name about to be registered) already exists in `env` before
  # calling `Inductive.declare/3`. Whichever declaration is elaborated second
  # silently wins the family slot in `env.families`, while `env.ctors` /
  # `env.ctor_to_family` end up with a DANGLING entry for the constructor
  # that shared the family's name (the interface's own dictionary
  # constructor `:Equatable`, per the record convention that a record's sole
  # constructor shares its family's name) — `check_all_ctors/3` only
  # re-checks the *new* declaration's own constructor list, so the stale
  # leftover is never re-validated against the new family. No real dependent
  # language (Idris/Agda/Lean) allows two unrelated top-level declarations in
  # one module to bind the same name this way; it must be a compile error.
  test "D2: an interface's dictionary record name colliding with a sibling type declaration is rejected" do
    src = """
    mod X
      interface Equatable(a)
        fn eq(x: a, y: a) -> Bool
      type Equatable = Foo | Bar
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end

  # --------------------------------------------------------------------------
  # D3: a function-typed constructor field is accepted for a record (or a
  # parameterized enum) but rejected for a plain (zero-type-param) enum,
  # purely because the two forms are built by two independent, duplicated
  # constructor-elaboration pipelines with different feature coverage.
  #
  # A record (`:struct`, any arity) and a parameterized enum
  # (`type_params != []`) both route their constructor field types through
  # `elaborate_gadt_ctor/5` -> `build_explicit_tele/5` -> `idx_to_core/5`,
  # which fully supports arrow (function) types via `arrow_to_pi/4` — the
  # very same lowering `first_class_function_test.exs` exercises for ordinary
  # function parameter types (`fn ap(f: (Nat) -> Nat, x: Nat) -> Nat = ...`).
  #
  # A plain, zero-type-param enum (`type X = A(...) | B(...)`) instead routes
  # through the separate, older `build_ctors/1` -> `variant_to_ctor/1` ->
  # `fields_to_telescope/1` -> `type_to_core/1` pipeline, which has no arrow
  # clause at all and explicitly rejects one:
  #
  #     defp type_to_core({:function_call, meta, params}) do
  #       cond do
  #         Keyword.get(meta, :function_type) ->
  #           {:error, {:unsupported_field_type, :function}}
  #         ...
  #
  # So `type Callback = Wrap((Int) -> Int)` fails to elaborate, while the
  # semantically identical `rec Callback\n  f: (Int) -> Int` (or even
  # `type Callback(a) = Wrap((Int) -> Int)`, once `a` is unused but present)
  # succeeds. Idris/Agda/Lean impose no such restriction — a constructor
  # field may be any well-formed type, function types included, independent
  # of whether the datatype happens to be parameterized. This is pure
  # duplication (`type_to_core` reimplements a strict subset of
  # `idx_to_core`) producing an arbitrary feature gap, not a deliberate
  # restriction.
  test "D3: a function-typed field is accepted for a plain enum constructor, matching records" do
    assert {:ok, _env} = elaborate_all("type Callback = Wrap((Int) -> Int)\n")
  end
end
