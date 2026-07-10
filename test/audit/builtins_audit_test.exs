defmodule Cure.Audit.BuiltinsTest do
  @moduledoc """
  Audit findings for `lib/cure/core/builtins.ex` (the builtin/delta globals
  registry: declared Pi types + registered reduction behavior for the
  arithmetic/comparison/structural-equality op globals, plus the canonical
  Bool/Nat/Equivalent/Sigma/List inductive schemas).

  Each test below is a specific, currently-RED executable claim about
  behavior the audit believes is correct. See the comment above each test
  for the bug, why it is wrong, and what the reference implementations
  (Agda/Lean/Idris) do instead. Do not run this file automatically as part
  of the trusted-suite gate — it documents open findings, not yet-fixed
  regressions.
  """
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Core.{Builtins, Env, Inductive, Kernel}

  # ---------------------------------------------------------------------------
  # B1/B2/B3 shared background
  #
  # `Builtins.seed_ops/1` (builtins.ex:134-144) computes ONE `bool_ty` value —
  # `{:data, Inductive.builtin(env, :bool), [], []}` (builtins.ex:136) — and
  # bakes it as the codomain of EVERY comparison op (int_lt/le/gt/ge/eq/ne,
  # float_lt/le/gt/ge/eq/ne — via `seed_binops/3`, builtins.ex:162-171) and of
  # struct_eq/struct_ne (`seed_struct_ops/2`, builtins.ex:152-160). The doc
  # comment on `seed_ops` says it must "Run AFTER the inductive seeds so the
  # Bool codomain resolves through the registry" (builtins.ex:126-133).
  #
  # `Builtins.seed/2` takes an `exclude` MapSet (builtins.ex:115-124) so a
  # module that declares its OWN same-named type is not handed a duplicate,
  # look-alike seed — `maybe_seed/5`'s comment: "the module's own declaration
  # is the canonical family" (builtins.ex:183-193). Every real call site
  # threads this straight from the CURRENT SOURCE MODULE's own declared type
  # names (`declared_type_names(ast)`, program.ex:134/244/519) — so a module
  # that itself declares a type literally named `Bool` gets `:Bool` excluded
  # from `Builtins.seed`'s programmatic seed.
  #
  # `lib/std/bool.cure:12` is the ONE real `@builtin(:bool)` site in the tree
  # (`grep -rln "@builtin(:bool)"` finds only it) — i.e. Std.Bool.cure, the
  # module that DEFINES the canonical Bool, is exactly such a module. Any
  # OTHER user module that simply names a local type `Bool` (matching the
  # canonical schema or not — `declared_type_names` only looks at the NAME,
  # not at any `@builtin` tag) hits the identical path.
  #
  # For such a module, `maybe_seed(:bool, ...)` skips `declare_and_register`
  # entirely, so `Inductive.builtin(env, :bool)` is still `nil` at the moment
  # `seed_ops` runs (`seed_ops` always runs, unconditionally, as the last
  # step of `seed/2` — builtins.ex:116-124, `|> seed_ops()`). The module's own
  # `@builtin(:bool)` declaration only registers the real family LATER, in
  # `elaborate_declarations` (program.ex:136) — well after `seed_ops` already
  # closed over `{:data, nil, [], []}` as the codomain of all 14 comparison
  # ops plus both struct ops. That baked type is a plain Elixir term (a
  # snapshot, not a live lookup), so the later registration never goes back
  # and fixes it: `seed_ops`'s own stated invariant ("Bool codomain resolves
  # through the registry") is violated in exactly the one real scenario it
  # exists to describe.
  #
  # This is not merely cosmetic: `Kernel.infer(ctx, {:data, name, _, _})`
  # (kernel.ex:138-149) looks the family up with `Inductive.get_family(sig,
  # name)`, which is a bare `Map.get(families, name)` (inductive.ex:327) — for
  # `name = nil` this returns `nil` cleanly (no crash) and `infer` reports
  # `{:error, {:unknown_family, nil}}`. That error propagates, unmodified,
  # through every enclosing `with` in `infer(ctx, {:pi, ...})` (kernel.ex:96-
  # 103) up to `Kernel.check_def/2`'s builtin-op clause (kernel.ex:419-426),
  # whose own comment says builtin ops are "Total by fiat (Lean/Idris treat
  # primitive ops so)" and must always check. In this scenario they don't.

  # B1: with :bool excluded (the Std.Bool.cure path, or any user module that
  # simply names a local type `Bool`), int_lt's declared codomain must still
  # reference the real Bool family and must still type-check — a builtin op's
  # signature should never depend on unrelated seeding/exclusion order (Lean's
  # kernel-Nat/Bool primitives and Agda's BUILTIN pragmas are resolved once,
  # unconditionally, never as a function of what else got seeded first).
  test "B1: comparison op codomain is a real Bool family even when :bool is excluded from seeding" do
    env = Builtins.seed(Env.empty(), MapSet.new([:Bool]))

    assert %{type: {:pi, _, {:pi, _, {:data, fam, [], []}}}} = Env.get_def(env, :int_lt)
    refute is_nil(fam)
    assert :ok = Kernel.check_def(env, :int_lt)
  end

  # B2: `seed_struct_ops/2` closes over the SAME `bool_ty` value computed in
  # `seed_ops/1` (builtins.ex:143 passes it in from the single call site), so
  # the identical defect breaks the A1 polymorphic structural-equality
  # globals (struct_eq/struct_ne) too, not just the monomorphic comparisons.
  test "B2: struct_eq/struct_ne codomain is a real Bool family even when :bool is excluded from seeding" do
    env = Builtins.seed(Env.empty(), MapSet.new([:Bool]))

    assert %{type: {:pi, _, {:pi, _, {:pi, _, {:data, fam, [], []}}}}} = Env.get_def(env, :struct_eq)
    refute is_nil(fam)
    assert :ok = Kernel.check_def(env, :struct_eq)
  end

  # B3: the defect must not survive the REAL pipeline order. `program.ex`
  # excludes `:Bool` from `Builtins.seed` (program.ex:134) and only
  # afterward, in `elaborate_declarations` (program.ex:136), processes the
  # module's own `@builtin(:bool)` declaration — which itself calls exactly
  # `Inductive.declare/3` + `Inductive.register_builtin/3` for `:Bool` under
  # key `:bool`. This test reproduces that sequence directly against the
  # public `Inductive` API (the same primitives `builtins.ex` itself uses for
  # `bool_family/0`, `bool_ctors/0`, and `declare_and_register/3`). Even
  # after the module's own canonical Bool is declared AND registered under
  # the exact key the seeded ops were supposed to resolve through,
  # `int_lt`'s type must end up well-formed once the whole module is
  # elaborated — not permanently pinned to the `nil`-family snapshot taken
  # before that registration happened.
  test "B3: registering the module's own Bool after seed/2 (the real elaborate_declarations order) must still leave int_lt checkable" do
    env = Builtins.seed(Env.empty(), MapSet.new([:Bool]))

    family = Inductive.family(:Bool, [], [], 0)
    ctors = [Inductive.ctor(:False, [], []), Inductive.ctor(:True, [], [])]
    env2 = env |> Inductive.declare(family, ctors) |> Inductive.register_builtin(:bool, :Bool)

    assert Inductive.builtin(env2, :bool) == :Bool
    assert :ok = Kernel.check_def(env2, :int_lt)
  end
end
