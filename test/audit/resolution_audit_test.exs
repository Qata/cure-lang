defmodule Cure.Audit.ResolutionTest do
  @moduledoc """
  Audit findings for `lib/cure/elab/resolution.ex` (E-layer name resolution /
  shadowing, "Approach B") and `lib/cure/elab/resolve.ex` (interface-method
  dispatch resolution). Each test is a specific, executable claim about
  CORRECT behavior; every test here is red today.

  R1 (resolution.ex, in concert with `program.ex`'s collision driver): the
  ENTIRE collision-detection pipeline — `owned_family_names/1` /
  `owned_def_names/1` in `program.ex`, fed into `Cure.Elab.Resolution.classify/2`
  — is scoped to exactly two namespaces: family/type names and top-level def
  names. A bare CONSTRUCTOR name is only ever re-keyed as a SIDE EFFECT of its
  owning FAMILY colliding (`rekey_module_env`'s `owned_ctor_names` is derived
  from `owned_family_names`). There is no independent constructor-name
  collision check. So when a local module declares a constructor whose bare
  name matches an imported constructor of a DIFFERENT, non-colliding family,
  `classify/2` never sees a collision, `rekey_module_env` is never invoked for
  the import, and the import's constructor is silently destroyed by the plain
  `Map.put` in `Cure.Core.Inductive.declare/3` — with no diagnostic AND no
  qualified escape hatch (the module was never re-keyed, so
  `resolve_qualified/3` has nothing to find). This breaks the module's own
  central promise (moduledoc: "resolves qualified surface references... from
  the re-keyed env"; local-type-shadowing plan: "keeping the imported family
  reachable via a qualified escape hatch").

  R2 (resolve.ex): `head_param_index/2`'s fallback for a higher-kinded
  interface method (`Functor`-style, head appears only applied as `f(a)`,
  never bare) silently assumes the head-bearing parameter is declared FIRST
  (`Enum.find_index(...) || 0`). This assumption is not documented as a
  surface-syntax rule anywhere and is not enforced by the parser or by
  `Cure.Elab.Interface`. Any higher-kinded method whose `f(...)`-typed
  parameter is not textually first silently classifies the WRONG argument as
  the dispatch head, so a perfectly valid instance registration is reported
  `{:no_instance, ...}` (or worse, a spurious error from trying to classify an
  unrelated argument's type).
  """
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Elab.{Program, Resolution}

  # ---------------------------------------------------------------------------
  # R1: local ctor `Ok` (of a local type `Res`) collides with the bare `Ok`
  # constructor of `Std.Result` (of the DIFFERENT family `Result`). The two
  # family names (`Res` vs `Result`) never collide, so `classify/2` — driven
  # by `program.ex`'s family/def-name-only ownership scan — never classifies
  # this as a collision and `Std.Result` is never re-keyed. `Std.Result`'s own
  # `Ok` constructor is silently dropped by the later `Map.put` when the local
  # `Res` type registers its own `Ok`.
  #
  # Correct behavior (Idris/Agda/Lean and this module's own documented
  # contract): whatever loses the bare-atom race must still be reachable
  # through the qualified escape hatch, exactly like a family-name collision
  # loser (R3/R5 in `test/cure/elab/type_shadowing_test.exs`). Today
  # `Resolution.resolve_qualified(env, "Std.Result.Ok", :value)` returns
  # `:error` — `Std.Result`'s `Ok` is not reachable under ANY key, bare or
  # qualified, after this program elaborates.
  # ---------------------------------------------------------------------------
  test "R1: a local ctor colliding with an import's same-named ctor from a DIFFERENT family stays reachable qualified" do
    src = """
    mod CtorNameCollision
      use Std.Result
      type Res = Ok(Int) | Err(String)
      fn mk() -> Res = Ok(5)
    end
    """

    assert {:ok, env} = Program.elaborate(src)

    assert {:ok, _key} = Resolution.resolve_qualified(env, "Std.Result.Ok", :value)
  end

  # ---------------------------------------------------------------------------
  # R2: `resolve.ex`'s `head_param_index/2` (private, exercised indirectly via
  # `Resolve.method_call/5` <- `elaborate_named_call/5`) defaults to parameter
  # index 0 whenever the head type variable has no BARE occurrence among a
  # method's params — the only case a higher-kinded interface (`Functor`) can
  # ever be in, since its head always appears applied (`f(a)`), never bare.
  # `test/cure/elab/resolve_hkt_test.exs`'s own passing `Functor` test happens
  # to declare `fmap(container: f(a), g: a -> b)` with the applied-head param
  # FIRST, which is exactly why it passes — masking that the "default to
  # first" heuristic is not actually locating the head, just getting lucky on
  # param order.
  #
  # Here the interface and its implementation both declare
  # `fmap(g: a -> b, container: f(a))` — a legal, unremarkable reordering; the
  # design doc (`docs/superpowers/specs/2026-07-10-typeclasses-design.md`
  # §3.4) defines resolution by "the type of the method's interface-head
  # argument position", not by textual position. `head_param_index` picks
  # index 0 (`g`, a lambda) as the head instead of index 1 (`container`, the
  # actual `f(a)`-typed argument), so a registered, valid `Functor for List`
  # instance is not found.
  # ---------------------------------------------------------------------------
  test "R2: higher-kinded method dispatch finds the f(a)-typed head argument regardless of its declared position" do
    src = """
    mod HktParamOrder
      fn lmap(xs: List(a), g: a -> b) -> List(b) =
        match xs
          [] -> []
          [h | t] -> [g(h) | lmap(t, g)]
      interface Functor(f)
        fn fmap(g: a -> b, container: f(a)) -> f(b)
      implementation Functor for List
        fn fmap(g: a -> b, container: List(a)) -> List(b) = lmap(container, g)
      fn bump(xs: List(Int)) -> List(Int) = fmap(fn(x) -> x + 10, xs)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
