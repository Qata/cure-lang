defmodule Cure.Elab.PolymorphicFunctionTest do
  @moduledoc """
  Polymorphic functions via implicit type parameters (Idris parity). A bare
  implicit parameter `{a}` (Cure's `{name}` erased-argument syntax) carried no
  kind, so `elaborate_param_telescope` rejected it with `{:untyped_parameter, …}`.
  A bare implicit type variable ranges over `Type`, so its kind now defaults to
  `Type` (erased) — exactly like `{a: Type}`. The implicit is then solved from the
  present arguments by the existing metavariable machinery (`elaborate_global_app`
  / `solve_arg`), so `id`, `const`, and polymorphic higher-order functions type
  and run.

  Oracle `func/fn05_poly_id` + `func/fn06_poly_const` pin accept/accept.

  Not covered here: solving a constructor's implicit parameter from an *expected*
  type (`fn g() -> List(Nat) = Nil()` — the return annotation is not propagated
  into constructor implicit-solving). That is checking-mode constructor
  elaboration, a separate reach.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "the polymorphic identity function types and runs" do
    src = @nat <> "  fn id({a}, x: a) -> a = x\n  fn g() -> Nat = id(S(Z()))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.PfId", functions: [:id, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "a two-type-parameter const function selects the first argument" do
    src =
      @nat <>
        "  fn const({a}, {b}, x: a, y: b) -> a = x\n  fn g() -> Nat = const(S(Z()), Z())\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.PfConst", functions: [:const, :g])

    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "a polymorphic higher-order function applies its function argument" do
    src =
      @nat <>
        "  fn ap({a}, {b}, f: (a) -> b, x: a) -> b = f(x)\n  fn inc(n: Nat) -> Nat = S(n)\n" <>
        "  fn g() -> Nat = ap(inc, S(Z()))\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.PfAp", functions: [:ap, :inc, :g])

    # ap(inc, S(Z)) = inc(S(Z)) = S(S(Z)).
    assert apply(mod, :g, []) == {:S, {:S, :Z}}
  end

  test "an untyped explicit (non-implicit) parameter is still rejected" do
    # The Type-default applies ONLY to implicit `{a}`; a bare value parameter with
    # no type annotation remains an error.
    assert {:error, {:untyped_parameter, _}} =
             Program.elaborate(@nat <> "  fn f(x) -> Nat = Z()\nend\n")
  end
end
