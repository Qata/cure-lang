defmodule Cure.Audit.InterfaceImplTest do
  @moduledoc """
  Red tests pinning soundness/correctness gaps found while auditing
  `lib/cure/elab/interface.ex` and `lib/cure/elab/implementation.ex` (the
  compile-time `interface`/`implementation` typeclass pair) against Idris2
  `interface`/`implementation` and Lean 4 `class`/`instance` elaboration, and
  against Cure's own design spec
  (`docs/superpowers/specs/2026-07-10-typeclasses-design.md`) and plan
  (`docs/superpowers/plans/2026-07-10-typeclasses-plan.md`).

  Every test asserts the CORRECT behaviour and is red today. See each test's
  comment for the traced root cause.
  """

  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Elab.{Program, Coherence}
  alias Cure.Core.{Env, Inductive}


  # --------------------------------------------------------------------------
  # IF2 — a higher-kinded interface never gets its Core dictionary record
  # type declared, silently breaking abstract (dictionary) dispatch.
  # --------------------------------------------------------------------------

  test "IF2: a higher-kinded interface (head kind Type -> Type) never gets its dictionary record family declared" do
    # BUG. `Interface.declare_dictionary_former/2` has two clauses:
    # `head_kind: :type` builds the Core record family via
    # `Declarations.declare_record/4` (interface.ex:55-62); every OTHER head
    # kind (interface.ex:65, `defp declare_dictionary_former(_desc, env), do:
    # {:ok, env}`) is a bare no-op. The comment above it (interface.ex:51-54)
    # claims the higher-kinded former "is built by the HKT resolution step"
    # elsewhere -- but grep across lib/cure/elab/*.ex for any OTHER call to
    # `declare_record`/`Inductive.declare` keyed on an interface name finds
    # none. So a `Type -> Type`-headed interface such as `Functor` is NEVER
    # registered as a Core inductive family at all.
    #
    # This silently breaks ABSTRACT (dictionary) dispatch: any polymorphic
    # function constrained by `where Functor(f)` needs
    # `Resolve.dict_value/dict_term` (resolve.ex:77-83, 213-229) to build a
    # `{:ctor, :Functor, fields}` value of type `Functor(head)` -- which
    # requires the `Functor` family to exist. CONCRETE dispatch (a direct
    # `fmap(xs, g)` call, as in resolve_hkt_test.exs) never touches this path
    # at all, which is why the existing test suite never caught the gap. The
    # design spec's own success criterion is "Functor is genuinely
    # higher-kinded" (design doc §1) with abstract dispatch as a first-class
    # requirement (§3.4 point 2), not concrete-only sugar.
    src = """
    mod M
      interface Functor(f)
        fn fmap(container: f(a), g: a -> b) -> f(b)
    end
    """

    assert {:ok, env} = Program.elaborate(src)
    desc = Env.get_interface(env, :Functor)
    assert desc.head_kind == {:arrow, :type, :type}

    assert Inductive.family?(env, :Functor),
           "Functor's Core dictionary record family must be registered even " <>
             "though its head is higher-kinded, so abstract/dictionary " <>
             "dispatch through a `where Functor(f)` constraint has something " <>
             "to build a dictionary value against"
  end

  # --------------------------------------------------------------------------
  # IF3 — two in-scope interfaces sharing a method name are never flagged;
  # method-name resolution has no cross-interface ambiguity check at all.
  # --------------------------------------------------------------------------

  test "IF3: two in-scope interfaces declaring a method with the same name are silently both registered" do
    # BUG. `Interface.for_method/2` (interface.ex:67-73) is the SOLE lookup
    # `Resolve.method_call` (resolve.ex:38) uses to find "the interface
    # descriptor whose method set contains `method`" for an unqualified call
    # `size(x)`: `Enum.find_value(ifaces, fn {_name, desc} -> ... end)` over
    # the WHOLE `env.interfaces` map, returning the FIRST interface (in
    # unspecified `%{}` iteration order) whose method table happens to
    # contain the name. There is no code path anywhere -- not in
    # `Interface.elaborate/2` (which never consults already-registered
    # interfaces), not in `for_method`, not in `Resolve` -- that ever checks
    # whether a method name is unique across in-scope interfaces. So an
    # unqualified call to `size` after this module would silently bind to
    # WHICHEVER interface's descriptor Elixir's map iteration happens to
    # yield first, independent of which one the call site actually means,
    # with zero ambiguity diagnostic at either the declaration or the call.
    #
    # Both Idris2 and Lean 4 require disambiguation (namespaced or
    # type-directed) when two in-scope interfaces/classes declare a
    # same-named method; an unqualified reference that cannot be
    # disambiguated is a compile error, not an arbitrary pick.
    src = """
    mod M
      interface Eqs(a)
        fn size(x: a) -> Int
      interface Ord(a)
        fn size(x: a) -> Bool
    end
    """

    assert match?({:error, _}, Program.elaborate(src)),
           "a method name shared by two in-scope interfaces must be flagged " <>
             "at registration (or every later unqualified call must require " <>
             "explicit disambiguation) -- interface.ex never checks for " <>
             "cross-interface method-name collisions at all"
  end

  # --------------------------------------------------------------------------
  # IF4 — a named implementation is registered in the coherence table but is
  # never bound as an actual value, so the coherence escape hatch is inert.
  # --------------------------------------------------------------------------

  test "IF4: a named implementation is recorded in Coherence but never bound as a value a caller can reference" do
    # BUG. Cure's locked coherence policy (memory `typeclass-surface-
    # decisions`, design spec §2/§3.4 point 5) is "global uniqueness + named
    # implementations as an escape hatch": `implementation Eqs for Int as
    # strictInt` is supposed to register under `:strictInt` "as an ordinary
    # dictionary-valued binding... A caller selects it explicitly with plain
    # record projection, `strictInt.eq(x, y)`... no new call syntax is
    # needed" (design spec §3.4 point 5).
    #
    # `Implementation.register_instance/4` (implementation.ex:134-147) only
    # writes the `ref` map into `Coherence.named` via
    # `Coherence.register_named/4` -- it never calls `Env.add_def` (or any
    # equivalent) to bind the atom `:strictInt` itself to anything. Confirmed
    # independently: `Coherence.lookup_named/2` (coherence.ex:69-77) has ZERO
    # callers anywhere in lib/ -- nothing in the elaborator ever consults the
    # named registry, so there is no code path through which
    # `strictInt.eq(x, y)` (or any other reference to `strictInt`) could ever
    # resolve. The escape hatch the locked coherence policy depends on to let
    # a second (overlapping) instance coexist is entirely non-functional: it
    # is accepted at parse/register time and then permanently unreachable.
    src = """
    mod M
      interface Eqs(a)
        fn eqs(x: a, y: a) -> Bool
      implementation Eqs for Int as strictInt
        fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
    end
    """

    {:ok, env} = Program.elaborate(src)
    assert {:ok, _ref} = Coherence.lookup_named(Env.coherence(env), :strictInt)

    assert Env.get_def(env, :strictInt) != nil,
           "a named implementation must be bound as an ordinary global value " <>
             "(of type Eqs(Int)) so 'strictInt.eq(x, y)'-style explicit " <>
             "selection (design spec §3.4 point 5) has something to project"
  end

end
