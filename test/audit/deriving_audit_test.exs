defmodule Cure.Audit.DerivingTest do
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Elab.{Program, Emit}

  # ---------------------------------------------------------------------------
  # DV1: deriving hardcodes the scrutinee variable names "x"/"y" instead of the
  # interface's actual declared parameter names.
  #
  # `lib/cure/elab/deriving.ex` builds a derived method's PARAMETER LIST from the
  # interface's real parameter names (`method_def/6` maps `info.params` and keeps
  # each `pname`, e.g. "a1"/"a2" below) — but the method BODY is built by
  # `body(:Equatable, ...)` / `body(:Ord, ...)`, which unconditionally scrutinises
  # `var("x")` and matches `var("y")` (deriving.ex:118, :121, :143, :146),
  # regardless of what the bound parameters are actually named. Whenever an
  # `Equatable`/`Ord` interface's method isn't spelled with literal params named
  # "x" and "y" (any other convention — "a1"/"a2", "l"/"r", "this"/"that" — is
  # equally valid interface surface syntax), the generated body references two
  # free variables that were never bound by the function's own signature, and
  # elaboration must fail — for EVERY derived instance under that interface, not
  # just ones with fields.
  #
  # Haskell's GHC-generated `Eq`/`Ord` instances and Idris2's `Deriving.Eq`/`Ord`
  # always reference exactly the argument names the derivation itself introduces
  # for the generated clause — there is no possible name mismatch between a
  # derived instance's header and its body, because both come from the same
  # generation step. Cure's `deriving.ex` threads the real names into the header
  # but not into the body, so the two can (and here, do) disagree.
  #
  # This is a compile-time break (elaboration of the derived body fails with an
  # unresolved-identifier error), not a silent unsoundness — but it means
  # `deriving Equatable`/`deriving Ord` only works by accident, for interfaces
  # that happen to spell their method parameters "x"/"y" (exactly what every
  # existing `deriving_test.exs` fixture does).
  test "DV1: derived Equatable elaborates when the interface's eq params aren't named x/y" do
    src = """
    mod DvOne
      interface Equatable(a)
        fn eq(a1: a, a2: a) -> Bool
      type Color = Red | Green | Blue deriving Equatable
      fn eqSame() -> Bool = eq(Green, Green)
      fn eqDiff() -> Bool = eq(Red, Blue)
    end
    """

    assert {:ok, env} = Program.elaborate(src)

    functions = Enum.uniq([:eqSame, :eqDiff] ++ Program.impl_def_names(env))
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.DvOneColor", functions: functions)

    assert apply(m, :eqSame, []) == true
    assert apply(m, :eqDiff, []) == false
  end

  # ---------------------------------------------------------------------------
  # DV2: deriving on a parameterized ADT never threads a `where Iface(a)`
  # dictionary constraint for the type parameter, so any field of the bound
  # parameter's own type makes the derived instance unelaborable.
  #
  # `for_type_ast/2` (deriving.ex:230-231) builds `for_type = Lst(a)` — the head
  # type applied to its own (unbound-in-the-instance) type-parameter NAMES — for
  # a parameterized type such as `type Lst(a) = Nil | Cons(a, Lst(a))`. The
  # generated `eq` method's body calls `eq(a0, b0)` on the `a`-typed field
  # (deriving.ex's `eq_conj`, called for every field by position with no regard
  # to whether the field's type is the recursive family itself or the bound type
  # parameter). `a` auto-generalizes to an implicit rigid type variable
  # (`Cure.Elab.Declarations.auto_generalize/3`), so at that call site
  # `Cure.Elab.Resolve.method_call/5` classifies the field's type as `{:rigid,
  # lvl}` and requires an in-scope dictionary binder of type `Equatable(a)`
  # (`Resolve.abstract/6`, `find_dict_binder/4`) — but such a binder is only ever
  # introduced by an explicit `where Iface(a)` clause recorded in a function's
  # `:constraints` meta (`Declarations.inject_constraint_dicts/2`). Deriving's
  # `method_def/6` (deriving.ex:85-104) never puts a `:constraints` key on the
  # generated method's meta, so no such dictionary is ever injected. Deriving a
  # `Lst(a)`'s `Equatable`/`Ord` therefore fails to elaborate as soon as the
  # element type is abstract, i.e. for the single most common use of `deriving`
  # on a container type.
  #
  # Haskell's `deriving (Eq)` on `data List a = Nil | Cons a (List a)` produces
  # `instance Eq a => Eq (List a)`, correctly qualifying the instance by `Eq a`;
  # Idris2's `%runElab derive` does the same (`Deriving.Eq`/`Deriving.Ord`
  # auto-add an interface constraint per used type parameter). Cure's deriving
  # does neither — no equivalent `where Equatable(a)` is ever synthesised.
  test "DV2: derived Equatable elaborates for a parameterized recursive container" do
    src = """
    mod DvTwo
      interface Equatable(a)
        fn eq(x: a, y: a) -> Bool
      implementation Equatable for Int
        fn eq(x: Int, y: Int) -> Bool = x == y
      type Lst(a) = Nil | Cons(a, Lst(a)) deriving Equatable
      fn l1() -> Lst(Int) = Cons(1, Nil)
      fn l2() -> Lst(Int) = Cons(1, Nil)
      fn l3() -> Lst(Int) = Cons(2, Nil)
      fn eqSame() -> Bool = eq(l1(), l2())
      fn eqDiff() -> Bool = eq(l1(), l3())
    end
    """

    assert {:ok, env} = Program.elaborate(src)

    functions = Enum.uniq([:eqSame, :eqDiff, :l1, :l2, :l3] ++ Program.impl_def_names(env))
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.DvTwoLst", functions: functions)

    assert apply(m, :eqSame, []) == true
    assert apply(m, :eqDiff, []) == false
  end

  # ---------------------------------------------------------------------------
  # DV3: `Deriving.generate/3` never validates that the container it was handed
  # actually looks like a variant/enum body, so an unsupported shape (a record's
  # named-field list, or any other container whose entries aren't `variant:
  # true` tagged) silently derives an implementation whose method body is an
  # EMPTY `match` — zero arms, unsatisfiable for every input — instead of
  # reporting an error.
  #
  # `constructors/1` (deriving.ex:65-78) only recognises `{:function_def, m, _}`
  # / `{:variable, m, _}` entries tagged `variant: true`; anything else (e.g. a
  # `rec`'s `{:param, meta, fname}` field list — see
  # `Cure.Elab.Declarations.struct_ctor_sig/2`, which builds exactly that shape)
  # silently falls through its catch-all clause to `[]`. `generate/3` then
  # proceeds unconditionally: `body(:Equatable, eq_name, [], _env)` builds
  # `match(var("x"), [])` — a `{:pattern_match, ..., [scrut]}` node with NO match
  # arms at all — and wraps it in `{:ok, {:implementation, ...}}`. The surface
  # parser currently never *reaches* this path for a `rec` (it never attaches a
  # `deriving` clause when parsing `rec`, `lib/cure/compiler/parser.ex:2878-2908`
  # vs `:3200-3213`), so today's compiler pipeline can't trigger it end-to-end —
  # but `Deriving.generate/3` is itself a public, directly-callable function (the
  # existing `deriving Show` test in `test/cure/elab/deriving_test.exs` calls it
  # exactly this way), and nothing in its contract or its doc comment restricts
  # it to enum-shaped containers. Any future caller (a `rec ... deriving`
  # extension, an `@derive` decorator, a macro-built container) hits this
  # unguarded fallthrough and gets a broken, non-exhaustive instance instead of a
  # clear error.
  #
  # Idris2/Haskell's deriving machinery is defined only over algebraic/variant
  # types; asking either to derive `Eq` for something outside that shape is a
  # reported error at the derivation site, never a silently-emitted vacuous
  # instance.
  test "DV3: Deriving.generate rejects a non-variant (struct-shaped) container instead of emitting an empty match" do
    {:ok, env} =
      Program.elaborate("""
      mod DvThree
        interface Equatable(a)
          fn eq(x: a, y: a) -> Bool
      end
      """)

    # The exact shape `Cure.Elab.Declarations.struct_ctor_sig/2` builds a `rec`'s
    # fields into: a plain list of `{:param, meta, fname}` entries, none tagged
    # `variant: true`.
    fields = [
      {:param, [type: {:variable, [], "Int"}], "x"},
      {:param, [type: {:variable, [], "Int"}], "y"}
    ]

    container = {:container, [container_type: :struct, name: "Point", type_params: []], fields}

    assert {:error, _reason} = Cure.Elab.Deriving.generate(:Equatable, container, env)
  end
end
