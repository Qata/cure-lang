defmodule Cure.Elab.UnionTest do
  @moduledoc """
  End-to-end elaboration of anonymous unions, through `Program.elaborate/1` (so the
  stdlib prelude is in scope and `String` resolves).
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Inductive}
  alias Cure.Elab.{Program, Union}

  defp unwrap_lams({:lam, _g, _dom, body}), do: unwrap_lams(body)
  defp unwrap_lams(term), do: term

  defp union_families(env) do
    env.families |> Map.keys() |> Enum.filter(&Union.union_family?/1) |> Enum.sort()
  end

  describe "family generation" do
    test "a union in a parameter annotation declares its family" do
      src = """
      mod M
        fn f(x: Int | Bool) -> Int = 1
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert Inductive.family?(env, :"Union<Bool|Int>")
    end

    test "the family has one constructor per member, family-qualified" do
      src = """
      mod M
        fn f(x: Int | Bool) -> Int = 1
      end
      """

      assert {:ok, env} = Program.elaborate(src)

      names =
        env |> Inductive.ctors_of(:"Union<Bool|Int>") |> Enum.map(& &1.name) |> Enum.sort()

      assert names == [:"Union<Bool|Int>$Bool", :"Union<Bool|Int>$Int"]
    end

    test "a type member's ctor takes one payload argument; a literal member's takes none" do
      src = """
      mod M
        fn f(x: Int | :north) -> Int = 1
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      key = :"Union<Atom#:north|Int>"

      arities =
        env
        |> Inductive.ctors_of(key)
        |> Map.new(fn c -> {c.name, length(c.args)} end)

      assert arities[:"Union<Atom#:north|Int>$Int"] == 1
      assert arities[:"Union<Atom#:north|Int>$Atom#:north"] == 0
    end

    test "Int | Bool and Bool | Int declare ONE family, not two" do
      src = """
      mod M
        fn f(x: Int | Bool) -> Int = 1
        fn g(y: Bool | Int) -> Int = 2
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert union_families(env) == [:"Union<Bool|Int>"]
    end

    test "a one-member union collapses to the member itself — no family is generated" do
      src = """
      mod M
        fn f(x: Int | Int) -> Int = x
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert union_families(env) == []
    end

    test "(A | B) | C flattens: a union-typed alias used as a member splices in" do
      src = """
      mod M
        typealias P = Int | Bool
        fn f(x: P | Atom) -> Int = 1
      end
      """

      assert {:ok, env} = Program.elaborate(src)

      assert Inductive.family?(env, :"Union<Atom|Bool|Int>")

      ctors =
        env |> Inductive.ctors_of(:"Union<Atom|Bool|Int>") |> Enum.map(& &1.name) |> Enum.sort()

      assert length(ctors) == 3
    end
  end

  describe "admission errors surface from elaboration" do
    test "rejects a literal overlapping its own type" do
      src = """
      mod M
        fn f(x: Int | 3) -> Int = 1
      end
      """

      assert {:error, {:union_member_overlap, "Int#3", "Int"}} = Program.elaborate(src)
    end
  end

  describe "injection at check-position" do
    test "a member value is injected when checked against the union" do
      src = """
      mod M
        fn f(n: Int) -> Int | Bool = n
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      body = Env.get_def(env, :f).body |> unwrap_lams()

      assert {:ctor, :"Union<Bool|Int>$Int", [{:var, 0}]} = body
    end

    test "a literal is injected into its literal member constructor" do
      src = """
      mod M
        fn f() -> 3 | 4 = 3
      end
      """

      assert {:ok, env} = Program.elaborate(src)

      assert {:ctor, :"Union<Int#3|Int#4>$Int#3", []} = Env.get_def(env, :f).body
    end

    test "a value whose type is not a member is rejected" do
      src = """
      mod M
        fn f(b: Bool) -> Int | Atom = b
      end
      """

      assert {:error, _} = Program.elaborate(src)
    end
  end

  describe "widening" do
    test "a narrower union is widened into a wider one" do
      src = """
      mod M
        fn narrow(n: Int) -> Int | Bool = n
        fn wide(n: Int) -> Int | Bool | Atom = narrow(n)
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      body = Env.get_def(env, :wide).body |> unwrap_lams()

      assert {:case, _scrut, _motive, branches} = body

      # One branch per ctor of the NARROW family, each remapped to its counterpart
      # in the wide one. This is a real function, not a cast.
      assert branches |> Enum.map(fn {c, ar, _} -> {c, ar} end) |> Enum.sort() ==
               [{:"Union<Bool|Int>$Bool", 1}, {:"Union<Bool|Int>$Int", 1}]
    end

    test "widening to a union that lacks a source member is rejected" do
      src = """
      mod M
        fn narrow(n: Int) -> Int | Atom = n
        fn wide(n: Int) -> Int | Bool = narrow(n)
      end
      """

      assert {:error, _} = Program.elaborate(src)
    end
  end

  describe "elimination via typed patterns" do
    test "a match over a union becomes a Core :case with one branch per member" do
      src = """
      mod M
        fn f(x: Int | Bool) -> Int = match x
          n: Int -> n
          b: Bool -> 0
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      body = Env.get_def(env, :f).body |> unwrap_lams()

      assert {:case, _scrut, _motive, branches} = body

      assert branches |> Enum.map(fn {c, ar, _} -> {c, ar} end) |> Enum.sort() ==
               [{:"Union<Bool|Int>$Bool", 1}, {:"Union<Bool|Int>$Int", 1}]
    end

    test "a literal member is matched as a bare literal and binds nothing" do
      src = """
      mod M
        fn f(x: Int | :north) -> Int = match x
          n: Int -> n
          :north -> 0
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      body = Env.get_def(env, :f).body |> unwrap_lams()

      assert {:case, _, _, branches} = body
      arities = Map.new(branches, fn {c, ar, _} -> {c, ar} end)

      assert arities[:"Union<Atom#:north|Int>$Atom#:north"] == 0
      assert arities[:"Union<Atom#:north|Int>$Int"] == 1
    end

    test "a non-exhaustive match is rejected by the existing coverage check" do
      src = """
      mod M
        fn f(x: Int | Bool) -> Int = match x
          n: Int -> n
      end
      """

      assert {:error, {:missing_branch, _}} = Program.elaborate(src)
    end

    test "a branch naming a non-member is rejected" do
      src = """
      mod M
        fn f(x: Int | Bool) -> Int = match x
          n: Int -> n
          a: Atom -> 0
      end
      """

      assert {:error, _} = Program.elaborate(src)
    end

    test "a sub-union branch binds the narrowed value" do
      src = """
      mod M
        fn f(x: Int | Bool | Atom) -> Int | Bool | Atom = match x
          n: Int -> n
          rest: Bool | Atom -> rest
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      body = Env.get_def(env, :f).body |> unwrap_lams()

      assert {:case, _, _, branches} = body
      # One Core branch per member of the WIDE union — the sub-union arm expanded.
      assert length(branches) == 3
    end

    test "the round trip: inject then eliminate recovers the payload" do
      src = """
      mod M
        fn wrap(n: Int) -> Int | Bool = n
        fn unwrap(x: Int | Bool) -> Int = match x
          n: Int -> n
          b: Bool -> 0
        fn go(n: Int) -> Int = unwrap(wrap(n))
      end
      """

      assert {:ok, _} = Program.elaborate(src)
    end
  end

  # The end-to-end proof: a union is not just well-typed, it RUNS. Construct, match,
  # recover the value on a real BEAM.
  #
  # (Spec §13 asks for this on generic-unix AtomVM. That is not runnable from this
  # repo — cure-lang is the compiler; the AtomVM loop lives in the parent esp32-beam
  # repo. This is the in-repo equivalent; AtomVM validation is a follow-up there.)
  describe "BEAM round-trip" do
    test "construct, match, and recover the payload" do
      src = """
      mod URT
        fn wrap(n: Int) -> Int | Bool = n
        fn unwrap(x: Int | Bool) -> Int = match x
          n: Int -> n
          b: Bool -> 0
        fn go(n: Int) -> Int = unwrap(wrap(n))
      end
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(src)
      assert apply(:"Cure.URT", :go, [7]) == 7
    end

    test "a type member erases to a tagged 2-tuple under its family-qualified ctor" do
      src = """
      mod UTM
        fn wrap(n: Int) -> Int | Bool = n
      end
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(src)

      assert apply(:"Cure.UTM", :wrap, [7]) == {:"Union<Bool|Int>$Int", 7}
    end

    test "a literal member erases to its family-qualified NULLARY ctor atom" do
      src = """
      mod ULT
        fn pick() -> :north | :south = :north
      end
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(src)

      assert apply(:"Cure.ULT", :pick, []) ==
               :"Union<Atom#:north|Atom#:south>$Atom#:north"
    end
  end

  describe "the generated-family namespace is reserved" do
    # `Union.union_family?/1` recognises a generated family purely by testing
    # whether its atom starts with the literal prefix "Union<" (union.ex:45-47).
    # The design's own safety argument for every check-position injection
    # (elaborator.ex `maybe_inject_union/5`) rests on the claim that this prefix
    # is *unproducible* by a user-authored type name. Backtick-quoted
    # identifiers (`lexer.ex:652`, `lex_quoted_identifier/1`) admit ARBITRARY
    # characters, including `<`, `>`, and `|`, and `parse_type_def/2`
    # (`parser.ex:3226`) accepts any identifier-token name with no restriction
    # on which lexing form produced it — so a user CAN declare a real ADT named
    # `` `Union<Bool|Int>` ``. Once that name is registered, `union_family?/1`
    # can no longer tell it apart from a compiler-generated family, which
    # breaks flattening (a member that happens to normalise to that name gets
    # wrongly "exploded" as if its own constructors were union members) and
    # would equally confuse injection/widening for any function whose declared
    # return type is that user type.
    #
    # A user type declared with a name in this namespace must therefore be
    # rejected at declaration time — that is what actually keeps the namespace
    # reserved, rather than merely asserting that it is.
    test "declaring a user type whose name collides with the generated namespace is rejected" do
      src = """
      mod RSV
        type `Union<Bool|Int>` = A | B
      end
      """

      assert {:error, _} = Cure.Compiler.compile_and_load(src)
    end

    test "using such a colliding type as a union member does not corrupt flattening" do
      # Before the fix: `P`'s constructors A/B get wrongly spliced in as if they
      # were union members of `P | Atom`, producing a bogus 3-member family
      # `Union<A|Atom|B>` instead of a legitimate 2-member union whose members
      # are `Atom` and the opaque payload type `P`.
      src = """
      mod RSV2
        type `Union<Bool|Int>` = A | B

        typealias P = `Union<Bool|Int>`

        fn f(x: P | Atom) -> Int = 1
      end
      """

      # Whatever the outcome, the collision must not silently produce a
      # 3-member family whose keys are the colliding type's own constructor
      # names. The declaration itself is rejected (see the test above), so this
      # program can never reach that corrupted state.
      assert {:error, _} = Cure.Compiler.compile_and_load(src)
    end
  end

  describe "sub-union arm substitution respects inner shadowing" do
    # `expand_member_arm` (elaborator.ex) rewrites a sub-union arm's bound name
    # (`rest` below) to `assert_type <fresh> : <sub-union>` via a plain textual
    # walk (`subst_surface_var/3` originally; now `subst_respecting_shadowing/3`)
    # over the arm's SURFACE body. That walk must not descend into a nested
    # binder that rebinds the SAME name — a nested `match` arm whose own pattern
    # is also named `rest`, or a lambda parameter named `rest` — because that
    # inner occurrence refers to the INNER binding (with the inner's own,
    # narrower type), not the outer sub-union value.
    #
    # This is not confined to union code: `pattern_binders/1` (elaborator.ex)
    # backs `binds_any?/2`, the general capture-avoidance guard `elaborate_let_block`
    # and ~10 other surface-substitution call sites rely on throughout the whole
    # elaborator. It recognises a binder only via a `{:variable, _, v}` node — but
    # `:typed_pattern`'s bound name is a bare STRING in its children
    # (`{:typed_pattern, _, [name, type_ast]}`), so a typed pattern was invisible to
    # every one of those guards. Proven independently of any union sub-arm logic:
    test "a `let`'s capture-avoidance guard sees a typed-pattern's shadowing" do
      # `ok/1`'s argument is elaborated in CHECK position against its declared
      # `Bool` parameter type, so a wrongly-substituted lambda fails there with
      # `{:lambda_expected_pi, _}` — a DIFFERENT, later, more confusing error than
      # the correct, immediate `{:unsupported_expression, lambda}` rejection that
      # `elaborate_let_block` gives for a non-inferable `let` rhs shadowed before
      # its only "use". Before the `pattern_binders/1` fix this test observed
      # `{:error, {:lambda_expected_pi, {:data, :Bool, [], []}}}` — proof the
      # outer `let`'s lambda was spliced into `ok(n)`'s argument position instead
      # of the inner, freshly-matched Bool `n` — even though `n: Bool -> ok(n)`'s
      # `n` is a completely ordinary (non-sub-union) type-member pattern.
      src = """
      mod LBD
        fn ok(b: Bool) -> Bool = b

        fn f(x: Int | Bool) -> Bool =
          let n = fn(y) -> y
          match x
            n: Int -> true
            n: Bool -> ok(n)
      end
      """

      assert {:error, {:unsupported_expression, {:lambda, _, _}}} = Program.elaborate(src)
    end

    test "a nested match rebinding the sub-union arm's name is refused, not silently corrupted" do
      src = """
      mod SH2
        fn describe(x: Int | Bool | Atom) -> Bool =
          match x
            n: Int -> true
            rest: Bool | Atom ->
              match rest
                rest: Bool -> not rest
                a: Atom -> false
      end
      """

      # Before the fix: the inner `rest: Bool -> not rest` arm's body `rest` got
      # SILENTLY rewritten to the OUTER `assert_type <outer-fresh> : Bool | Atom`
      # ascription (the substitution could not see that the inner match's own
      # pattern rebinds `rest`), so `not` was applied to a Bool|Atom UNION value
      # instead of the freshly-bound inner Bool — failing with the confusing
      # `{:foreign_ctor, :"Union<Atom|Bool>$Atom"}`, whose shape gives no hint
      # that shadowing is the actual cause.
      #
      # After the fix: the same class of shadowing this codebase's OTHER
      # surface-substitution sites refuse outright (`:shadowed_as`,
      # `:shadowed_tuple`, `:shadowed_catchall`, …) is refused here too, with an
      # honest, correctly-labelled diagnostic instead of a confusing downstream
      # type error.
      assert {:error, {:unsupported_pattern, :shadowed_sub_union}} = Program.elaborate(src)
    end

    test "a lambda parameter rebinding the sub-union arm's name is refused, not silently corrupted" do
      src = """
      mod SH3
        fn describe(x: Int | Bool | Atom) -> Bool =
          match x
            n: Int -> true
            rest: Bool | Atom ->
              let g : (Bool) -> Bool = fn(rest) -> not rest
              g(true)
      end
      """

      # The lambda's own parameter `rest` shadows the outer sub-union binding
      # inside the lambda body; before the fix, `not rest` there was silently
      # rewritten to reference the OUTER Bool|Atom union value instead of the
      # lambda's own Bool parameter. Refused outright, for the same reason as
      # the nested-match case above.
      assert {:error, {:unsupported_pattern, :shadowed_sub_union}} = Program.elaborate(src)
    end
  end

  describe "dependent-pipeline routing sees a union wherever it appears" do
    # Program.dependent?/1's generic fallback (`{_tag, _meta, children} when
    # is_list(children)`) only recurses into a node's CHILDREN, never its META —
    # which is exactly why `:param`'s type (`Keyword.get(meta, :type)`) needed its
    # own dedicated clause. A union type can ALSO appear in two other meta-only
    # positions this branch's two new dependent?/1 clauses (:union_type,
    # :typed_pattern) do not, by themselves, make reachable:
    #
    #   * a `let`'s type ascription (`type_annotation:` in `:assignment`'s meta,
    #     not its children — parser.ex's `let_ascribed`/`maybe_wrap_as`);
    #   * a match arm's OWN PATTERN (`pattern:` in `:match_arm`'s meta, not its
    #     children — parser.ex `parse_match_arm/1`).
    #
    # A module using a union ONLY in one of those two positions (no function
    # param/return type ever names the union) is silently routed to the CLASSIC
    # pipeline, which has no union machinery at all — not a clean
    # `:unsupported_container`-style rejection, but whatever confusing error
    # falls out of classic's ordinary (non-union-aware) match-arm handling.
    test "a union named only in a `let` ascription still routes to the dependent pipeline" do
      src = """
      mod LetOnly
        fn f() -> Int =
          let x : Int | Bool = 5
          match x
            n: Int -> n
            b: Bool -> 0
      end
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(src)
      assert apply(:"Cure.LetOnly", :f, []) == 5
    end
  end
  # The headline motivation (spec §1.3): put three unrelated types into a Map without
  # declaring a throwaway public ADT. Requires goal-directed solving — Std.Map.put's
  # `v` must be solved from the EXPECTED map type, not inferred from the first value
  # argument, or `v` locks to Int and the union never gets a chance to inject.
  describe "heterogeneous Map (the motivating case)" do
    test "a map literal at a union value type injects each element" do
      src = """
      mod HM
        use Std.Map
        fn build() -> Map(Atom, Int | Bool | Atom) = %{a: 1, b: true, c: :other}
      end
      """

      assert {:ok, _} = Program.elaborate(src)
    end

    test "round-trip: build a heterogeneous map, read it back, and discriminate" do
      src = """
      mod HMR
        use Std.Map

        fn build() -> Map(Atom, Int | Bool | Atom) = %{a: 1, b: true, c: :other}

        fn describe(v: Int | Bool | Atom) -> Int = match v
          n: Int -> n
          b: Bool -> 100
          a: Atom -> 200

        fn look(k: Atom) -> Int = describe(Std.Map.get(k, build()))
      end
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(src)

      assert apply(:"Cure.HMR", :look, [:a]) == 1
      assert apply(:"Cure.HMR", :look, [:b]) == 100
      assert apply(:"Cure.HMR", :look, [:c]) == 200
    end

    test "Std.Map.put at a union value type also injects" do
      src = """
      mod HMP
        use Std.Map
        fn build() -> Map(Atom, Int | Bool) = Std.Map.put(:a, 1, Std.Map.new())
      end
      """

      assert {:ok, _} = Program.elaborate(src)
    end
  end

  # An @extern hands back a RAW Erlang value with no constructor tag. Rather than
  # forbidding union-returning externs outright, the boundary GENERATES a discriminating
  # wrapper: call the raw function, guard on the result, inject the matching ctor. The
  # union is a real tagged union everywhere in Cure; the untagging exists only at the FFI
  # seam.
  #
  # Sound IFF the members can be told apart from an untagged value by an ORDERED guard
  # chain, most-specific-first: literals test the exact value, and a refining guard is
  # emitted ahead of the guard it refines (`is_boolean` before `is_atom`, so `Bool | Atom`
  # works — true/false take the Bool clause, every other atom falls through to Atom).
  #
  # Only members sharing a guard that neither refines are rejected: `Int | Nat` (both
  # Erlang integers), `List(Int) | List(Bool)` (both lists). No order separates those.
  describe "@extern returning a union: discriminating wrapper" do
    test "distinguishable members are accepted and tagged at runtime" do
      src = """
      mod EXD
        @extern(:erlang, :abs, 1)
        fn raw(n: Int) -> Int | Binary

        fn use_it(n: Int) -> Int = match raw(n)
          i: Int -> i
          b: Binary -> 0
      end
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(src)

      # erlang:abs/1 returns a raw integer; the wrapper must tag it.
      assert apply(:"Cure.EXD", :raw, [-5]) == {:"Union<Binary|Int>$Int", 5}
      # ...and the ordinary union elimination must then discriminate it.
      assert apply(:"Cure.EXD", :use_it, [-5]) == 5
    end

    test "a literal member is discriminated by exact value" do
      src = """
      mod EXL
        @extern(:erlang, :hd, 1)
        fn head(xs: List(Atom)) -> :north | Int
      end
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(src)

      assert apply(:"Cure.EXL", :head, [[:north]]) ==
               :"Union<Atom#:north|Int>$Atom#:north"
    end

    test "REJECTS members that share an erased representation: Int | Nat" do
      src = """
      mod EXN1
        @extern(:erlang, :abs, 1)
        fn raw(n: Int) -> Int | Nat
      end
      """

      assert {:error, {:extern_union_indistinct, :raw, _}} = Program.elaborate(src)
    end

    # SUPERSEDED. This originally asserted `Bool | Atom` was REJECTED, on the grounds
    # that Bool erases to the atoms true/false and so "collides" with Atom. That
    # encoded WRONG behaviour: `is_boolean/1` is a real, total Erlang guard that
    # strictly REFINES `is_atom/1`, so the two are perfectly discriminable by ORDER —
    # true/false take the Bool clause, every other atom falls through to Atom. The
    # question is never "do two members share a class", it is "can one member's guard
    # be ordered before the other's". Rejecting this lost real safety: the author's
    # only alternative was to type the extern as a bare Atom and hand-check.
    test "ACCEPTS Bool | Atom — is_boolean refines is_atom, so order discriminates" do
      src = """
      mod EXN2
        @extern(:erlang, :hd, 1)
        fn raw(xs: List(Atom)) -> Bool | Atom
      end
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(src)

      # true/false take the more specific Bool clause...
      assert apply(:"Cure.EXN2", :raw, [[true]]) == {:"Union<Atom|Bool>$Bool", true}
      assert apply(:"Cure.EXN2", :raw, [[false]]) == {:"Union<Atom|Bool>$Bool", false}
      # ...and every other atom falls through to Atom.
      assert apply(:"Cure.EXN2", :raw, [[:other]]) == {:"Union<Atom|Bool>$Atom", :other}
    end

    # NOT admissible — and for a reason that has nothing to do with the FFI. `:north`'s
    # type IS Atom, so `let x: :north | Atom = :north` admits TWO injections and there is
    # no subtyping to break the tie. The design's literal/type overlap rule rejects it at
    # canonicalisation, before runtime discrimination is even asked about.
    #
    # Worth stating plainly: INJECTION ambiguity and RUNTIME discrimination are different
    # questions. Order resolves the second (`Bool | Atom`); it can never resolve the first.
    test "REJECTS :north | Atom — a literal may not overlap its OWN type (injection, not FFI)" do
      src = """
      mod EXN2b
        @extern(:erlang, :hd, 1)
        fn raw(xs: List(Atom)) -> :north | Atom
      end
      """

      assert {:error, {:union_member_overlap, "Atom#:north", "Atom"}} = Program.elaborate(src)
    end

    test "ACCEPTS a literal over a class member: 3 | Nat (the sentinel pattern)" do
      src = """
      mod EXN3
        @extern(:erlang, :abs, 1)
        fn raw(n: Int) -> 3 | Nat
      end
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(src)

      assert apply(:"Cure.EXN3", :raw, [-3]) == :"Union<Int#3|Nat>$Int#3"
      assert apply(:"Cure.EXN3", :raw, [-7]) == {:"Union<Int#3|Nat>$Nat", 7}
    end

    test "STILL REJECTS two class members that share a guard: List(Int) | List(Bool)" do
      # Both erase to Erlang lists and neither guard refines the other — no order separates
      # them, so no wrapper can exist.
      src = """
      mod EXN4
        use Std.List
        @extern(:erlang, :hd, 1)
        fn raw(xs: List(Binary)) -> List(Int) | List(Bool)
      end
      """

      assert {:error, {:extern_union_indistinct, :raw, _}} = Program.elaborate(src)
    end

    test "a union in an @extern's ARGUMENT position is unaffected" do
      # Passing a union INTO Erlang is honest: the tagged tuple is a fine Erlang term.
      src = """
      mod EXA
        @extern(:erlang, :term_to_binary, 1)
        fn enc(v: Int | Bool) -> Binary
      end
      """

      assert {:ok, _} = Program.elaborate(src)
    end
  end
end
