defmodule Cure.Elab.UnionIdentityTest do
  @moduledoc """
  The load-bearing soundness property of anonymous unions.

  Because a union's family name is CONTENT-DERIVED, two modules writing the same
  union must land on the same family (or a value built in one will not typecheck in
  the other) — and two modules whose members merely SHARE A BARE NAME but are
  unrelated types must NOT (or the two collapse into one family and the type system
  silently conflates them).
  """
  use ExUnit.Case, async: true

  alias Cure.Core.Inductive
  alias Cure.Elab.{Program, Union}

  defp union_families(env) do
    env.families |> Map.keys() |> Enum.filter(&Union.union_family?/1) |> Enum.sort()
  end

  describe "cross-module identity" do
    test "two modules writing the same union share ONE family" do
      src = """
      mod A
        fn mk(n: Int) -> Int | Bool = n
      end

      mod B
        fn mk2(n: Int) -> Bool | Int = n
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert union_families(env) == [:"Union<Int|Std.Bool#Bool>"]
    end

    test "a union value built in A typechecks and eliminates in B" do
      src = """
      mod A
        fn mk(n: Int) -> Int | Bool = n
      end

      mod B
        use A
        fn out(n: Int) -> Int = match A.mk(n)
          i: Int -> i
          b: Bool -> 0
      end
      """

      assert {:ok, _} = Program.elaborate(src)
    end
  end

  # Two SIBLING modules in one source may not both declare `Point` — that is a hard
  # `:sibling_module_collision`. The shadowing hazard is reachable only across an
  # IMPORT boundary: a local declaration shadows an imported module's type, and
  # `Resolution.rekey_module_env/3` re-keys the imported (loser) module's `Point` to
  # `:"Mod#Point"`.
  #
  # A compiler-GENERATED union family is not "owned" by any surface declaration, so it
  # is not in the rekey pass's owned-names set. These tests pin that its ctor payload
  # types and its own content-derived key are nonetheless rewritten — otherwise the
  # imported module's `Union<Int|Point>` would keep a DANGLING bare `:Point` payload
  # and would collide with the importing program's own, unrelated `Union<Int|Point>`.
  describe "shadowing across an import: a generated union family must be rekeyed too" do
    alias Cure.Core.{Env, Grade}
    alias Cure.Elab.Resolution

    setup do
      point = {:data, :Point, [], []}
      ukey = :"Union<Int|Point>"

      env =
        %Env{}
        |> Inductive.declare(Inductive.family(:Point, [], [], 0), [
          Inductive.ctor(:APoint, [], [])
        ])
        |> Inductive.declare(Inductive.family(ukey, [], [], 0), [
          Inductive.ctor(:"Union<Int|Point>$Int", [{:v, {:int_type}}], [], [Grade.unrestricted()]),
          Inductive.ctor(:"Union<Int|Point>$Point", [{:v, point}], [], [Grade.unrestricted()])
        ])
        |> Env.add_def(
          :mk,
          {:pi, Grade.unrestricted(), point, {:data, ukey, [], []}},
          {:ctor, :"Union<Int|Point>$Point", [{:var, 0}]}
        )

      %{env: env}
    end

    test "the union family's KEY is recomputed from the rekeyed member", %{env: env} do
      out = Resolution.rekey_module_env(env, "M", MapSet.new([:Point]))

      assert Map.has_key?(out.families, :"Union<Int|M#Point>")

      # The stale, bare-Point key must be GONE — leaving it would let this imported
      # union be conflated with an unrelated local `Point | Int`.
      refute Map.has_key?(out.families, :"Union<Int|Point>")
    end

    test "the union ctor's payload type is rewritten to the qualified member", %{env: env} do
      out = Resolution.rekey_module_env(env, "M", MapSet.new([:Point]))

      ctor = out.ctors[:"Union<Int|M#Point>$M#Point"]
      assert [{:v, {:data, :"M#Point", [], []}}] = ctor.args
      assert out.ctor_to_family[:"Union<Int|M#Point>$M#Point"] == :"Union<Int|M#Point>"

      refute Map.has_key?(out.ctors, :"Union<Int|Point>$Point")
    end

    test "occurrences in def bodies and types follow the rename", %{env: env} do
      out = Resolution.rekey_module_env(env, "M", MapSet.new([:Point]))

      assert {:ctor, :"Union<Int|M#Point>$M#Point", [{:var, 0}]} = out.defs[:mk].body

      assert {:pi, _, {:data, :"M#Point", [], []}, {:data, :"Union<Int|M#Point>", [], []}} =
               out.defs[:mk].type
    end

    test "a union with NO rekeyed member is left completely alone", %{env: env} do
      # Union<Bool|Int> mentions nothing being rekeyed, so it must keep its key and
      # its ctors untouched — the pass must not churn unrelated generated families.
      bool = {:data, :Bool, [], []}

      env =
        Inductive.declare(env, Inductive.family(:"Union<Bool|Int>", [], [], 0), [
          Inductive.ctor(:"Union<Bool|Int>$Bool", [{:v, bool}], [], [Grade.unrestricted()]),
          Inductive.ctor(:"Union<Bool|Int>$Int", [{:v, {:int_type}}], [], [Grade.unrestricted()])
        ])

      out = Resolution.rekey_module_env(env, "M", MapSet.new([:Point]))

      assert Map.has_key?(out.families, :"Union<Bool|Int>")
      assert Map.has_key?(out.ctors, :"Union<Bool|Int>$Int")
    end
  end

  # `Union.family_key/1`'s `Union<…>` vs `Disjoint<…>` PREFIX is computed from each
  # member's `runtime_class/1`, which recognises well-known erasure shapes (`Nat`,
  # `Bool`, `Bounded`, `List`) by matching their BARE, unqualified family atom
  # (`:Nat`). `Resolution.rekey_module_env/3` rewrites a shadowed member's payload
  # type to a QUALIFIED atom (`:"M#Nat"`) and then RECOMPUTES the family key from
  # that rewritten member set — so `runtime_class` sees `:"M#Nat"`, fails every bare
  # pattern, and falls through to `:unsupported`. `Nat` and `Int` both genuinely
  # erase to Erlang integers and OVERLAP, so the prefix must stay `Disjoint<…>`
  # (tag load-bearing) after rekeying, exactly as it was before. `:unsupported`
  # does not overlap `:integer` (only `:atom`/itself get that treatment), so the
  # recomputed key silently flips to `Union<…>` — misclassifying a union whose tag
  # IS load-bearing as one whose tag is not.
  describe "shadowing across an import: a well-known runtime class survives rekeying" do
    alias Cure.Core.{Env, Grade}
    alias Cure.Elab.Resolution

    test "Nat | Int stays Disjoint<...> after Nat is rekeyed to a qualified name" do
      nat = {:data, :Nat, [], []}
      ukey = :"Disjoint<Int|Nat>"

      env =
        %Env{}
        |> Inductive.declare(Inductive.family(:Nat, [], [], 0), [Inductive.ctor(:Z, [], [])])
        |> Inductive.declare(Inductive.family(ukey, [], [], 0), [
          Inductive.ctor(:"Disjoint<Int|Nat>$Int", [{:v, {:int_type}}], [], [Grade.unrestricted()]),
          Inductive.ctor(:"Disjoint<Int|Nat>$Nat", [{:v, nat}], [], [Grade.unrestricted()])
        ])

      out = Resolution.rekey_module_env(env, "M", MapSet.new([:Nat]))

      new_key = :"Disjoint<Int|M#Nat>"
      assert Map.has_key?(out.families, new_key)
      refute Map.has_key?(out.families, :"Union<Int|M#Nat>")
    end
  end

  # `union_renames/3` (resolution.ex) makes ONE pass over `Map.keys(env.families)`,
  # accumulating renames into `amap` as it goes. If a union family (the OUTER union)
  # has a member whose payload type embeds ANOTHER union family's type (the INNER
  # union, nested inside e.g. a `List(...)`, not flattened because it is not the
  # top-level member type), and the fold visits the OUTER union BEFORE the INNER one,
  # the outer's new key is computed against a STALE `amap` that does not yet contain
  # the inner union's rename — so the outer union's computed "new key" is wrongly
  # identical to its OLD key (no rename recorded), even though its constructor
  # argument type IS correctly rewritten afterward (by the unconditional
  # `rekey_ctors`/`rekey_term` pass, which runs with the FINAL, complete `amap`). The
  # family ends up registered under a NAME that lies about its own content.
  #
  # `Map.keys/1` order is not insertion order — empirically, interning the OUTER
  # union's atom before the INNER union's atom (regardless of which `Inductive.declare`
  # call runs first) reliably produces the outer-before-inner fold order needed to
  # observe this.
  describe "nested unions: a union family embeds ANOTHER union family as a member payload" do
    alias Cure.Core.{Env, Grade}
    alias Cure.Elab.Resolution

    setup do
      # Intern the OUTER key's atom BEFORE the inner one (see module comment).
      outer_key = :"Union<AAA|MyList(Union<Int|Shadowed>)>"
      inner_key = :"Union<Int|Shadowed>"

      env =
        %Env{}
        |> Inductive.declare(Inductive.family(:Shadowed, [], [], 0), [
          Inductive.ctor(:ShadowedMk, [], [])
        ])
        |> Inductive.declare(Inductive.family(:AAA, [], [], 0), [
          Inductive.ctor(:AAAMk, [], [])
        ])
        |> Inductive.declare(Inductive.family(:MyList, [{:a, {:type, 0}}], [], 1), [])
        |> Inductive.declare(Inductive.family(outer_key, [], [], 0), [
          Inductive.ctor(:"#{outer_key}$AAA", [{:v, {:data, :AAA, [], []}}], [], [
            Grade.unrestricted()
          ]),
          Inductive.ctor(
            :"#{outer_key}$MyList(#{inner_key})",
            [{:v, {:data, :MyList, [{:data, inner_key, [], []}], []}}],
            [],
            [Grade.unrestricted()]
          )
        ])
        |> Inductive.declare(Inductive.family(inner_key, [], [], 0), [
          Inductive.ctor(:"Union<Int|Shadowed>$Int", [{:v, {:int_type}}], [], [Grade.unrestricted()]),
          Inductive.ctor(:"Union<Int|Shadowed>$Shadowed", [{:v, {:data, :Shadowed, [], []}}], [], [
            Grade.unrestricted()
          ])
        ])

      # Confirms this fixture actually reproduces the outer-first fold order this
      # test targets (a change in map internals would silently invalidate the test
      # otherwise, rather than failing loudly for the intended reason).
      assert [^outer_key, ^inner_key] =
               env.families |> Map.keys() |> Enum.filter(&Union.union_family?/1)

      %{env: env, outer_key: outer_key, inner_key: inner_key}
    end

    test "the OUTER union's stored key matches its own rewritten content", %{
      env: env,
      outer_key: outer_key
    } do
      out = Resolution.rekey_module_env(env, "M", MapSet.new([:Shadowed]))

      new_inner_key = :"Union<Int|M#Shadowed>"
      new_outer_key = :"Union<AAA|MyList(#{new_inner_key})>"

      # The old, un-renamed outer key must be GONE...
      refute Map.has_key?(out.families, outer_key)
      # ...replaced by a family whose NAME reflects the fully-transitively-rewritten
      # inner union, not a stale reference to the inner union's OLD key.
      assert Map.has_key?(out.families, new_outer_key)

      ctor = out.ctors[:"#{new_outer_key}$MyList(#{new_inner_key})"]
      assert [{:v, {:data, :MyList, [{:data, ^new_inner_key, [], []}], []}}] = ctor.args
    end
  end
end
