defmodule Cure.Elab.TypeDeclarationTest do
  @moduledoc """
  Regressions around what a type declaration actually declares.

  `type X = Y` with a single bare right-hand side is ambiguous, and the parser cannot
  resolve it — it tags the RHS `variant: true` and defers:

      type MyNat = Nat        # an ALIAS: `Nat` names a type in scope
      type Unit  = MkUnit     # a one-constructor ENUM: `MkUnit` names no type

  Both used to take the alias branch, which installed `Unit := {:data, :MkUnit, [], []}`
  with a hardcoded kind of `{:type, 0}` and never checked it — so a one-constructor enum
  silently became an alias to a family that does not exist. Nothing checked because the
  only kernel call on a typealias was `maybe_certify/2`, whose whole job is to SWALLOW
  errors: for a function body a failure there means "does not certify as total, stop
  δ-unfolding", never "ill-typed" (the body's `Kernel.check/3` already ran). A typealias
  had no prior check, so a genuine kind error was discarded like a benign non-termination
  verdict.

  Three consequences, all fixed:

    * `typealias Bad = Z` (aliasing a Nat CONSTRUCTOR) reported `{:ok, _}`. Idris
      (`Bad : Type; Bad = Z`) and Lean (`def Bad : Type := Z`) reject it.
    * an `interface` declares its dictionary as a record family of the same name, but
      `:interface` was missing from the per-module duplicate-type scan, so a sibling
      `type Equatable = ...` silently overwrote it.
    * a plain zero-type-param enum was built by a duplicate constructor pipeline that
      reimplemented a strict subset of `idx_to_core/5` and rejected arrow types outright,
      so `type Callback = Wrap((Int) -> Int)` failed while the identical `rec Callback`
      and `type Callback(a) = ...` succeeded. That pipeline is deleted.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Emit, Program}

  @nat "  type Nat = Z | S(Nat)\n"

  describe "typealias" do
    test "an alias to a type is accepted" do
      assert {:ok, _} = Program.elaborate("mod M\n" <> @nat <> "  typealias Good = Nat\nend\n")
    end

    test "an alias to a constructor is rejected — a constructor is not a type" do
      assert {:error, {:typealias_not_a_type, :Bad, _}} =
               Program.elaborate("mod M\n" <> @nat <> "  typealias Bad = Z\nend\n")
    end
  end

  describe "type X = Y" do
    test "resolves to an ALIAS when Y names a type in scope" do
      src =
        "mod M\n" <>
          @nat <> "  type MyNat = Nat\n  fn f(n: MyNat) -> MyNat = S(n)\nend\n"

      assert {:ok, _} = Program.elaborate(src)
    end

    test "resolves to a one-constructor ENUM when Y names no type" do
      src = "mod M\n  type Unit = MkUnit\n  fn u() -> Unit = MkUnit()\nend\n"

      assert {:ok, env} = Program.elaborate(src)
      assert {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Test.UnitEnum", functions: [:u])
      assert apply(mod, :u, []) == :MkUnit
    end

    test "a one-constructor enum whose constructor already exists is a duplicate" do
      assert {:error, {:duplicate_constructor, %{name: :Z, spans: [first, second]}}} =
               Program.elaborate("mod M\n" <> @nat <> "  type Bad = Z\nend\n")

      assert first.start_line == 2
      assert second.start_line == 3
    end
  end

  describe "name collisions within a module" do
    test "an interface's dictionary record collides with a sibling type declaration" do
      src = """
      mod X
        interface Equatable(a)
          fn eq(x: a, y: a) -> Bool
        type Equatable = Foo | Bar
      end
      """

      assert {:error, {:duplicate_type, %{name: :Equatable, spans: [first, second]}}} =
               Program.elaborate(src)

      assert first.start_line == 2
      assert second.start_line == 4
    end
  end

  describe "constructor field types" do
    test "a plain enum constructor accepts a function-typed field, like a record" do
      src = "mod M\n  type Callback = Wrap((Int) -> Int)\nend\n"

      assert {:ok, _} = Program.elaborate(src)
    end

    test "a negative occurrence in a function-typed field is still rejected by positivity" do
      # Admitting arrow fields must not admit the Curry paradox. `MkBad : (Bad -> Nat) -> Bad`
      # puts `Bad` to the left of an arrow in its own constructor.
      src = "mod M\n" <> @nat <> "  type Bad = MkBad((Bad) -> Nat)\nend\n"

      assert {:error, error} = Program.elaborate(src, file: "positivity.cure")
      assert {:non_strictly_positive, :"M#MkBad"} = Program.semantic_error(error)

      {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "positivity.cure", src)
      rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 80)

      assert diagnostic.code == "E103"
      assert diagnostic.primary.span.start_line == 3
      assert diagnostic.primary.span.start_column == 14
      assert diagnostic.primary.span.end_column == 19
      assert rendered =~ "3 |   type Bad = MkBad((Bad) -> Nat)"
      assert rendered =~ "^^^^^ this recursive type definition is not strictly positive"
      assert rendered =~ "Hint: Move the recursive type out of function-input positions"
    end
  end
end
