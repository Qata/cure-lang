defmodule Cure.Elab.GlobalNamespaceSoundnessTest do
  @moduledoc """
  Global / constructor / family name-collision behaviour, and the recorded decision
  about it (see memory `global-def-collision-gap`, audit K12 slice-4).

  Two distinct cases, deliberately treated differently:

  1. **Same-name globals WITHIN A MODULE overwrite (soundness) — REJECTED.** Two
     function definitions in one module sharing a name would silently overwrite one
     another in `env.defs`. `check_no_duplicate_defs` (program.ex) rejects this with
     `{:duplicate_definition, name}` — a landed soundness fix this session. (Two
     SIBLING modules sharing a name is legitimate namespacing and is accepted — see
     `Cure.Elab.CrossModuleNamesTest`.)

  2. **A function COEXISTING with a constructor / type of the same name — ACCEPTED,
     and DECLINED as a tightening (analysis discipline, faithfulness-without-
     soundness).** Constructors (`env.ctors`) and functions (`env.defs`) live in
     separate tables, so there is no overwrite; the fn simply shadows the ctor in
     expression position (Idris/Agda unify the value namespace and would reject the
     clash — a PARITY difference, not a soundness hole). The kernel remains sound
     against it: whatever the E-layer resolves the name to, the trusted Core
     re-checks the result, so a mis-resolution can only produce a *rejected* type
     mismatch, never an accepted ill-typed program. The discriminating test below is
     the recorded proof. A rejection rule here is entangled with the design-gated
     K12 qualified-`Sym` work and the LOCKED type-shadowing Approach B, and is
     flagged for operator design sign-off — so it is NOT landed unilaterally.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Errors, Lexer, Parser}
  alias Cure.Elab.Program

  defp check(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    Program.check_ast(ast)
  end

  test "same-named globals within one module are rejected (no silent overwrite)" do
    src =
      "mod A\n  fn foo(x: Int) -> Int = x\n  fn foo(y: Int) -> Int = y\nend\n"

    assert {:error, {:duplicate_definition, :foo}} = check(src)
  end

  test "a fn/ctor name collision cannot smuggle an ill-typed value past the kernel" do
    # `C` is both a constructor (: Foo) and a fn (() -> Int). Passing `C()` where a
    # `Foo` is expected must never be accepted: resolution picks the fn (Int) and the
    # kernel rejects Int-vs-Foo. (Sound regardless of which side resolution favours.)
    src =
      "mod X\n  type Foo = C\n  fn C() -> Int = 3\n  fn wants(x: Foo) -> Int = 0\n  fn test() -> Int = wants(C())\nend\n"

    assert {:error, {:conversion_failure, _, _}} = check(src)
  end

  # ---------------------------------------------------------------------------
  # Cross-module global-def collisions (design 2026-07-08).
  #
  # The gap this describe pins: `use A` + `use B` where both export a plain
  # global `helper/1` silently overwrites in `env.defs` (last-merge-wins). The
  # fixture points the dependent elaborator's ONLY import path
  # (`import_source_path/1`, which resolves "Std.<Name>" -> "<source_dir>/<name>.cure")
  # at a tmp dir via the `:stdlib_source_dir` override — the established pattern
  # from `test/cure/stdlib/paths_test.exs`. The real stdlib dir is copied in FIRST
  # so every fixture module's auto-prelude (Std.Bool + Std.Nat) still resolves.
  # ---------------------------------------------------------------------------
  describe "cross-module global def collisions (design 2026-07-08)" do
    setup do
      real_src = Cure.Stdlib.Paths.source_dir()
      tmp = Path.join(System.tmp_dir!(), "cure_global_coll_test_#{System.unique_integer([:positive])}")
      File.mkdir_p!(tmp)
      # Copy the real stdlib source in BEFORE the override takes effect: once
      # `:stdlib_source_dir` is set it is the ONLY source_dir candidate consulted
      # (no fallback), so auto-prelude's Std.Bool/Std.Nat must live inside `tmp`.
      File.cp_r!(real_src, tmp)

      # `import_source_path/1` lowercases the module tail: Std.CollA -> colla.cure.
      File.write!(Path.join(tmp, "colla.cure"), """
      mod Std.CollA
        fn helper(x: Nat) -> Nat = Z()
        fn lonely_helper(x: Nat) -> Nat = Z()
      end
      """)

      File.write!(Path.join(tmp, "collb.cure"), """
      mod Std.CollB
        fn helper(x: Nat) -> Nat = S(Z())
      end
      """)

      previous = Application.get_env(:cure, :stdlib_source_dir)
      Application.put_env(:cure, :stdlib_source_dir, tmp)

      on_exit(fn ->
        case previous do
          nil -> Application.delete_env(:cure, :stdlib_source_dir)
          value -> Application.put_env(:cure, :stdlib_source_dir, value)
        end

        File.rm_rf!(tmp)
      end)

      :ok
    end

    # In-memory importing modules (ordinary `check/1` sources — only the two
    # fixture files above live on disk). Each `helper` body is an OBSERVABLY
    # DISTINCT ctor shape (Z / S(Z) / S(S(Z))) so a wrong-but-well-typed
    # resolution is distinguishable from the right one.
    defp fixture_bare_call do
      "mod P\n  use Std.CollA\n  use Std.CollB\n  fn f() -> Nat = helper(Z())\nend\n"
    end

    defp fixture_bare_value do
      "mod P\n  use Std.CollA\n  use Std.CollB\n" <>
        "  fn ap(g: (Nat) -> Nat, x: Nat) -> Nat = g(x)\n" <>
        "  fn f() -> Nat = ap(helper, Z())\nend\n"
    end

    defp fixture_qualified_both do
      "mod P\n  use Std.CollA\n  use Std.CollB\n" <>
        "  fn fa() -> Nat = Std.CollA.helper(Z())\n" <>
        "  fn fb() -> Nat = Std.CollB.helper(Z())\nend\n"
    end

    defp fixture_local_shadow do
      "mod P\n  use Std.CollA\n  use Std.CollB\n" <>
        "  fn helper(x: Nat) -> Nat = S(S(Z()))\n" <>
        "  fn f() -> Nat = helper(Z())\nend\n"
    end

    defp fixture_no_collision do
      "mod P\n  use Std.CollA\n  fn f() -> Nat = lonely_helper(Z())\nend\n"
    end

    test "bare call of a doubly-imported name is an ambiguity error, not last-merge-wins" do
      # TODAY: silently binds the last-merged helper -> {:ok, _}
      # AFTER: {:error, {:ambiguous_name, :helper, mods}} with both modules listed
      assert {:error, {:ambiguous_name, :helper, mods}} = check(fixture_bare_call())
      assert Enum.sort(mods) == ["Std.CollA", "Std.CollB"]
    end

    test "bare VALUE reference (higher-order arg) raises the same ambiguity error" do
      assert {:error, {:ambiguous_name, :helper, _}} = check(fixture_bare_value())
    end

    test "qualified calls reach their own module's body despite the collision" do
      # A wrong resolution (both qualified calls silently landing on the same
      # slice) is well-typed too, so inspect WHICH body each qualified key
      # resolved to, not just overall success.
      {:ok, env} = check(fixture_qualified_both())
      assert match?({:lam, _, {:ctor, :Z, []}}, env.defs[:"Std.CollA#helper"].body)
      assert match?({:lam, _, {:ctor, :S, [{:ctor, :Z, []}]}}, env.defs[:"Std.CollB#helper"].body)
    end

    test "local def shadows the imports; qualified still reaches them" do
      # Local helper(x) = S(S(Z())) -- a THIRD shape, so a bare call resolving to
      # the local body (correct) is distinguishable from either import's body.
      {:ok, env} = check(fixture_local_shadow())
      assert match?({:lam, _, {:ctor, :S, [{:ctor, :S, [{:ctor, :Z, []}]}]}}, env.defs[:helper].body)
      assert match?({:lam, _, {:ctor, :Z, []}}, env.defs[:"Std.CollA#helper"].body)
      assert match?({:lam, _, {:ctor, :S, [{:ctor, :Z, []}]}}, env.defs[:"Std.CollB#helper"].body)
    end

    test "non-colliding imported defs keep bare keys (no blanket re-keying)" do
      {:ok, env} = check(fixture_no_collision())
      assert Map.has_key?(env.defs, :lonely_helper)

      refute Enum.any?(Map.keys(env.defs), fn k ->
               String.ends_with?(Atom.to_string(k), "#lonely_helper")
             end)
    end

    test "E089 formatter names the code, both modules, and the qualified-form hint" do
      msg = Errors.format_error({:ambiguous_name, :helper, ["Std.CollA", "Std.CollB"]}, "x.cure")
      assert msg =~ "E089"
      assert msg =~ "Std.CollA"
      assert msg =~ "Std.CollB"
      assert msg =~ "Std.CollA.helper"
    end
  end
end
