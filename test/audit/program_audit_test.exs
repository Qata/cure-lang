defmodule Cure.Audit.ProgramTest do
  @moduledoc """
  Audit findings for `lib/cure/elab/program.ex` (whole-program elaboration
  driver). Each test is a specific, executable claim about CORRECT behavior;
  every test here is red today.

  Root cause shared by all three findings: `program.ex` has TWO different
  code paths that build an `Cure.Core.Env` from a parsed AST —

    1. the top-level entry (`check_ast/2` -> `check_ast_elixir_core/1`), which
       runs `check_no_duplicate_defs/types/ctors` before elaborating, AND
    2. every imported-module path (`module_slice_env/1`, used for direct
       `use` imports, and `import_source_env/2`, used for transitive nested
       imports), which calls `elaborate_declarations/3` DIRECTLY and never
       runs any duplicate check.

  `Cure.Core.Env.add_def/5` and `Cure.Core.Inductive.declare/3` both register
  by plain `Map.put` (confirmed by reading `lib/cure/core/inductive.ex`), so
  whichever code path skips the duplicate check silently keeps only the LAST
  same-named declaration and drops the others with no error. This is exactly
  the soundness hole `check_no_duplicate_defs` was written to close (see
  `test/cure/elab/dup_def_test.exs`), just reachable through two doors that
  check never covers.

  P1 shows the SAME underlying gap fires even with NO `use` import at all:
  two sibling `mod` blocks in a single parsed AST are flattened into one
  shared `env.defs` by `declarations/1` with no per-module rekeying (unlike
  the `use`-import collision path, which has dedicated rekey machinery in
  `Cure.Elab.Resolution` that `program.ex` never invokes for this case).
  `test/cure/elab/cross_module_names_test.exs` asserts only `{:ok, _}` for
  this scenario and never inspects which body survives, so the loss has gone
  unnoticed by the existing suite.
  """
  use ExUnit.Case, async: false
  @moduletag :audit

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp elaborate(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    Program.check_ast(ast)
  end

  # ---------------------------------------------------------------------------
  # P1: sibling `mod` blocks in ONE source/AST silently overwrite each other's
  # same-named function in the shared `env.defs`, with no rekeying at all.
  #
  # `declarations/1` (program.ex:401-431) flattens ALL sibling modules'
  # declarations into ONE list before `elaborate_declarations/3` ever runs
  # (program.ex:136: `elaborate_declarations(declarations(ast), env0, ...)`),
  # so `Env.add_def` for module B's `foo` (Map.put, program.ex never scopes
  # this per module) plainly overwrites module A's `foo` that was registered
  # moments earlier in the SAME pass. `check_no_duplicate_defs` cannot catch
  # this because it is intentionally scoped PER MODULE (comment at
  # program.ex:42-49): two sibling modules sharing a name is meant to be
  # LEGITIMATE (mirrors 5 stdlib modules all declaring `map`), resolved by
  # rekeying -- but the rekey machinery (`Cure.Elab.Resolution.rekey_module_env`)
  # is only ever invoked from `shadow_resolved_imports/1` for `use`-imported
  # modules, never for sibling `mod` blocks declared in the same AST.
  #
  # Correct behavior: module A's own declared body for `foo` must still be
  # the one A's own code sees/keeps after elaborating the whole file, exactly
  # as if A had been elaborated alone. Today it is replaced by B's body
  # instead, because B is later in declaration order.
  # ---------------------------------------------------------------------------
  test "P1: sibling modules sharing a function name must not silently overwrite each other's body" do
    only_a_src = """
    mod A
      fn foo() -> Int = 1
    end
    """

    only_b_src = """
    mod B
      fn foo() -> Int = 2
    end
    """

    both_src = """
    mod A
      fn foo() -> Int = 1
    end
    mod B
      fn foo() -> Int = 2
    end
    """

    {:ok, only_a} = elaborate(only_a_src)
    {:ok, only_b} = elaborate(only_b_src)
    {:ok, both} = elaborate(both_src)

    # Sanity: the fixture genuinely distinguishes the two bodies.
    refute only_a.defs[:foo].body == only_b.defs[:foo].body

    # A's own `foo` must survive elaborating the combined file exactly as it
    # elaborated alone -- today `both.defs[:foo].body` silently equals
    # `only_b`'s body instead (B, declared later, wins the shared bare key).
    assert both.defs[:foo].body == only_a.defs[:foo].body
  end

  # ---------------------------------------------------------------------------
  # P2/P3: an imported (`use Std.X`) module's OWN declarations never pass
  # through `check_no_duplicate_defs` / `check_no_duplicate_types`, unlike
  # the top-level module. `module_slice_env/1` (program.ex:539-550), which
  # elaborates every direct `use` target, calls `elaborate_declarations/3`
  # straight from the parsed AST with none of the three duplicate guards that
  # `check_ast/2` (program.ex:34-40) runs for the entry module. The exact same
  # `Map.put`-overwrite mechanics apply (`Env.add_def` / `Inductive.declare`),
  # so a duplicate inside a `Std.*` source silently keeps only the last
  # declaration instead of being rejected like an equivalent duplicate at the
  # top level (`test/cure/elab/dup_def_test.exs`,
  # `test/cure/elab/cross_module_names_test.exs`).
  #
  # Uses the established stdlib_source_dir override fixture pattern from
  # `test/cure/elab/global_namespace_soundness_test.exs` to point the ONLY
  # import resolution path (`import_source_path/1`) at a tmp copy of the real
  # stdlib plus one extra fixture module.
  # ---------------------------------------------------------------------------
  describe "P2/P3: duplicate declarations inside an imported module bypass the same-module dup checks" do
    setup do
      real_src = Cure.Stdlib.Paths.source_dir()

      tmp =
        Path.join(
          System.tmp_dir!(),
          "cure_program_audit_dup_import_#{System.unique_integer([:positive])}"
        )

      File.mkdir_p!(tmp)
      # Copy the real stdlib source in BEFORE the override takes effect (the
      # established pattern): once `:stdlib_source_dir` is set it is the ONLY
      # source_dir candidate, so auto-prelude's Std.Bool/Std.Nat must still
      # live inside `tmp`.
      File.cp_r!(real_src, tmp)

      File.write!(Path.join(tmp, "dupfn.cure"), """
      mod Std.DupFn
        fn foo() -> Int = 1
        fn foo() -> Int = 2
      end
      """)

      File.write!(Path.join(tmp, "duptype.cure"), """
      mod Std.DupType
        type Widget = MkA
        type Widget = MkB
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

    test "P2: a duplicate fn name inside an imported Std module is rejected, not silently kept last-wins" do
      src = "mod P\n  use Std.DupFn\n  fn f() -> Int = foo()\nend\n"

      # Correct behavior (mirrors dup_def_test.exs for the top-level module):
      # Std.DupFn declares `foo` twice within its own module, which must be
      # rejected the same way it would be if `Std.DupFn`'s body were pasted
      # directly into the top-level module. Today this instead returns
      # `{:ok, _}`, silently keeping only the second `foo` (== 2).
      assert {:error, {:duplicate_definition, :foo}} = elaborate(src)
    end

    test "P3: a duplicate type name inside an imported Std module is rejected, not silently kept last-wins" do
      src = "mod Q\n  use Std.DupType\n  fn g() -> Widget = MkB\nend\n"

      # Correct behavior (mirrors check_no_duplicate_types for the top-level
      # module): Std.DupType declares `Widget` twice within its own module.
      # Today this instead returns `{:ok, _}`, silently keeping only the
      # second `type Widget = MkB` (`env.families[:Widget]` overwritten via
      # plain `Map.put` in `Cure.Core.Inductive.declare/3`).
      assert {:error, {:duplicate_type, :Widget}} = elaborate(src)
    end
  end
end
