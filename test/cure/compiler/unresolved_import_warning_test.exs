defmodule Cure.Compiler.UnresolvedImportWarningTest do
  use ExUnit.Case, async: false

  @moduletag :tmp_dir

  test "imported-but-unresolvable unqualified call compiles with a W088 warning",
       %{tmp_dir: dir} do
    # `use Ghost` imports a module that exports no `phantom/0`; the call
    # falls back to a local call (unchanged behavior) but must WARN now.
    ghost = Path.join(dir, "ghost.cure")
    File.write!(ghost, "mod Ghost\n  fn real() -> Int = 1\n")

    user = Path.join(dir, "user.cure")

    File.write!(user, """
    mod GhostUser
      use Ghost
      fn start() -> Int = phantom()
    """)

    out = Path.join(dir, "ebin")

    assert {:ok, _mod, _w} =
             Cure.Compiler.compile_file(ghost, output_dir: out, emit_events: false)

    :ok = Cure.Compiler.load_emitted(:"Cure.Ghost", out)

    # `phantom` is neither a local function of GhostUser nor an export of
    # Ghost, so codegen's fallback emits a local call to an undefined
    # function; erl_lint always rejects that, so this case surfaces on the
    # lint-error path (extended to a 3-tuple carrying the codegen warnings)
    # rather than the {:ok, ...} path. See the plan's Task 7, Step 3.
    assert {:error, {:beam_lint_error, _lint, warnings}} =
             Cure.Compiler.compile_file(user,
               output_dir: out,
               emit_events: false,
               check_types: false
             )

    assert Enum.any?(warnings, fn
             {:unresolved_import, "phantom", 0, mods, _line} -> :"Cure.Ghost" in mods
             _ -> false
           end)
  end
end
