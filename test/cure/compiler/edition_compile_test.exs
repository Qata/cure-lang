# F-A (audit iteration 3): the compile pipeline (Cure.Compiler) must resolve each
# source's edition (file @edition pragma > Cure.toml [project].edition > default)
# and drive the lexer/parser with it — spec §3.2/§4. Before this wiring the build
# path was edition-blind: it always lexed under current() and never consulted
# resolve/1, so a typo'd edition compiled silently (§3.1 violation) and §4's
# edition-parameterized lexing was dead on the build path.
defmodule Cure.Compiler.EditionCompileTest do
  use ExUnit.Case, async: true

  setup do
    dir = Path.join(System.tmp_dir!(), "cure_edcompile_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    {:ok, dir: dir}
  end

  test "compile fails loudly on an unknown @edition pragma (resolve gate, before codegen)" do
    src = "@edition(\"9999\")\nmod M\n  fn f() -> Int = 1\n"

    assert {:error, {:edition_error, {:unknown_edition, "9999"}}} =
             Cure.Compiler.compile_string(src, file: "t.cure", emit_events: false)
  end

  test "compile fails loudly when the project manifest declares an unknown edition", %{dir: dir} do
    File.write!(Path.join(dir, "Cure.toml"), "[project]\nname = \"x\"\nedition = \"1999\"\n")
    src = "mod M\n  fn f() -> Int = 1\n"

    assert {:error, {:edition_error, {:unknown_edition, "1999"}}} =
             Cure.Compiler.compile_string(src,
               file: "t.cure",
               emit_events: false,
               project_dir: dir
             )
  end

  test "compile honors a valid manifest edition (resolve is consulted, no crash)", %{dir: dir} do
    File.write!(Path.join(dir, "Cure.toml"), "[project]\nname = \"x\"\nedition = \"2026\"\n")
    src = "mod M\n  fn f() -> Int = 1\n"

    assert {:ok, _mod, _warns} =
             Cure.Compiler.compile_string(src,
               file: "t.cure",
               emit_events: false,
               project_dir: dir,
               output_dir: dir
             )
  end

  test "compile with a valid @edition pragma still compiles", %{dir: dir} do
    src = "@edition(\"2026\")\nmod M\n  fn f() -> Int = 1\n"

    assert {:ok, _mod, _warns} =
             Cure.Compiler.compile_string(src, file: "t.cure", emit_events: false, output_dir: dir)
  end
end
