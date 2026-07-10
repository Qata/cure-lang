defmodule Cure.EditionTest do
  use ExUnit.Case, async: true
  alias Cure.Edition

  test "current is the newest known edition and is valid" do
    assert Edition.current() == "2026"
    assert Edition.valid?("2026")
    assert Edition.all() == ["2026"]
  end

  test "parse accepts a known edition and rejects an unknown one" do
    assert Edition.parse("2026") == {:ok, "2026"}
    assert Edition.parse("2062") == {:error, {:unknown_edition, "2062"}}
  end

  test "compare orders editions by integer year" do
    assert Edition.compare("2026", "2026") == :eq
    # a hypothetical newer edition compares greater (compare must not itself
    # gate on the allow-list, so ordering logic is testable ahead of minting)
    assert Edition.compare("2025", "2026") == :lt
    assert Edition.compare("2027", "2026") == :gt
  end

  describe "pragma_edition/1" do
    test "reads a file-leading @edition pragma, skipping comments and blanks" do
      src = "## header comment\n\n@edition(\"2026\")\nmod M\n"
      assert Cure.Edition.pragma_edition(src) == "2026"
    end

    test "returns nil when the first non-trivia item is not an @edition pragma" do
      assert Cure.Edition.pragma_edition("mod M\n@edition(\"2026\")\n") == nil
    end

    # Iteration 12 (audit): the pre-scan was line-based and fence-blind. The lexer
    # consumes a `###...###` fenced multi-line doc comment into a single
    # :doc_comment token, so an `@edition(...)` line INSIDE the fence is never a
    # pragma. But `trivia_line?` skipped only the opening `###` (it starts with
    # `#`) and then read the fenced-out `@edition("2025")` as the first
    # substantive line — resolving a pragma the compiler never sees. The pre-scan
    # must skip the whole fenced block, exactly like the lexer.
    test "an @edition inside a ###-fenced doc comment is not a pragma" do
      src = "###\n@edition(\"2025\")\n###\nmod Foo do\n  def start() = 0\nend\n"
      assert Cure.Edition.pragma_edition(src) == nil
    end

    test "a real pragma after a ###-fenced doc comment is still read" do
      src = "###\ndoc prose\n###\n@edition(\"2026\")\nmod M\n"
      assert Cure.Edition.pragma_edition(src) == "2026"
    end

    test "an indented ###-fence is skipped as a whole" do
      src = "  ###\n  @edition(\"2025\")\n  ###\nmod M\n"
      assert Cure.Edition.pragma_edition(src) == nil
    end
  end

  describe "resolve/1 precedence" do
    test "a file pragma wins over everything" do
      assert Cure.Edition.resolve(%{source: "@edition(\"2026\")\nmod M\n"}) == {:ok, "2026"}
    end

    test "an unknown pragma edition is an error" do
      assert {:error, {:unknown_edition, "2062"}} =
               Cure.Edition.resolve(%{source: "@edition(\"2062\")\nmod M\n"})
    end

    test "no pragma and no project dir falls back to the latest edition" do
      assert Cure.Edition.resolve(%{source: "mod M\n"}) == {:ok, Cure.Edition.current()}
    end
  end

  describe "missing-edition advisory (spec §3.2 point 2)" do
    setup do
      Cure.Edition.reset_advisory!()
      :ok
    end

    defp write_toml_no_edition do
      dir = Path.join(System.tmp_dir!(), "cureadv_#{System.unique_integer([:positive])}")
      File.mkdir_p!(dir)
      File.write!(Path.join(dir, "Cure.toml"), "[project]\nname = \"demo\"\nversion = \"0.1.0\"\n")
      dir
    end

    test "a Cure.toml with no edition key logs a one-time advisory" do
      dir = write_toml_no_edition()

      log =
        ExUnit.CaptureLog.capture_log(fn ->
          assert {:ok, _} = Cure.Edition.resolve(%{source: "mod M\n", project_dir: dir})
        end)

      assert log =~ "no `edition` declared"
    end

    test "the advisory fires only once across repeated resolutions" do
      dir = write_toml_no_edition()

      log =
        ExUnit.CaptureLog.capture_log(fn ->
          Cure.Edition.resolve(%{source: "mod M\n", project_dir: dir})
          Cure.Edition.resolve(%{source: "mod M\n", project_dir: dir})
        end)

      assert length(Regex.scan(~r/no `edition` declared/, log)) == 1
    end
  end
end
