# F2 (audit iteration 4): the @edition pragma errors and the compile-boundary
# {:edition_error, {:unknown_edition, _}} previously hit the catch-all formatter,
# which rendered a raw `inspect` tuple ("compilation error … {:edition_pragma_
# unknown, 1, 1}"). A "must fail loudly" error (spec §3.1) has to be legible: it
# names what is wrong and, for an unknown edition, lists the known ones.
defmodule Cure.Compiler.EditionErrorFormatTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Errors

  test "placement error explains the pragma must lead the file" do
    msg = Errors.format_error({:edition_pragma_placement, 4, 1}, "t.cure")
    assert msg =~ "edition"
    assert msg =~ ~r/first|before any/i
    refute msg =~ "compilation error"
  end

  test "malformed error names the required 4-digit single-line form" do
    msg = Errors.format_error({:edition_pragma_malformed, 1, 1}, "t.cure")
    assert msg =~ "4-digit"
    assert msg =~ "@edition(\"2026\")"
    refute msg =~ "compilation error"
  end

  test "unknown-pragma error lists the known editions" do
    msg = Errors.format_error({:edition_pragma_unknown, 1, 1}, "t.cure")
    assert msg =~ ~r/unknown edition/i
    assert msg =~ Cure.Edition.current()
    refute msg =~ "compilation error"
  end

  test "compile-boundary unknown-edition error names the value and the known set" do
    msg = Errors.format_error({:edition_error, {:unknown_edition, "9999"}}, "t.cure")
    assert msg =~ "9999"
    assert msg =~ ~r/unknown edition/i
    assert msg =~ Cure.Edition.current()
    refute msg =~ "compilation error"
  end
end
