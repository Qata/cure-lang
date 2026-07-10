defmodule Cure.Stdlib.TypeclassTailElaboratesTest do
  @moduledoc """
  The #21 typeclass tail — `Std.Equatable`, `Std.Ord`, `Std.Show` — was written
  against the legacy `proto`/`impl` surface, which the dependent elaborator
  rejects with `{:unsupported_container, :protocol}`. All three are migrated to
  `interface`/`implementation`; their derived helpers (`ne`, `lt`/`le`/`gt`/`ge`,
  `show_line`) dispatch through a `where`-introduced dictionary.

  `Std.Equatable` now elaborates end-to-end on the dependent pipeline (its
  `String` instance rides `String = List(Char)` via `use Std.String`).

  `Std.Ord` and `Std.Show` are surface-migrated and build under the classic
  pipeline (see `Cure.Compiler.InterfaceDispatchCodegenTest`), but do NOT yet
  elaborate on the dependent pipeline:
    * `Std.Ord` — its `String`/`Float` instances compare with `<`, and neither
      `String` (= `List(Char)`) nor `Char` (= `Bounded`) supports `<`
      (`{:unsupported_operand_type, :<}`). Blocked on lexicographic ordering
      for `List(Char)`.
    * `Std.Show` — its instance bodies use `<>`, which desugars to the
      `Std.Semigroup.combine` method; without `use Std.Semigroup` in scope that
      is an `:unknown_global`. Adding the import then surfaces a deeper
      `:bad_motive` on the `<>`-built bodies, so Show needs more than an import.
  Both are pinned below as the current dependent-pipeline blocker so a future
  fix flips a red assertion to green rather than passing silently.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  defp elaborates(path) do
    Program.elaborate(File.read!(path))
  end

  test "Std.Equatable elaborates on the dependent pipeline" do
    assert {:ok, _env} = elaborates("lib/std/equatable.cure")
  end

  test "Std.Ord is blocked on String/Char `<` (lexicographic ordering)" do
    assert {:error, {:unsupported_operand_type, :<}} = elaborates("lib/std/ord.cure")
  end

  test "Std.Show is blocked on `<>` desugaring to an out-of-scope `combine`" do
    assert {:error, :unknown_global} = elaborates("lib/std/show.cure")
  end
end
