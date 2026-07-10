defmodule Cure.Stdlib.TypeclassTailElaboratesTest do
  @moduledoc """
  The #21 typeclass tail — `Std.Equatable`, `Std.Ord`, `Std.Show` — was written
  against the legacy `proto`/`impl` surface, which the dependent elaborator
  rejects with `{:unsupported_container, :protocol}`. All three are migrated to
  `interface`/`implementation`; their derived helpers (`ne`, `lt`/`le`/`gt`/`ge`,
  `show_line`) dispatch through a `where`-introduced dictionary.

  `Std.Equatable` and `Std.Ord` now elaborate end-to-end on the dependent
  pipeline (both ride `String = List(Char)` via `use Std.String`).

  `Std.Ord`'s `Char` instance compares Unicode code points via
  `Std.Char.code_point` (a `Char -> Int` coercion) and Int `<`; its `String`
  instance is lexicographic over `List(Char)` through a top-level
  `compare_string` recursion. No `<` is used on a non-primitive operand, so the
  old `{:unsupported_operand_type, :<}` blocker is gone. (The comparison
  *operators* `<`/`>` on non-primitive operands still route nowhere yet — that
  is the separate keystone step that unblocks `core`/`test`.)

  `Std.Show` remains surface-migrated and classic-building (see
  `Cure.Compiler.InterfaceDispatchCodegenTest`) but does NOT yet elaborate on
  the dependent pipeline: its instance bodies use `<>`, which desugars to the
  `Std.Semigroup.combine` method; without `use Std.Semigroup` in scope that is
  an `:unknown_global`. Adding the import then surfaces a deeper `:bad_motive`
  on the `<>`-built bodies, so Show needs more than an import. It is pinned
  below as the current dependent-pipeline blocker so a future fix flips a red
  assertion to green rather than passing silently.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  defp elaborates(path) do
    Program.elaborate(File.read!(path))
  end

  test "Std.Equatable elaborates on the dependent pipeline" do
    assert {:ok, _env} = elaborates("lib/std/equatable.cure")
  end

  test "Std.Ord elaborates on the dependent pipeline (code-point + lexicographic)" do
    assert {:ok, _env} = elaborates("lib/std/ord.cure")
  end

  test "Std.Show is blocked on `<>` desugaring to an out-of-scope `combine`" do
    assert {:error, :unknown_global} = elaborates("lib/std/show.cure")
  end
end
