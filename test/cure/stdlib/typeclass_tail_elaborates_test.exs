defmodule Cure.Stdlib.TypeclassTailElaboratesTest do
  @moduledoc """
  The #21 typeclass tail — `Std.Equatable`, `Std.Comparable`, `Std.Show` — was
  written against the legacy `proto`/`impl` surface, which the dependent
  elaborator rejects with `{:unsupported_container, :protocol}`. All three are
  migrated to `interface`/`implementation`.

  `Std.Equatable` and `Std.Comparable` now elaborate end-to-end on the dependent
  pipeline (both ride `String = List(Char)` via `use Std.String`).

  `Std.Comparable`'s `Char` instance compares Unicode code points via
  `Std.Char.code_point` (a `Char -> Int` coercion) and Int `<`; its `String`
  instance is lexicographic over `List(Char)` through a top-level
  `compare_string` recursion. `compare` is the only method — the comparison
  *operators* `<`/`>`/`<=`/`>=` are the surface and route through it (a
  non-primitive `a < b` desugars to `compare(a, b) == LessThan()`), so there
  are no `lt`/`le`/`gt`/`ge` named helpers.

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

  test "Std.Comparable elaborates on the dependent pipeline (code-point + lexicographic)" do
    assert {:ok, _env} = elaborates("lib/std/comparable.cure")
  end

  test "Std.Show is blocked on `<>` desugaring to an out-of-scope `combine`" do
    assert {:error, :unknown_global} = elaborates("lib/std/show.cure")
  end
end
