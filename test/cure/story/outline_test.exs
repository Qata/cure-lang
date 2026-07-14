defmodule Cure.Story.OutlineTest do
  use ExUnit.Case, async: true

  alias Cure.Story.Outline

  test "classifies transparent lifted behavior modules" do
    root = Path.join(System.tmp_dir!(), "cure_outline_#{System.unique_integer([:positive])}")
    lib = Path.join(root, "lib")
    File.mkdir_p!(lib)

    on_exit(fn -> File.rm_rf!(root) end)

    File.write!(Path.join(lib, "objects.cure"), """
    actor Cure.OutlineActor with 0
    fsm Cure.OutlineFsm with 0
    sup Cure.OutlineSup
    app Cure.OutlineApp
    """)

    outline = Outline.build(root)

    assert [%{name: "Cure.OutlineApp"}] = outline.apps
    assert [%{name: "Cure.OutlineSup"}] = outline.supervisors
    assert [%{name: "Cure.OutlineActor"}] = outline.actors
    assert [%{name: "Cure.OutlineFsm"}] = outline.fsms
  end
end
