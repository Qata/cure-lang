defmodule Cure.Compiler.GroupDecoratorAttrTest do
  use ExUnit.Case, async: true

  # Classic (non-dependent) module: routes through Cure.Compiler.Codegen.
  # `@group` sits above `mod` (the canonical placement post-cutover).
  @classic_src "@group(:test)\nmod GroupClassicFixture\n  fn f() -> Int = 1\n"

  # Dependent module (indexed type ⇒ Cure.Elab.Emit pipeline). `@group` sits
  # above `mod`, describing the whole module.
  @dependent_src """
  @group(:test)
  mod GroupDependentFixture
    type Nat = Z | S(Nat)
    type Vector(a: Type) indices (n: Nat)
      empty : Vector(a, Z)
  end
  """

  setup do
    dir = Path.join(System.tmp_dir!(), "cure_group_attr_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf(dir) end)
    {:ok, dir: dir}
  end

  defp compile_and_read_group(src, name, dir) do
    path = Path.join(dir, "#{name}.cure")
    File.write!(path, src)

    {:ok, module, _warnings} =
      Cure.Compiler.compile_file(path, output_dir: dir, check_types: false)

    beam = Path.join(dir, "#{module}.beam")

    {:ok, {^module, [attributes: attrs]}} =
      :beam_lib.chunks(String.to_charlist(beam), [:attributes])

    Keyword.get(attrs, :group)
  end

  test "classic module carries @group as a BEAM :group attribute", %{dir: dir} do
    assert compile_and_read_group(@classic_src, "GroupClassicFixture", dir) == [:test]
  end

  test "dependent module carries @group as a BEAM :group attribute", %{dir: dir} do
    assert compile_and_read_group(@dependent_src, "GroupDependentFixture", dir) == [:test]
  end
end
