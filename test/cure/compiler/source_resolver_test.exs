defmodule Cure.Compiler.SourceResolverTest do
  use ExUnit.Case, async: false
  alias Cure.Compiler.SourceResolver

  test "resolves a stdlib module name to its .cure source" do
    assert {:ok, path} = SourceResolver.module_path("Std.Operators")
    assert String.ends_with?(path, "operators.cure")
    assert File.exists?(path)
  end

  test "returns :not_found for an unknown module" do
    assert :not_found = SourceResolver.module_path("Totally.Bogus.Module")
  end

  @tag :tmp_dir
  test "resolves a user module by declared name from a source root", %{tmp_dir: dir} do
    file = Path.join(dir, "weird_name.cure")
    File.write!(file, "mod My.Widget\n  fn go() -> Int = 1\nend\n")

    prev = Process.get(:cure_source_roots, [])
    Process.put(:cure_source_roots, [dir])

    try do
      assert {:ok, ^file} = SourceResolver.module_path("My.Widget")
    after
      Process.put(:cure_source_roots, prev)
    end
  end
end
