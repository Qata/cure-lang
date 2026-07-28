defmodule Cure.Elab.ModuleMergeLawsTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  @moduletag :tmp_dir

  setup %{tmp_dir: dir} do
    previous = Process.get(:cure_source_roots)
    Process.put(:cure_source_roots, [dir])

    on_exit(fn ->
      if previous,
        do: Process.put(:cure_source_roots, previous),
        else: Process.delete(:cure_source_roots)

      Process.delete(:cure_module_loader_observer)
    end)

    :ok
  end

  test "loading one canonical interface repeatedly is idempotent", %{tmp_dir: dir} do
    provider =
      write!(
        dir,
        "provider.cure",
        """
        mod Merge.Provider
          typealias Code = Int
          fn same(value: Code) -> Code = value
        """
      )

    Process.put(:cure_module_loader_observer, self())

    assert {:ok, env} =
             Program.elaborate("""
             mod Merge.Consumer
               use Merge.Provider
               use Merge.Provider
               fn run(value: Code) -> Code = same(value)
             """)

    assert Map.has_key?(env.defs, :"Merge.Provider#Code")
    assert Map.has_key?(env.defs, :"Merge.Provider#same")

    compiling =
      collect_loader_events()
      |> Enum.filter(&match?({:compiling, "Merge.Provider", ^provider}, &1))

    assert compiling == [{:compiling, "Merge.Provider", provider}]
  end

  test "merge order preserves canonical identities and transparent aliases", %{tmp_dir: dir} do
    write!(
      dir,
      "base.cure",
      """
      mod Merge.Base
        typealias Code = Int
      """
    )

    write!(
      dir,
      "left.cure",
      """
      mod Merge.Left
        use Merge.Base
        fn left(value: Code) -> Code = value
      """
    )

    write!(
      dir,
      "right.cure",
      """
      mod Merge.Right
        use Merge.Base
        fn right(value: Code) -> Code = value
      """
    )

    projections =
      for imports <- [["Merge.Left", "Merge.Right"], ["Merge.Right", "Merge.Left"]] do
        source = """
        mod Merge.Consumer
          use #{Enum.at(imports, 0)}
          use #{Enum.at(imports, 1)}
          fn run(value: Merge.Base.Code) -> Merge.Base.Code = value
        """

        assert {:ok, env} = Program.elaborate(source)

        env.defs
        |> Map.take([
          :"Merge.Base#Code",
          :"Merge.Left#left",
          :"Merge.Right#right",
          :"Merge.Consumer#run"
        ])
      end

    assert [first, second] = projections
    assert first == second
    assert first[:"Merge.Base#Code"].body == {:data, :"Std.Int#Int", [], []}
  end

  defp collect_loader_events(acc \\ []) do
    receive do
      {:cure_module_loader, event} -> collect_loader_events([event | acc])
    after
      0 -> Enum.reverse(acc)
    end
  end

  defp write!(dir, name, source) do
    path = Path.join(dir, name)
    File.write!(path, source)
    path
  end
end
