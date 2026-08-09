defmodule Cure.Compiler.InterfaceBenchmarkTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.InterfaceBenchmark

  test "reports cold and warm module-interface timings separately" do
    root = Path.join(System.tmp_dir!(), "cure_interface_benchmark_#{System.unique_integer([:positive])}")
    path = Path.join(root, "bench.cure")
    File.mkdir_p!(root)
    suffix = System.unique_integer([:positive])
    File.write!(path, "mod Bench#{suffix}\n  fn answer() -> Int = 42\n")

    on_exit(fn -> File.rm_rf!(root) end)
    expected_module = "Bench#{suffix}"

    assert {:ok, report} = InterfaceBenchmark.run([path], warm_iterations: 2)
    assert report.pipeline == :canonical
    assert report.source_count == 1
    assert report.cold.total_us >= 0
    assert report.cold.rebuilt_modules == [expected_module]
    assert report.cold.phases.module_check >= 0
    assert [%{modules: [^expected_module], elapsed_us: elapsed}] = report.cold.components
    assert elapsed >= 0

    assert length(report.warm) == 2

    assert Enum.all?(report.warm, fn sample ->
             sample.total_us >= 0 and sample.rebuilt_modules == [] and sample.phases.module_check >= 0
           end)
  end
end
