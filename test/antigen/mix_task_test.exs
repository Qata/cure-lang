defmodule Mix.Tasks.AntigenTest do
  use ExUnit.Case, async: false
  import ExUnit.CaptureIO

  @tmp "tmp/antigen_task_test"
  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  test "mix antigen --count runs the explorer and prints a summary" do
    out =
      capture_io(fn ->
        Mix.Tasks.Antigen.run([
          "--count",
          "50",
          "--corpus",
          Path.join(@tmp, "corpus.sexp"),
          "--seeds",
          Path.join(@tmp, "seeds.sexp"),
          "--report-dir",
          @tmp
        ])
      end)

    assert out =~ "antigen" and (out =~ "infection" or out =~ "banked")
  end

  test "mix antigen generate --count harvests seeds and writes no infection reports" do
    Mix.Tasks.Antigen.run([
      "generate",
      "--count",
      "50",
      "--seeds",
      Path.join(@tmp, "seeds.sexp"),
      "--report-dir",
      @tmp
    ])

    assert File.exists?(Path.join(@tmp, "seeds.sexp"))
    refute File.exists?(Path.join(@tmp, "latest.txt"))
  end

  test "the wired-in default_gen draws :typed_term challenges (Tier B is live)" do
    seeds_path = Path.join(@tmp, "seeds_tier_b.sexp")

    Mix.Tasks.Antigen.run([
      "generate",
      "--count",
      "300",
      "--seeds",
      seeds_path,
      "--report-dir",
      @tmp
    ])

    kinds =
      Antigen.Corpus.stream(seeds_path)
      |> Enum.flat_map(fn
        {:ok, c} -> [c.kind]
        _ -> []
      end)
      |> MapSet.new()

    assert :typed_term in kinds
  end

  test "budget_to_count converts minutes to a round count via the fixed rounds-per-minute constant" do
    one_minute = Mix.Tasks.Antigen.budget_to_count("1m")
    assert one_minute > 0
    assert Mix.Tasks.Antigen.budget_to_count("2m") == one_minute * 2
  end
end
