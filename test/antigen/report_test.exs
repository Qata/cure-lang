defmodule Antigen.ReportTest do
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Report}

  @tmp "tmp/antigen_report_test"
  setup do
    File.rm_rf!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  test "write_infection writes a full report and updates latest.txt before returning" do
    c = Challenge.new(kind: :stub, assay: "totality/diverging", label: :diverging, payload: %{term: {:type, 0}}, seed: 12345)
    assert {:ok, path} = Report.write_infection(@tmp, c, {:violation, :wrongly_certified}, %{discard_rate: 0.0})
    assert File.exists?(path)
    body = File.read!(path)
    assert body =~ "totality/diverging"
    assert body =~ "12345"
    assert body =~ "wrongly_certified"
    assert File.read!(Path.join(@tmp, "latest.txt")) =~ Path.basename(path)
  end

  test "breadcrumb is a single grep-surviving line naming the assay, seed, and file" do
    c = Challenge.new(kind: :stub, assay: "totality/diverging", label: :diverging, payload: %{term: {:type, 0}}, seed: 999)
    line = Report.breadcrumb(c, "tmp/antigen/failure-999-totality_diverging-1.txt")
    refute line =~ "\n"
    assert line =~ "ANTIGEN INFECTION" and line =~ "totality/diverging" and line =~ "seed=999"
  end
end
