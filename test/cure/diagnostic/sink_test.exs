defmodule Cure.Diagnostic.SinkTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.{Operational, Sink}

  test "collects diagnostics and renders them with shared options" do
    diagnostic = Operational.file_read("demo.cure", :enoent)
    sink = Sink.new(format: :plain, width: 72) |> Sink.emit(diagnostic)

    assert [rendered] = Sink.render_all(sink)
    assert rendered =~ "E095"
    assert rendered =~ "demo.cure"
    assert length(sink.diagnostics) == 1
  end

  test "flush writes diagnostics and clears the batch" do
    {:ok, device} = StringIO.open("")
    sink = Sink.new(format: :plain, output_device: device) |> Sink.emit(Operational.usage("cure check"))

    assert {:ok, flushed} = Sink.flush(sink)
    assert flushed.diagnostics == []
    {_input, output} = StringIO.contents(device)
    assert output =~ "E099"
  end

  test "machine formats preserve structured output" do
    diagnostic = Operational.usage("cure check")
    sink = Sink.new(format: :json) |> Sink.emit(diagnostic)
    assert [%{"code" => "E099"}] = Sink.render_all(sink)
  end

  test "LSP flush emits JSON rather than an Elixir inspection" do
    diagnostic = Operational.usage("cure check")
    {:ok, device} = StringIO.open("")
    sink = Sink.new(format: :lsp, output_device: device) |> Sink.emit(diagnostic)

    assert {:ok, _flushed} = Sink.flush(sink)
    {_input, output} = StringIO.contents(device)
    assert [%{"code" => "E099"}] = Jason.decode!(output)
  end
end
