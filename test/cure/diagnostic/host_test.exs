defmodule Cure.Diagnostic.HostTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Host

  test "renders structured compiler failures through the shared diagnostic model" do
    source = "fn run() -> Int = missing_name\n"

    rendered =
      Host.render(
        {:source_context, {:unknown_global, "missing_name"}, %{line: 1, column: 20}},
        "demo.cure",
        source
      )

    assert rendered =~ "[E091]"
    assert rendered =~ "missing_name"
    assert rendered =~ "demo.cure"
    assert rendered =~ "^"
  end

  test "renders operational failures without fabricating source context" do
    rendered = Host.render({:file_read_error, "demo.cure", :enoent}, "demo.cure")

    assert rendered =~ "[E095]"
    assert rendered =~ "Cannot read `demo.cure`"
    refute rendered =~ "^"
  end

  test "renders macro syntax failures as contextual syntax diagnostics" do
    source = "fn run() -> Int = say nope\n"

    rendered = Host.render({:macro_use_mismatch, "say", {:literal, "hello"}, "nope", 1, 20}, "demo.cure", source)

    assert rendered =~ "[E094]"
    assert rendered =~ "MACRO SYNTAX DOES NOT MATCH"
    assert rendered =~ "demo.cure"
    refute rendered =~ ":macro_use_mismatch"
  end
end
