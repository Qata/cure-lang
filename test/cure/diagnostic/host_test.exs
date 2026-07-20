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

  test "blames computed macro rejection on the authored invocation" do
    source = "fn run() -> Int = actor()\n"

    rendered =
      Host.render(
        {:computed_macro_error, [keyword: "actor", line: 1, col: 20],
         {:invalid_generated_syntax, {:raw_syntax_in_expansion, []}}},
        "demo.cure",
        source
      )

    assert rendered =~ "[E092]"
    assert rendered =~ "actor"
    assert rendered =~ "demo.cure"
    refute rendered =~ ":computed_macro_error"
  end

  test "converts code generation and BEAM lint failures to a stable internal code" do
    assert Host.render({:codegen_error, :bad_artifact}, "demo.cure") =~
             "[E101]"

    rendered = Host.render({:beam_lint_error, [], []}, "demo.cure")
    assert rendered =~ "[E101]"
    refute rendered =~ ":beam_lint_error"
  end

  test "converts legacy type and edition tuples into structured diagnostics" do
    type_rendered = Host.render({:type_mismatch, "expected Int, found String", [line: 1, col: 20]}, "demo.cure")
    assert type_rendered =~ "[E093]"

    edition_rendered = Host.render({:edition_pragma_malformed, 1, 1}, "demo.cure")
    assert edition_rendered =~ "[E094]"
    assert edition_rendered =~ "EDITION PRAGMA IS MALFORMED"
  end

  test "keeps macro validation failures structured at the host boundary" do
    rendered = Host.render({:rule_unpinned, ["every"]}, "macro.cure")

    assert rendered =~ "[E092]"
    assert rendered =~ "MACRO VALIDATION FAILED"
    assert rendered =~ "every"
    refute rendered =~ ":rule_unpinned"
  end

  test "renders erasure violations with the supported runtime classes" do
    rendered = Host.render({:unknown_erasure_class, :Handle, :banana}, "demo.cure")

    assert rendered =~ "[E102]"
    assert rendered =~ "banana"
    assert rendered =~ "pid"
    refute rendered =~ ":unknown_erasure_class"
  end

  test "renders trusted positivity and relevance rejections" do
    positivity = Host.render({:non_strictly_positive, :Bad}, "demo.cure")
    assert positivity =~ "[E103]"
    assert positivity =~ "Bad"

    relevance = Host.render({:erased_used_relevantly, %{binder: 0, site: :returned}}, "demo.cure")
    assert relevance =~ "[E104]"
    assert relevance =~ "returned"
  end

  test "renders declaration conflicts with their authored identity" do
    rendered = Host.render({:overlapping_overload, :move, 1}, "demo.cure")

    assert rendered =~ "[E105]"
    assert rendered =~ "move"
    assert rendered =~ "arity 1"
  end

  test "does not fall through to legacy formatting for an unregistered reason" do
    rendered = Host.render({:unregistered_compiler_reason, :detail}, "demo.cure")

    assert rendered =~ "[E101]"
    assert rendered =~ "fingerprint"
    refute rendered =~ ":unregistered_compiler_reason"
  end
end
