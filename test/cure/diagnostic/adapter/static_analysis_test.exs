defmodule Cure.Diagnostic.Adapter.StaticAnalysisTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.{Adapter, Renderer, SourceRegistry}
  alias Cure.Diagnostic.Adapter.StaticAnalysis

  test "relevance rejection labels the erased binder and its runtime use" do
    source = "n n\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:relevance, source, "relevance.cure")
    {:ok, binder_span} = SourceRegistry.span(registry, :relevance, 0, 1)
    {:ok, use_span} = SourceRegistry.span(registry, :relevance, 2, 3)

    error =
      {:source_context, {:erased_used_relevantly, %{binder: 2, site: :returned}},
       %{span: use_span, binder_span: binder_span, binder_name: :n}}

    direct = StaticAnalysis.from_error(error)
    assert Adapter.from_error(error) == direct

    assert Renderer.plain(direct, registry, width: 80) ==
             """
             -- ERASED VALUE USED RELEVANTLY [E104] -------------------------- relevance.cure

             The erased parameter `n` is used as the function's runtime result, but erased
             parameters do not exist at runtime.

             at relevance.cure:1:3
             1 | n n
               | - ^ `n` is erased here; this returns an erased value at runtime

             Hint: Declare `n` as a runtime parameter, or keep it out of runtime expressions
             """
             |> String.trim_trailing()
  end

  test "the static-analysis family rejects unrelated failures" do
    assert_raise Cure.Diagnostic.UnhandledError, fn ->
      StaticAnalysis.from_error({:conversion_failure, :actual, :expected})
    end
  end

  test "resource usage preserves declaration and earlier-use regions" do
    source = "x x x\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:usage, source, "usage.cure")
    {:ok, binder_span} = SourceRegistry.span(registry, :usage, 0, 1)
    {:ok, first_use} = SourceRegistry.span(registry, :usage, 2, 3)
    {:ok, second_use} = SourceRegistry.span(registry, :usage, 4, 5)

    error =
      {:source_context, {:usage_violation, %{binder: 0, declared: :linear, used: :unrestricted}},
       %{
         span: second_use,
         binder_span: binder_span,
         binder_name: :x,
         use_spans: [first_use, second_use]
       }}

    direct = StaticAnalysis.from_error(error)
    assert Adapter.from_error(error) == direct
    assert direct.code == "E117"
    assert Enum.map(direct.secondary, & &1.span) == [binder_span, first_use]

    rendered = Renderer.plain(direct, registry, width: 80)
    assert rendered =~ "another use on this path is here"
    assert rendered =~ "this parameter is declared `linear` here"
    assert rendered =~ "Hint: Pass `x` only to linear parameters"
  end
end
