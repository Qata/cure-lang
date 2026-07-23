defmodule Cure.Diagnostic.Adapter.TypeTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.{Adapter, ExpectationOrigin, Renderer, SourceRegistry, TypeProblem}
  alias Cure.Diagnostic.Adapter.Type, as: TypeAdapter

  test "the canonical type family preserves contextual prose, both source labels, and exact output" do
    source = "fn run() -> Int = true\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:type_test, source, "type.cure")
    {:ok, expected_span} = SourceRegistry.span(registry, :type_test, 12, 15)
    {:ok, actual_span} = SourceRegistry.span(registry, :type_test, 18, 22)

    problem = %TypeProblem{
      kind: :type_mismatch,
      actual: "Bool",
      expected: "Int",
      origin: %ExpectationOrigin{kind: :annotation, span: expected_span},
      expression: :literal,
      span: actual_span
    }

    direct = TypeAdapter.from_error(problem)
    assert Adapter.from_error(problem) == direct

    assert Renderer.plain(direct, registry, width: 80) ==
             """
             -- ANNOTATION DOES NOT MATCH [E093] ---------------------------------- type.cure

             This expression does not match the type written in its annotation.

             Expected: Int
             Found:    Bool

             at type.cure:1:19
             1 | fn run() -> Int = true
               |             ---   ^^^^ the expectation comes from here; this expression has the wrong type
             """
             |> String.trim_trailing()
  end

  test "Core and constraints remain debug-only at the family boundary" do
    problem = %TypeProblem{
      kind: :conversion_failure,
      actual: {:data, :Actual, [], []},
      expected: {:data, :Expected, [], []},
      origin: %ExpectationOrigin{kind: :annotation},
      debug: %{constraints: [{:cannot_unify, :actual, :expected}]}
    }

    regular = TypeAdapter.from_error(problem)
    debug = TypeAdapter.from_error(problem, debug: true)

    refute Map.has_key?(regular.payload, :debug)
    refute Renderer.json(regular) =~ "cannot_unify"
    assert debug.payload.debug.details == problem.debug
    assert Renderer.json(debug) =~ "cannot_unify"
  end

  test "legacy contextual failures expose their retained repair as a source-tagged hint" do
    source = "value\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:legacy_type, source, "type_context.cure")
    {:ok, span} = SourceRegistry.span(registry, :legacy_type, 0, 5)

    diagnostic = Adapter.from_error(:not_a_function, span: span)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             """
             -- APPLICATION TARGET IS NOT CALLABLE [E093] ----------------- type_context.cure

             This value is used as a function, but its type is not callable.

             at type_context.cure:1:1
             1 | value
               | ^^^^^ apply a function or constructor value

             Hint: Apply a function or constructor value
             """
             |> String.trim_trailing()
  end

  test "raw kernel conversion failures normalize through the type family" do
    raw = {:conversion_failure, {:data, :Bool, [], []}, {:data, :Int, [], []}}
    assert TypeAdapter.from_error(raw) == Adapter.from_error(raw)

    contextual =
      {:source_context, raw,
       %{
         expectation_origin: :call_argument,
         checking: :consume,
         argument_index: 0,
         expression_category: :call
       }}

    direct = TypeAdapter.from_error(contextual)
    assert Adapter.from_error(contextual) == direct
    assert direct.code == "E093"
    assert direct.title == "Argument has the wrong type"
    assert direct.payload.origin.owner == :consume
    assert direct.payload.origin.index == 0

    assert_raise Cure.Diagnostic.UnhandledError, fn ->
      TypeAdapter.from_error({:unknown_global, :missing})
    end
  end
end
