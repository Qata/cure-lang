defmodule Cure.Diagnostic.Adapter.KernelTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.{Adapter, Renderer, SourceRegistry}
  alias Cure.Diagnostic.Adapter.Kernel, as: KernelAdapter

  test "strict positivity points at the negative occurrence and its constructor" do
    source = "MkBad Bad\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:positivity, source, "positivity.cure")
    {:ok, constructor_span} = SourceRegistry.span(registry, :positivity, 0, 5)
    {:ok, occurrence_span} = SourceRegistry.span(registry, :positivity, 6, 9)

    error =
      {:source_context, {:non_strictly_positive, :"Demo#MkBad"},
       %{
         span: occurrence_span,
         constructor_span: constructor_span,
         family_name: "Bad",
         precise_occurrence: true
       }}

    direct = KernelAdapter.from_error(error)
    assert Adapter.from_error(error) == direct

    assert Renderer.plain(direct, registry, width: 80) ==
             """
             -- RECURSIVE TYPE APPEARS IN A FUNCTION INPUT [E103] ----------- positivity.cure

             `Bad` appears in a function input stored by `MkBad`. A recursive type may appear
             in a stored function's result, but not in one of its inputs.

             at positivity.cure:1:7
             1 | MkBad Bad
               | ----- ^^^ this constructor stores the unsafe function type; recursive `Bad` is consumed here

             Hint: Move `Bad` to the function result, or make the input non-recursive
             """
             |> String.trim_trailing()
  end

  test "the kernel family rejects non-kernel variants" do
    assert_raise Cure.Diagnostic.UnhandledError, fn ->
      KernelAdapter.from_error({:unknown_global, :missing})
    end
  end

  test "trusted type rejections are owned by the kernel adapter" do
    source = "bad\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:kernel, source, "kernel.cure")
    {:ok, span} = SourceRegistry.span(registry, :kernel, 0, 3)

    errors = [
      {:index_mismatch, :details},
      {:cannot_unify, :actual, :expected},
      {:escaping_variable, 1},
      {:occurs_check, 1, :term},
      {:ctor_requires_checking_mode, :Family},
      {:bounded_bound_not_concrete, :bound},
      :arg_arity,
      :ctor_arity,
      :domain_mismatch,
      :grade_mismatch,
      :bad_motive,
      :not_a_type,
      :not_a_type_value,
      :universe_level,
      :universe_ceiling
    ]

    for error <- errors do
      direct = KernelAdapter.from_error(error, span: span)
      assert Adapter.from_error(error, span: span) == direct
      assert direct.code == "E093"
      assert direct.primary.span == span
      assert direct.payload.kind
    end

    rendered =
      KernelAdapter.from_error({:cannot_unify, :actual, :expected},
        span: span
      )
      |> Renderer.plain(registry, width: 80)

    assert rendered =~ "TYPES CANNOT BE UNIFIED [E093]"
    assert rendered =~ "^^^ change the expression or annotation so the types agree"
  end
end
