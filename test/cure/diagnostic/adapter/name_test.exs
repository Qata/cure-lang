defmodule Cure.Diagnostic.Adapter.NameTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.{Adapter, Renderer, SourceRegistry}
  alias Cure.Diagnostic.Adapter.Name, as: NameAdapter

  test "the name family retains candidate identity and emits a unique typo edit" do
    source = "pritn\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:name_test, source, "name.cure")
    {:ok, span} = SourceRegistry.span(registry, :name_test, 0, 5)

    candidate = %{
      id: {:value, :"Std.Io", :print, 1},
      name: "print",
      namespace: :value,
      visibility: :public,
      arity: 1,
      owner: :"Std.Io",
      imported: true,
      requires_import: false,
      origin: :import
    }

    opts = [span: span, candidates: [candidate], arity: 1]
    direct = NameAdapter.unknown_name(:value, "pritn", opts)

    assert Adapter.unknown_name(:value, "pritn", opts) == direct
    assert [detail] = direct.payload.candidate_details
    assert detail.candidate_id == candidate.id
    assert detail.owner == :"Std.Io"
    assert detail.namespace == :value
    assert detail.origin == :import

    assert [suggestion] = direct.suggestions
    assert suggestion.applicability == :machine_applicable
    assert [%{span: ^span, replacement: "print"}] = suggestion.edits

    assert Renderer.plain(direct, registry, width: 80) ==
             """
             -- UNKNOWN VALUE [E091] ---------------------------------------------- name.cure

             `pritn` is not available in this value namespace.

             at name.cure:1:1
             1 | pritn
               | ^^^^^ `pritn` was not found

             Hint: Did you mean `print`?
             """
             |> String.trim_trailing()
  end

  test "an unavailable candidate remains qualified and never becomes a speculative edit" do
    diagnostic =
      NameAdapter.unknown_name(:value, "pritn",
        candidates: [
          %{
            id: :qualified_print,
            name: "print",
            namespace: :value,
            owner: :"Std.Io",
            visibility: :public,
            imported: false,
            requires_import: true,
            origin: :stdlib
          }
        ]
      )

    assert diagnostic.payload.candidate_details |> hd() |> Map.take([:candidate_id, :owner, :requires_import]) ==
             %{candidate_id: :qualified_print, owner: :"Std.Io", requires_import: true}

    assert [suggestion] = diagnostic.suggestions
    assert suggestion.applicability == :maybe_incorrect
    assert suggestion.edits == []
    assert suggestion.message =~ "`Std.Io.print`"
    assert suggestion.message =~ "Qualify it or import its module"
  end

  test "raw producer variants route exhaustively through the name family" do
    variants = [
      {:unknown_global, :missing},
      {:unbound_var, :missing},
      {:unknown_family, :Missing},
      {:unknown_ctor, :Missing},
      {:unknown_constructor, :Missing},
      {:unknown_field, :Point, :z, [:x, :y]},
      {:no_such_interface, :Missing},
      {:unknown_interface_method, :Eq, :missing}
    ]

    for error <- variants do
      assert NameAdapter.from_error(error) == Adapter.from_error(error)
      assert NameAdapter.from_error(error).code == "E091"
    end

    diagnostic = NameAdapter.from_error({:ambiguous_name, :shared, ["Left", "Right"]})
    assert diagnostic == Adapter.from_error({:ambiguous_name, :shared, ["Left", "Right"]})
    assert diagnostic.code == "E089"
    assert diagnostic.payload == %{namespace: :value, name: "shared", owners: ["Left", "Right"]}
    assert hd(diagnostic.suggestions).message =~ "`Left.shared` or `Right.shared`"

    assert_raise Cure.Diagnostic.UnhandledError, fn ->
      NameAdapter.from_error({:ordinary_type_failure, :not_a_name_error})
    end
  end
end
