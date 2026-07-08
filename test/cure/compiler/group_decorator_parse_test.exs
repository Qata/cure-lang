defmodule Cure.Compiler.GroupDecoratorParseTest do
  use ExUnit.Case, async: true

  # Extract the `mod ...` container body from parse_source output, which may be
  # either the container tuple itself or a list wrapping it.
  defp module_body(ast) do
    case ast do
      {:container, meta, body} ->
        if Keyword.get(meta, :container_type) == :module, do: body, else: []

      list when is_list(list) ->
        Enum.find_value(list, [], fn
          {:container, meta, body} ->
            if Keyword.get(meta, :container_type) == :module, do: body, else: false

          _ ->
            false
        end)

      _ ->
        []
    end
  end

  test "@group(:core) is a standalone decorator node, never attached to the following fn" do
    src = "mod X\n  @group(:core)\n  fn f() -> Int = 1\n"
    {:ok, ast} = Cure.Compiler.parse_source(src)
    body = module_body(ast)

    # The module body carries a standalone @group decorator node.
    assert Enum.any?(body, fn
             {:decorator, meta, [{:literal, _, :core}]} ->
               Keyword.get(meta, :name) == "group"

             _ ->
               false
           end),
           "expected a standalone {:decorator, [name: \"group\"...], [:core]} node in #{inspect(body)}"

    # The following fn must NOT carry a `decorator:` meta entry.
    fn_node =
      Enum.find(body, fn
        {:function_def, meta, _} -> Keyword.get(meta, :name) == "f"
        _ -> false
      end)

    assert fn_node != nil, "expected fn f in module body: #{inspect(body)}"
    {:function_def, fn_meta, _} = fn_node

    refute Keyword.has_key?(fn_meta, :decorator),
           "fn f must not carry a decorator: entry, got #{inspect(fn_meta)}"
  end
end
