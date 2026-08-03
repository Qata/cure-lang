defmodule Cure.Compiler.ModuleSkeleton.Declaration do
  @moduledoc false

  @enforce_keys [:key, :name, :namespace, :visibility, :owner]
  defstruct key: nil,
            name: nil,
            namespace: nil,
            visibility: nil,
            owner: nil,
            span: nil,
            header: nil
end

defmodule Cure.Compiler.ModuleSkeleton do
  @moduledoc false

  alias Cure.Compiler.ModuleSkeleton.Declaration

  @enforce_keys [:identity, :module_name, :source_path]
  defstruct identity: nil,
            module_name: nil,
            source_path: nil,
            declarations: %{}

  @type t :: %__MODULE__{}

  @spec collect(tuple() | list(), {String.t(), String.t()}, Path.t()) :: t()
  def collect(ast, {package, module_name} = identity, source_path) do
    declarations =
      ast
      |> declaration_nodes()
      |> Enum.reduce(%{}, fn node, declarations ->
        case declaration(node, package, module_name) do
          nil -> declarations
          %Declaration{} = declaration -> Map.put(declarations, {declaration.namespace, declaration.name}, declaration)
        end
      end)

    %__MODULE__{
      identity: identity,
      module_name: module_name,
      source_path: source_path,
      declarations: declarations
    }
  end

  defp declaration_nodes({:container, meta, body}) when is_list(meta) and is_list(body) do
    if Keyword.get(meta, :container_type) in [:module, :proof], do: body, else: []
  end

  defp declaration_nodes({:block, _meta, items}) when is_list(items), do: items
  defp declaration_nodes(_), do: []

  defp declaration({:function_def, meta, _body} = node, package, module_name) when is_list(meta) do
    with name when is_binary(name) <- Keyword.get(meta, :name) do
      visibility = if Keyword.get(meta, :visibility, :public) == :public, do: :public, else: :private

      %Declaration{
        key: {package, module_name, :value, name},
        name: name,
        namespace: :value,
        visibility: visibility,
        owner: {package, module_name},
        span: source_span(meta),
        header: node
      }
    end
  end

  defp declaration(_node, _package, _module_name), do: nil

  defp source_span(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{name: %Cure.Diagnostic.Span{} = span} -> span
      %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = span} -> span
      _ -> nil
    end
  end
end
