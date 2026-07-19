defmodule Cure.Compiler.Parser.FixityScan do
  @moduledoc """
  Table-independent structural extraction from Cure source. Given a module's
  source (or an already-harvested node list), reports its own fixity /
  precedence-group declarations, `use` targets, `@prelude` flag, and module
  name — WITHOUT requiring a fully successful parse of its function bodies.
  Declarations are inert (their parse never consults the fixity table), so
  `synchronize_to_statement` recovery inside the harvest pass guarantees they
  survive even when surrounding expressions misparse.
  """

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Compiler.Parser.FixityTable

  @empty %{fixity: [], uses: [], prelude?: false, module: nil}

  @spec harvest_source(String.t(), String.t(), FixityTable.t()) :: %{
          fixity: [tuple()],
          uses: [%{target: String.t(), line: pos_integer()}],
          prelude?: boolean(),
          module: String.t() | nil
        }
  def harvest_source(source, file, base) do
    case Lexer.tokenize(source, emit_events: false) do
      {:ok, tokens} ->
        exprs = Parser.harvest(tokens, file, base, Cure.Edition.current())

        %{
          fixity: collect_fixity(exprs),
          uses: collect_uses(exprs),
          prelude?: prelude?(exprs),
          module: module_name(exprs)
        }

      _ ->
        @empty
    end
  end

  @spec collect_fixity(term()) :: [tuple()]
  def collect_fixity(ast),
    do:
      deep_collect(ast, fn
        {:fixity, _, _} = n -> [n]
        {:precedencegroup, _, _} = n -> [n]
        _ -> []
      end)

  @spec collect_uses(term()) :: [%{target: String.t(), line: pos_integer()}]
  def collect_uses(ast),
    do:
      deep_collect(ast, fn
        {:import, meta, _} when is_list(meta) ->
          case Keyword.get(meta, :source) do
            s when is_binary(s) -> [%{target: s, line: Keyword.get(meta, :line, 1)}]
            _ -> []
          end

        _ ->
          []
      end)

  @spec collect_use_targets(term()) :: [String.t()]
  def collect_use_targets(ast), do: ast |> collect_uses() |> Enum.map(& &1.target)

  @spec prelude?(term()) :: boolean()
  def prelude?(ast) do
    deep_reduce(ast, false, fn
      {:property, meta, _}, false when is_list(meta) -> Keyword.get(meta, :name) == "prelude"
      {_t, meta, _}, false when is_list(meta) -> match?({:prelude, _}, Keyword.get(meta, :decorator))
      _, acc -> acc
    end)
  end

  # Mirrors `DepGraph.find_module/1`'s filter exactly: `:container` is also
  # emitted for non-module constructs (`:struct`, `:primitive`, `:opaque`,
  # `:enum`, `:protocol`, `:trait`), so matching on the tag alone risks
  # returning a nested type's name instead of the module's, especially on a
  # `synchronize_to_statement`-recovered harvest of malformed source where
  # node order/nesting can't be assumed well-formed.
  @module_container_types [:module, :proof]

  @spec module_name(term()) :: String.t() | nil
  def module_name(ast) do
    deep_reduce(ast, nil, fn
      {:container, meta, _}, nil when is_list(meta) ->
        if Keyword.get(meta, :container_type) in @module_container_types,
          do: Keyword.get(meta, :name),
          else: nil

      _, acc ->
        acc
    end)
  end

  # -- deep walkers (mirror BuiltinFixity.collect_fixity_nodes shape) --------

  defp deep_collect(node, f) when is_tuple(node) do
    f.(node) ++ (node |> Tuple.to_list() |> deep_collect(f))
  end

  defp deep_collect(list, f) when is_list(list), do: Enum.flat_map(list, &deep_collect(&1, f))
  defp deep_collect(_other, _f), do: []

  defp deep_reduce(node, acc, f) when is_tuple(node) do
    acc = f.(node, acc)
    node |> Tuple.to_list() |> deep_reduce(acc, f)
  end

  defp deep_reduce(list, acc, f) when is_list(list),
    do: Enum.reduce(list, acc, fn el, a -> deep_reduce(el, a, f) end)

  defp deep_reduce(_other, acc, _f), do: acc
end
