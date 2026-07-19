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

  @doc """
  Fold the `precedencegroup`/`infix`/`prefix`/`postfix` declarations found in
  `ast` into `base`, returning the extended `FixityTable`. Groups are registered
  first (so `higher_than`/`lower_than` links resolve against groups declared
  later in the same source) then operator lexemes bind to those groups.

  Table-independent: reads only the harvested declaration nodes, never the
  fixity table it is building, so it is safe to call while assembling the
  built-in table at compile time.
  """
  @spec build_table(term(), FixityTable.t()) :: FixityTable.t()
  def build_table(ast, base) do
    nodes = collect_fixity(ast)

    table =
      Enum.reduce(nodes, base, fn
        {:precedencegroup, meta, _}, acc ->
          FixityTable.add_group(acc, Keyword.fetch!(meta, :name),
            assoc: Keyword.get(meta, :assoc, :left),
            higher_than: Keyword.get(meta, :higher_than, []),
            lower_than: Keyword.get(meta, :lower_than, [])
          )

        _other, acc ->
          acc
      end)

    Enum.reduce(nodes, table, fn
      {:fixity, meta, _}, acc -> add_fixity_op(acc, meta)
      _other, acc -> acc
    end)
  end

  defp add_fixity_op(table, meta) do
    lexeme = Keyword.get(meta, :operator)
    group = Keyword.get(meta, :group)

    if is_binary(lexeme) and is_atom(group) and not is_nil(group) do
      case Keyword.get(meta, :fixity) do
        :infix -> FixityTable.add_infix(table, lexeme, group)
        :prefix -> FixityTable.add_prefix(table, lexeme, group)
        :postfix -> FixityTable.add_postfix(table, lexeme, group)
        _ -> table
      end
    else
      table
    end
  end

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
