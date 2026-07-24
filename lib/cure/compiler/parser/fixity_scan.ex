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
    case Lexer.tokenize(source, file: file, emit_events: false) do
      {:ok, tokens} ->
        exprs = Parser.harvest(tokens, file, base, Cure.Edition.current())
        facts = collect_module_facts(exprs)

        %{
          fixity: facts.fixity,
          uses: facts.uses,
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

  @doc "Collect a harvested module's fixity declarations and imports in one walk."
  @spec collect_module_facts(term()) :: %{fixity: [tuple()], uses: [%{target: String.t(), line: pos_integer()}]}
  def collect_module_facts(ast) do
    {fixity, uses} = deep_scan(ast, [], [])
    %{fixity: Enum.reverse(fixity), uses: Enum.reverse(uses)}
  end

  @doc "Return exact authored name ranges for the selected precedence groups."
  @spec group_spans(term(), [atom()]) :: [Cure.Diagnostic.Span.t()]
  def group_spans(ast, groups) do
    wanted = MapSet.new(groups)

    ast
    |> collect_fixity()
    |> Enum.flat_map(fn
      {:precedencegroup, meta, _} when is_list(meta) ->
        with name when not is_nil(name) <- Keyword.get(meta, :name),
             true <- MapSet.member?(wanted, name),
             %Cure.MetaAST.SourceInfo{name: %Cure.Diagnostic.Span{} = span} <-
               Keyword.get(meta, :source_info) do
          [span]
        else
          _ -> []
        end

      _ ->
        []
    end)
  end

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

  defp deep_collect(node, f) do
    node
    |> deep_collect(f, [])
    |> Enum.reverse()
  end

  # Build the result backwards so a scanner never repeatedly copies the
  # already-visited prefix with `++`. The visitor is applied before children,
  # matching the old pre-order result; reversing the accumulated list restores
  # the same order at the boundary.
  defp deep_collect(node, f, acc) when is_tuple(node) do
    acc = Enum.reduce(f.(node), acc, &[&1 | &2])
    Enum.reduce(Tuple.to_list(node), acc, &deep_collect(&1, f, &2))
  end

  defp deep_collect(list, f, acc) when is_list(list),
    do: Enum.reduce(list, acc, &deep_collect(&1, f, &2))

  defp deep_collect(_other, _f, acc), do: acc

  defp deep_scan(node, fixity, uses) when is_tuple(node) do
    {fixity, uses} =
      case node do
        {:fixity, _, _} = value ->
          {[value | fixity], uses}

        {:precedencegroup, _, _} = value ->
          {[value | fixity], uses}

        {:import, meta, _} when is_list(meta) ->
          case Keyword.get(meta, :source) do
            source when is_binary(source) ->
              {fixity, [%{target: source, line: Keyword.get(meta, :line, 1)} | uses]}

            _ ->
              {fixity, uses}
          end

        _ ->
          {fixity, uses}
      end

    Enum.reduce(Tuple.to_list(node), {fixity, uses}, fn child, acc ->
      deep_scan(child, elem(acc, 0), elem(acc, 1))
    end)
  end

  defp deep_scan(list, fixity, uses) when is_list(list),
    do: Enum.reduce(list, {fixity, uses}, fn child, {f, u} -> deep_scan(child, f, u) end)

  defp deep_scan(_other, fixity, uses), do: {fixity, uses}

  defp deep_reduce(node, acc, f) when is_tuple(node) do
    acc = f.(node, acc)
    node |> Tuple.to_list() |> deep_reduce(acc, f)
  end

  defp deep_reduce(list, acc, f) when is_list(list),
    do: Enum.reduce(list, acc, fn el, a -> deep_reduce(el, a, f) end)

  defp deep_reduce(_other, acc, _f), do: acc
end
