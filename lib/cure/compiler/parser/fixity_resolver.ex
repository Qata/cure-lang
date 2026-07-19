defmodule Cure.Compiler.Parser.FixityResolver do
  @moduledoc """
  Assemble `fixity(M) = base ∪ ⋃ own(X) over use_reach(M) ∪ own(M) ∪ user
  prelude providers`, resolving the `use`-closure on demand by name (no
  precomputed DepGraph). Groups are merged before operators; a same-lexeme/
  different-group or same-name/different-body clash is a hard conflict.
  Reachability uses set-union, so `use` cycles need no special handling.
  Target modules are scanned with the tolerant harvest only — never a full
  `Parser.parse` — so this never recurses into itself.
  """

  alias Cure.Compiler.Parser.{FixityTable, FixityScan}
  alias Cure.Compiler.SourceResolver

  @spec assemble(FixityTable.t(), [tuple()], [String.t()], [String.t()], keyword()) ::
          {:ok, FixityTable.t()} | {:error, term()}
  def assemble(base, own_fixity, own_uses, prelude_providers, _opts \\ []) do
    seeds = Enum.uniq(own_uses ++ prelude_providers)

    with {:ok, reached_fixity} <- gather(seeds, MapSet.new(), [], base) do
      # own(M) is folded LAST so M's own declarations are still subject to the
      # same conflict rule against everything it imports.
      fold(base, reached_fixity ++ own_fixity)
    end
  end

  # BFS over the use-closure, accumulating each reached module's own fixity
  # nodes. `base` seeds each target's harvest so built-in operators in the
  # target's bodies don't misparse (Component 1).
  defp gather([], _seen, acc, _base), do: {:ok, acc}

  defp gather([name | rest], seen, acc, base) do
    if MapSet.member?(seen, name) do
      gather(rest, seen, acc, base)
    else
      seen = MapSet.put(seen, name)

      case SourceResolver.module_path(name) do
        {:ok, path} ->
          case File.read(path) do
            {:ok, source} ->
              scan = FixityScan.harvest_source(source, path, base)
              next = rest ++ Enum.map(scan.uses, & &1.target)
              gather(next, seen, acc ++ scan.fixity, base)

            {:error, _} ->
              gather(rest, seen, acc, base)
          end

        :not_found ->
          gather(rest, seen, acc, base)
      end
    end
  end

  # Groups first (ops reference them), then operators. Short-circuit on conflict.
  defp fold(base, nodes) do
    groups = Enum.filter(nodes, &match?({:precedencegroup, _, _}, &1))
    ops = Enum.filter(nodes, &match?({:fixity, _, _}, &1))

    with {:ok, t1} <- reduce_merge(base, groups),
         {:ok, t2} <- reduce_merge(t1, ops) do
      {:ok, t2}
    end
  end

  defp reduce_merge(table, nodes) do
    Enum.reduce_while(nodes, {:ok, table}, fn node, {:ok, t} ->
      case merge_node(t, node) do
        {:ok, t2} -> {:cont, {:ok, t2}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp merge_node(table, {:precedencegroup, meta, _}) when is_list(meta) do
    FixityTable.merge_group(table, Keyword.fetch!(meta, :name),
      assoc: Keyword.get(meta, :assoc, :left),
      higher_than: Keyword.get(meta, :higher_than, []),
      lower_than: Keyword.get(meta, :lower_than, [])
    )
  end

  defp merge_node(table, {:fixity, meta, _}) when is_list(meta) do
    lexeme = Keyword.get(meta, :operator)
    group = Keyword.get(meta, :group)
    fixity = Keyword.get(meta, :fixity)

    if is_binary(lexeme) and is_atom(group) and not is_nil(group) and
         fixity in [:infix, :prefix, :postfix] do
      FixityTable.merge_op(table, lexeme, fixity, group)
    else
      {:ok, table}
    end
  end

  defp merge_node(table, _), do: {:ok, table}
end
