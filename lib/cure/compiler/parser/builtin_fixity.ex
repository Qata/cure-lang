defmodule Cure.Compiler.Parser.BuiltinFixity do
  @moduledoc """
  The built-in operator `FixityTable`, derived from `Std.Operators`
  (`operators.cure`).

  This lives in the compiler/parser layer — not in `Cure.Stdlib.Preload` — so
  the Pratt parser can reach it at *bootstrap*. `Preload` bakes its stdlib
  dependency maps at Elixir compile time by running `DepGraph.scan/1`, which
  re-enters `Parser.parse/2`; the parser needs the built-in fixity table to bind
  operators (and the `.` projection) correctly while that scan runs, but
  `Preload`'s own module is not yet available during its compilation. Housing the
  table here — a module compiled before `Preload` — breaks that cycle: the parser
  depends only on this module, never on `Preload`.

  The table is memoized in `:persistent_term` under a fixed key. `operators.cure`
  is a compiler-internal, static source within a running VM, so re-parsing it on
  every `Parser.parse` call (the loop seeds each module's table from it) would be
  wasted work. No invalidation, because the stdlib is fixed for a compiler build.
  """

  alias Cure.Compiler.Parser.FixityTable
  alias Cure.Stdlib.Paths

  @fixity_table_key {__MODULE__, :builtin_fixity_table}

  # Captured at Elixir compile time from the in-tree `lib/std/`.
  @stdlib_source_dir Path.expand("../../../std", __DIR__)

  @doc "The memoized built-in fixity table."
  @spec table() :: FixityTable.t()
  def table do
    case :persistent_term.get(@fixity_table_key, :__missing__) do
      :__missing__ ->
        table = compute()
        :persistent_term.put(@fixity_table_key, table)
        table

      table ->
        table
    end
  end

  @doc """
  Extend an existing `FixityTable` with the `precedencegroup`/`infix`/… decls
  found in `ast`. Used by the parser to layer a module's own fixity declarations
  onto the memoized built-in table.
  """
  @spec extend(FixityTable.t(), term()) :: FixityTable.t()
  def extend(base, ast), do: build(ast, base)

  # Parsing `operators.cure` re-enters `Parser.parse`, which itself seeds its
  # state from `table/0`. A process flag breaks that recursion: while building,
  # the parser seeds an EMPTY table (safe — `operators.cure` is all inert
  # declarations, no operator expressions to bind).
  defp compute do
    prev = Process.put(:cure_building_fixity_table, true)

    try do
      with {:ok, path} <- operators_source_path(),
           {:ok, source} <- File.read(path),
           {:ok, tokens} <- Cure.Compiler.Lexer.tokenize(source, emit_events: false),
           {:ok, ast} <-
             Cure.Compiler.Parser.parse(tokens,
               file: path,
               emit_events: false,
               prelude_macros: false
             ) do
        build(ast, FixityTable.new())
      else
        _ -> FixityTable.new()
      end
    after
      case prev do
        nil -> Process.delete(:cure_building_fixity_table)
        _ -> Process.put(:cure_building_fixity_table, prev)
      end
    end
  end

  # Locate `operators.cure`: prefer the in-tree `lib/std/` copy captured at
  # Elixir compile time, then fall back to the resolved runtime source dir
  # (`priv/std/` in a packaged build).
  defp operators_source_path do
    candidates =
      [Path.join(@stdlib_source_dir, "operators.cure")] ++
        case Paths.source_dir() do
          nil -> []
          dir -> [Path.join(dir, "operators.cure")]
        end

    case Enum.find(candidates, &File.exists?/1) do
      nil -> :not_found
      path -> {:ok, path}
    end
  end

  # Reduce the parsed `Std.Operators` AST into a FixityTable: register every
  # precedence group first (so `higher_than` links resolve), then every
  # operator lexeme.
  defp build(ast, base) do
    nodes = collect_fixity_nodes(ast)

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
      {:fixity, meta, _}, acc ->
        add_fixity_op(acc, meta)

      _other, acc ->
        acc
    end)
  end

  defp add_fixity_op(table, meta) do
    lexeme = Keyword.get(meta, :operator)
    group = Keyword.get(meta, :group)

    if is_binary(lexeme) and is_atom(group) and not is_nil(group) do
      opts = [builtin: Keyword.get(meta, :builtin, false)]

      case Keyword.get(meta, :fixity) do
        :infix -> FixityTable.add_infix(table, lexeme, group, opts)
        :prefix -> FixityTable.add_prefix(table, lexeme, group, opts)
        :postfix -> FixityTable.add_postfix(table, lexeme, group, opts)
        _ -> table
      end
    else
      table
    end
  end

  # Deep-walk the AST collecting `{:precedencegroup, …}` / `{:fixity, …}` nodes
  # in source order. A hand-rolled walk (not `Macro.prewalk`) because these
  # inert declaration nodes are not standard Elixir AST.
  defp collect_fixity_nodes(ast) do
    ast |> do_collect_fixity([]) |> Enum.reverse()
  end

  defp do_collect_fixity(node, acc) when is_tuple(node) do
    acc =
      case node do
        {tag, meta, _} when tag in [:precedencegroup, :fixity] and is_list(meta) -> [node | acc]
        _ -> acc
      end

    node |> Tuple.to_list() |> Enum.reduce(acc, &do_collect_fixity/2)
  end

  defp do_collect_fixity(list, acc) when is_list(list) do
    Enum.reduce(list, acc, &do_collect_fixity/2)
  end

  defp do_collect_fixity(_other, acc), do: acc
end
