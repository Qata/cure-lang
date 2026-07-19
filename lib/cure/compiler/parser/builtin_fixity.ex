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

  alias Cure.Compiler.Parser.{FixityTable, FixityScan}

  @fixity_table_key {__MODULE__, :builtin_fixity_table}

  # Captured at Elixir compile time from the in-tree `lib/std/`.
  @stdlib_source_dir Path.expand("../../../std", __DIR__)

  # Cheap textual gate: a source with no fixity-declaration keyword contributes
  # nothing to the fixity table, so it is skipped before the expensive harvest.
  @fixity_kw ~r/^\s*(infix|prefix|postfix|precedencegroup)\b/m

  @doc "The memoized built-in fixity table."
  @spec table() :: FixityTable.t()
  def table do
    # Provenance-safe to memo unconditionally: `bundled_prelude_sources/0` only
    # ever reads compiler-bundled stdlib paths under `@stdlib_source_dir`, never
    # project source, so the closure can't vary with the source universe. User
    # `@prelude` providers reach a module via the parser's `:prelude_providers`
    # option (FixityResolver), NOT through this table.
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

  # Union fixity over the compiler-bundled `@prelude` stdlib closure. Each
  # source is harvested (table-independent) then folded via `build/2`.
  #
  # The `:cure_building_fixity_table` guard is retained as a defensive belt: the
  # path below calls `Parser.harvest/4` directly (with an explicit empty `base`),
  # which never consults `session_builtin_fixity_table/0`, so it does not re-enter
  # `table/0` today. The guard would matter only if a future change routed
  # prelude-source scanning back through the full `Parser.parse/2` (whose line-190
  # `session_builtin_fixity_table/0` calls `table/0`), reintroducing the recursion.
  defp compute do
    prev = Process.put(:cure_building_fixity_table, true)

    try do
      Enum.reduce(bundled_prelude_sources(), FixityTable.new(), fn source_ast, acc ->
        build(source_ast, acc)
      end)
    after
      case prev do
        nil -> Process.delete(:cure_building_fixity_table)
        _ -> Process.put(:cure_building_fixity_table, prev)
      end
    end
  end

  # Compiler-bundled `@prelude` stdlib modules that declare operators, as
  # harvested ASTs (node lists). Located via the fixed `@stdlib_source_dir`
  # wildcard — independent of the project source universe.
  #
  # `@stdlib_source_dir` holds ~100 files; harvesting (full tolerant parse of)
  # every one on the first `table/0` call — which fires inside `preload.ex`'s
  # compile-time `DepGraph.scan` — is a large, wasted cost. A file that contains
  # no `infix`/`prefix`/`postfix`/`precedencegroup` keyword cannot contribute a
  # single entry to the fixity table, so a cheap textual pre-check (`@fixity_kw`)
  # skips it BEFORE the expensive harvest. This is semantically identical to
  # harvesting all files (a skipped file would have folded to nothing) and keeps
  # the model uniform: no module is named; ANY `@prelude` file that declares a
  # fixity is picked up. Today only `operators.cure` matches.
  defp bundled_prelude_sources do
    @stdlib_source_dir
    |> Path.join("*.cure")
    |> Path.wildcard()
    |> Enum.sort()
    |> Enum.flat_map(fn path ->
      with {:ok, source} <- File.read(path),
           true <- Regex.match?(@fixity_kw, source),
           {:ok, tokens} <- Cure.Compiler.Lexer.tokenize(source, emit_events: false) do
        exprs = Cure.Compiler.Parser.harvest(tokens, path, FixityTable.new(), Cure.Edition.current())
        if FixityScan.prelude?(exprs), do: [exprs], else: []
      else
        _ -> []
      end
    end)
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
