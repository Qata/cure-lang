defmodule Cure.Compiler.DepGraph do
  @moduledoc """
  Dependency graph over a set of `.cure` source files (a *compile set*),
  built with the headless front end (`Cure.Compiler.parse_source/2`) —
  no app boot, no type checking, no codegen.

  Two edge kinds, deliberately distinct (see the 2026-07-08
  auto-import-order design spec, §3.1):

    * **order-edges** — `use` declarations targeting modules declared
      inside the compile set. These gate compile order: classic codegen
      resolves `use`-imported unqualified calls by probing loaded beams.
    * **closure-edges** — the superset (`use` + qualified-call targets +
      `@prelude` providers). These describe what must be *loadable at runtime*
      and drive preload closure, never compile order: qualified calls
      lower syntactically and are order-free.

  Ordering is deterministic: Kahn's algorithm, alphabetical (path)
  tie-break. Cycles among `use` declarations are NOT an error (spec §3.1
  as amended 2026-07-08): a strongly-connected component compiles as a
  group in alphabetical path order — Cure's compile-set model matches
  Rust's crate-internal modules, where cycles are legal — and each
  multi-member SCC is reported as a closed cycle walk so callers can
  emit the W086 warning. Duplicate module names remain a hard error.
  """

  defstruct nodes: %{}, modules: %{}

  @type node_info :: %{
          path: Path.t(),
          module: String.t() | nil,
          line: pos_integer() | nil,
          blank?: boolean(),
          parse_error: term() | nil,
          order_deps: [%{target: String.t(), line: pos_integer()}],
          closure_deps: [String.t()]
        }

  @type t :: %__MODULE__{
          nodes: %{Path.t() => node_info()},
          modules: %{String.t() => Path.t()}
        }

  # Behavior-shaped declarations are standard-library syntax macros and arrive
  # here as generic `lift_module` values, never as compiler-owned object kinds.
  @module_container_types [:module, :proof]

  @spec scan([Path.t()], keyword()) ::
          {:ok, t()} | {:error, {:duplicate_module, String.t(), [Path.t()]}}
  def scan(paths, opts \\ []) do
    known = MapSet.new(Keyword.get(opts, :known_modules, []))
    nodes = paths |> Enum.sort() |> Map.new(fn path -> {path, scan_file(path)} end)

    case duplicate_module(nodes) do
      {name, dup_paths} ->
        {:error, {:duplicate_module, name, Enum.sort(dup_paths)}}

      nil ->
        modules =
          for {path, %{module: m}} <- nodes, is_binary(m), into: %{}, do: {m, path}

        universe = MapSet.union(known, MapSet.new(Map.keys(modules)))

        prelude_modules =
          nodes
          |> Map.values()
          |> Enum.filter(&Map.get(&1, :prelude_provider?, false))
          |> MapSet.new(& &1.module)

        nodes =
          Map.new(nodes, fn {path, node} ->
            {path, finalize_node(node, modules, universe, prelude_modules)}
          end)

        {:ok, %__MODULE__{nodes: nodes, modules: modules}}
    end
  end

  @type cycle_hop :: %{module: String.t(), path: Path.t(), line: pos_integer()}

  @spec order(t()) :: {:ok, [Path.t()], [[cycle_hop()]]}
  def order(%__MODULE__{nodes: nodes, modules: modules}) do
    {blank, real} = Enum.split_with(nodes, fn {_p, n} -> n.blank? end)
    blank_paths = blank |> Enum.map(&elem(&1, 0)) |> Enum.sort()
    # Computed once, not per-dependency-per-node: `real` doesn't change
    # while building `edges`, so re-deriving this map inside the inner
    # filter (once per candidate dep) is pure waste, not a correctness
    # concern (the value is identical every time).
    real_map = Map.new(real)

    edges =
      Map.new(real, fn {path, node} ->
        deps =
          node.order_deps
          |> Enum.map(&modules[&1.target])
          |> Enum.filter(&(&1 != nil and &1 != path and Map.has_key?(real_map, &1)))
          |> Enum.uniq()

        {path, deps}
      end)

    {ordered, stuck_groups} = kahn(edges)
    cycles = Enum.map(stuck_groups, &cycle_info(&1, real_map, modules))
    {:ok, ordered ++ blank_paths, cycles}
  end

  @doc "In-set `use` deps by module name (values sorted). Baking input for Preload."
  @spec order_deps_map(t()) :: %{String.t() => [String.t()]}
  def order_deps_map(%__MODULE__{nodes: nodes, modules: modules}) do
    for {_path, %{module: m} = node} <- nodes, is_binary(m), into: %{} do
      deps =
        node.order_deps
        |> Enum.map(& &1.target)
        |> Enum.filter(&(Map.has_key?(modules, &1) and &1 != m))
        |> Enum.uniq()
        |> Enum.sort()

      {m, deps}
    end
  end

  @doc "Roots plus transitive dependencies over `dep_map`, sorted. Missing keys contribute nothing."
  @spec closure(%{k => [k]}, [k]) :: [k] when k: term()
  def closure(dep_map, roots) do
    do_closure(dep_map, roots, MapSet.new()) |> MapSet.to_list() |> Enum.sort()
  end

  defp do_closure(_map, [], seen), do: seen

  defp do_closure(map, [root | rest], seen) do
    if MapSet.member?(seen, root) do
      do_closure(map, rest, seen)
    else
      do_closure(map, Map.get(map, root, []) ++ rest, MapSet.put(seen, root))
    end
  end

  @doc """
  Generic deterministic Kahn sort of `keys` using `dep_map` edges restricted
  to `keys`. SCC-tolerant like `order/1`: cycle members are emitted as an
  alphabetical group, so the result is always a complete ordering.
  """
  @spec toposort(%{k => [k]}, [k]) :: [k] when k: term()
  def toposort(dep_map, keys) do
    keyset = MapSet.new(keys)

    edges =
      Map.new(keys, fn k ->
        {k, dep_map |> Map.get(k, []) |> Enum.filter(&(MapSet.member?(keyset, &1) and &1 != k))}
      end)

    {ordered, _sccs} = kahn(edges)
    ordered
  end

  @doc "Per-module closure deps (in-universe filtered, sorted). Baking input for Preload."
  @spec closure_deps_map(t()) :: %{String.t() => [String.t()]}
  def closure_deps_map(%__MODULE__{nodes: nodes}) do
    for {_path, %{module: m} = node} <- nodes, is_binary(m), into: %{} do
      {m, node.closure_deps}
    end
  end

  @doc """
  Module names of every scanned node marked `@prelude`. A driver hands this set
  to `Parser.parse/2` as `:prelude_providers` so a user `@prelude` module's
  operators reach every sibling in the same compile run, even siblings that do
  not `use` it.
  """
  @spec prelude_provider_names(t()) :: [String.t()]
  def prelude_provider_names(%__MODULE__{nodes: nodes}) do
    for {_path, node} <- nodes,
        Map.get(node, :prelude_provider?, false),
        is_binary(node.module),
        do: node.module
  end

  # -- scanning ---------------------------------------------------------------

  defp duplicate_module(nodes) do
    nodes
    |> Enum.reduce_while(%{}, fn {path, %{module: m}}, acc ->
      cond do
        not is_binary(m) -> {:cont, acc}
        Map.has_key?(acc, m) -> {:halt, {m, [Map.fetch!(acc, m), path]}}
        true -> {:cont, Map.put(acc, m, path)}
      end
    end)
    |> case do
      {name, dup_paths} -> {name, dup_paths}
      _map -> nil
    end
  end

  defp scan_file(path) do
    base = %{
      path: path,
      module: nil,
      line: nil,
      blank?: false,
      parse_error: nil,
      order_deps: [],
      closure_deps: []
    }

    case File.read(path) do
      {:error, posix} ->
        %{base | parse_error: {:file_error, posix}}

      {:ok, source} ->
        if String.trim(source) == "" do
          %{base | blank?: true}
        else
          case Cure.Compiler.parse_source(source, file: path) do
            {:error, reason} ->
              # A recoverable parse error (e.g. a body using an operator not
              # bindable by a standalone table-naive parse) must not drop the
              # file: recover module / `use` edges / `@prelude` from the
              # tolerant harvest so its dependency edges and prelude flag
              # survive. `parse_error` stays set, so `finalize_node/4`
              # early-returns and `closure_deps` remains `[]` (a known,
              # accepted gap — `order/1` reads `order_deps`, not
              # `closure_deps`). A genuinely unrecoverable file yields
              # `scan.module == nil` and still drops, as before.
              scan =
                Cure.Compiler.Parser.FixityScan.harvest_source(
                  source,
                  path,
                  Cure.Compiler.Parser.BuiltinFixity.table()
                )

              %{
                base
                | parse_error: reason,
                  module: scan.module,
                  line: base.line,
                  order_deps: Enum.map(scan.uses, fn u -> %{target: u.target, line: u.line} end)
              }
              |> Map.put(:prelude_provider?, scan.prelude?)

            {:ok, ast} ->
              {module, line} = find_module(ast)
              uses = collect_uses(ast)
              qualified = collect_qualified_targets(ast)

              base
              |> Map.put(:prelude_provider?, prelude_decorated?(ast))
              |> Map.merge(%{
                module: module,
                line: line,
                order_deps: uses,
                closure_deps: Enum.map(uses, & &1.target) ++ qualified
              })
          end
        end
    end
  end

  defp finalize_node(%{blank?: true} = node, _modules, _universe, _prelude), do: node
  defp finalize_node(%{parse_error: e} = node, _modules, _universe, _prelude) when e != nil, do: node

  defp finalize_node(node, _modules, universe, prelude_modules) do
    closure =
      node.closure_deps
      |> Enum.filter(&MapSet.member?(universe, &1))
      |> Kernel.++(Enum.filter(prelude_modules, &MapSet.member?(universe, &1)))
      |> Enum.reject(&(&1 == node.module))
      |> Enum.uniq()
      |> Enum.sort()

    order_deps =
      node.order_deps
      |> Enum.reject(&(&1.target == node.module))
      |> Enum.uniq_by(& &1.target)

    %{node | closure_deps: closure, order_deps: order_deps}
  end

  defp prelude_decorated?(ast) do
    walk(ast, false, fn
      {:property, meta, _children}, false when is_list(meta) ->
        Keyword.get(meta, :name) == "prelude"

      {_tag, meta, _children}, false when is_list(meta) ->
        match?({:prelude, _}, Keyword.get(meta, :decorator))

      _node, found ->
        found
    end)
  end

  defp find_module({:container, meta, _body}) when is_list(meta) do
    if Keyword.get(meta, :container_type) in @module_container_types do
      {Keyword.get(meta, :name), Keyword.get(meta, :line)}
    else
      {nil, nil}
    end
  end

  defp find_module({:lift_module, meta, _body}) when is_list(meta) do
    {Keyword.get(meta, :module), Keyword.get(meta, :line)}
  end

  defp find_module(list) when is_list(list) do
    Enum.find_value(list, {nil, nil}, fn item ->
      case find_module(item) do
        {nil, nil} -> nil
        found -> found
      end
    end)
  end

  # A multi-statement source parses to a top-level `{:block, _, items}` wrapping
  # the module container (+ any trailing sibling). Descend into its items, just
  # as we descend into a raw list — otherwise the module name is lost and the
  # whole module drops out of the baked closure/order maps.
  defp find_module({:block, _meta, items}) when is_list(items), do: find_module(items)

  defp find_module(_other), do: {nil, nil}

  defp collect_uses(ast), do: walk(ast, [], &use_collector/2) |> Enum.reverse()

  defp use_collector({:import, meta, _}, acc) when is_list(meta) do
    case Keyword.get(meta, :source) do
      source when is_binary(source) ->
        [%{target: source, line: Keyword.get(meta, :line, 1)} | acc]

      _ ->
        acc
    end
  end

  defp use_collector(_node, acc), do: acc

  defp collect_qualified_targets(ast) do
    walk(ast, [], fn
      {:function_call, meta, _args}, acc when is_list(meta) ->
        name = Keyword.get(meta, :name, "")

        case String.split(name, ".") do
          parts when length(parts) > 1 -> [Enum.join(Enum.drop(parts, -1), ".") | acc]
          _ -> acc
        end

      _node, acc ->
        acc
    end)
    |> Enum.uniq()
  end

  defp walk({_tag, _meta, children} = node, acc, fun) do
    acc = fun.(node, acc)
    walk(children, acc, fun)
  end

  defp walk(list, acc, fun) when is_list(list),
    do: Enum.reduce(list, acc, &walk(&1, &2, fun))

  defp walk(_other, acc, _fun), do: acc

  # -- ordering ---------------------------------------------------------------

  # Deliberately simple, not optimal: pops ONE ready node per round and
  # rebuilds the whole map each time (O(V) per removal, O(V^2) overall)
  # rather than batching the ready set or maintaining reverse-adjacency
  # for O(V+E). Compile sets here are tens to low hundreds of files
  # (stdlib ~39) -- this is not a hot path, and the
  # simplicity keeps the alphabetical tie-break obviously correct.
  #
  # Returns {ordered_paths, stuck_groups}: when no node is ready (cycle
  # deadlock), the source SCC of the remaining subgraph is emitted as a
  # group (alphabetical within it) and its internal edge map is collected
  # so order/1 can report the closed cycle walk. Never errors.
  defp kahn(edges), do: do_kahn(edges, [], [])

  defp do_kahn(edges, acc, sccs) when map_size(edges) == 0,
    do: {Enum.reverse(acc), Enum.reverse(sccs)}

  defp do_kahn(edges, acc, sccs) do
    ready =
      edges
      |> Enum.filter(fn {_path, deps} -> deps == [] end)
      |> Enum.map(&elem(&1, 0))
      |> Enum.sort()

    case ready do
      [] ->
        # Cycle deadlock: emit the source SCC of the condensation as a
        # group. A source SCC at a deadlock is always multi-member (a
        # ready singleton would have been picked above).
        {members, scc_edges} = source_scc(edges)

        edges =
          edges
          |> Map.drop(members)
          |> Map.new(fn {p, deps} -> {p, deps -- members} end)

        do_kahn(edges, Enum.reverse(members) ++ acc, [scc_edges | sccs])

      [next | _] ->
        edges =
          edges
          |> Map.delete(next)
          |> Map.new(fn {p, deps} -> {p, List.delete(deps, next)} end)

        do_kahn(edges, [next | acc], sccs)
    end
  end

  # The SCC of the remaining subgraph with no dependencies on OTHER
  # remaining SCCs; among several sources, the one containing the
  # alphabetically-smallest path. Returns {sorted_members, scc_edge_map}.
  defp source_scc(edges) do
    sccs = tarjan(edges)
    scc_of = for {members, i} <- Enum.with_index(sccs), m <- members, into: %{}, do: {m, i}

    members =
      sccs
      |> Enum.filter(fn scc_members ->
        Enum.all?(scc_members, fn m ->
          Enum.all?(edges[m], fn d -> scc_of[d] == scc_of[m] end)
        end)
      end)
      |> Enum.min_by(fn scc_members -> Enum.min(scc_members) end)
      |> Enum.sort()

    member_set = MapSet.new(members)

    scc_edges =
      Map.new(members, fn m ->
        {m, Enum.filter(edges[m], &MapSet.member?(member_set, &1))}
      end)

    {members, scc_edges}
  end

  # Standard Tarjan SCC over the (small) stuck subgraph; returns [[path]].
  # Determinism: neighbors and roots visited in sorted order.
  defp tarjan(edges) do
    nodes = edges |> Map.keys() |> Enum.sort()

    {_state, sccs} =
      Enum.reduce(nodes, {%{index: %{}, low: %{}, stack: [], on: MapSet.new(), n: 0}, []}, fn v, {st, acc} ->
        if Map.has_key?(st.index, v), do: {st, acc}, else: strongconnect(v, edges, st, acc)
      end)

    Enum.reverse(sccs)
  end

  defp strongconnect(v, edges, st, sccs) do
    st = %{
      st
      | index: Map.put(st.index, v, st.n),
        low: Map.put(st.low, v, st.n),
        stack: [v | st.stack],
        on: MapSet.put(st.on, v),
        n: st.n + 1
    }

    {st, sccs} =
      Enum.reduce(Enum.sort(edges[v] || []), {st, sccs}, fn w, {st, sccs} ->
        cond do
          not Map.has_key?(st.index, w) ->
            {st, sccs} = strongconnect(w, edges, st, sccs)
            {%{st | low: Map.update!(st.low, v, &min(&1, st.low[w]))}, sccs}

          MapSet.member?(st.on, w) ->
            {%{st | low: Map.update!(st.low, v, &min(&1, st.index[w]))}, sccs}

          true ->
            {st, sccs}
        end
      end)

    if st.low[v] == st.index[v] do
      {members, rest} = Enum.split_while(st.stack, &(&1 != v))
      members = members ++ [v]
      rest = tl(rest)

      st = %{st | stack: rest, on: Enum.reduce(members, st.on, &MapSet.delete(&2, &1))}
      {st, [Enum.sort(members) | sccs]}
    else
      {st, sccs}
    end
  end

  defp cycle_info(scc_edges, nodes, modules) do
    path_to_module = for {m, p} <- modules, into: %{}, do: {p, m}
    start = scc_edges |> Map.keys() |> Enum.sort() |> hd()
    hops = trace_cycle(start, scc_edges, [])

    Enum.map(hops, fn path ->
      node = nodes[path]
      module = path_to_module[path] || "?"

      line =
        case Enum.find(node.order_deps, fn d -> modules[d.target] in hops end) do
          %{line: l} -> l
          _ -> node.line || 1
        end

      %{module: module, path: path, line: line}
    end)
  end

  # Do NOT `Enum.uniq/1` the final result: the whole point is to return a
  # CLOSED walk (first hop == last hop, e.g. `[A, B, A]`), matching the
  # spec's `A -> B -> A` format and the Task 3 formatter fixture. `uniq`
  # would strip that closing repeat and silently turn a cycle report into
  # an open chain that no longer shows it loops.
  defp trace_cycle(path, edges, seen) do
    if path in seen do
      Enum.reverse([path | Enum.take_while(seen, &(&1 != path))] ++ [path])
    else
      case edges[path] do
        [next | _] -> trace_cycle(next, edges, [path | seen])
        _ -> Enum.reverse([path | seen])
      end
    end
  end
end
