defmodule Cure.MetaAST.Conformance do
  @moduledoc """
  Structural MetaAST-conformance check for Cure's *surface* AST.

  Metastatic's generic traversal (`Metastatic.AST.traverse/4`) descends into a
  node only when it is the canonical `{type, meta, children}` shape — an atom
  `type`, a keyword-list `meta`, and the children in the third slot — and it
  recurses ONLY the children slot. Every other tuple it meets is passed through
  as an opaque leaf, and the meta slot is never walked. So a subterm is invisible
  to every MetaAST consumer (RAG, MCP, the migrator) in two distinct ways, which
  this module reports as two violation *kinds*:

    * `:bad_shape` — an atom-headed tuple that is NOT a canonical 3-tuple and yet
      hides a node. Metastatic treats it as an opaque leaf, so the subterms it
      carries are dropped. The six known shapes are `:named_implicit_pat`
      (4-tuple), `:named_dom` (`{tag, name, inner}`), `:arrow_chain` (2-tuple),
      `:gadt_ctor` (canonical, but its children slot holds a bare arrow_chain),
      `:group` (2-tuple), and `:builtin` (2-tuple).

    * `:node_in_meta` — a *canonical* node that stores a subterm inside a meta
      value (e.g. `param`'s type under `:type`, `function_def`'s `:params` /
      `:return_type`, `match_arm`'s `:pattern`). The node itself is shape-valid,
      so Metastatic descends its children and never sees the subterm parked in
      meta. This is the larger gap (~2,600 occurrences across the stdlib).

  The target invariant (see the 2026-07-15 blind-spot design, Option C / C2) is:
  **no canonical node may appear inside a meta value.** Meta holds only
  non-structural scalars (names, line/col, scope, visibility, arity, QTT grades);
  every subterm lives in children. `conformant?/1` is true exactly when both
  gates are clean. Some Cure nodes already satisfy this — `pattern_match` is
  `{:pattern_match, [line:, col:], [scrutinee, arms…]}` — so the check is not
  novel, it is a convention the rest of the surface must be brought in line with.

  This module is the total-descent DUAL of Metastatic's traversal: it walks every
  position, including the meta values that traversal skips and the irregular
  shapes it cannot enter, and reports each place a subterm would be lost.

  Deliberately NOT built on `Metastatic.AST.conforms?/1`: that predicate gates on
  a fixed `@all_types` registry which omits ~100 of Cure's node atoms (every
  dependent / macro / concurrency former), so it rejects almost the whole Cure
  surface. Conformance here is about SHAPE and PLACEMENT, not type-registry
  membership.
  """

  # Wide tuples carried as trivia, NOT normalization targets. Comments are leaves
  # under Metastatic's traversal anyway — their payload is never a node — so their
  # non-3-tuple shape hides no subterms and needs no rewrite.
  @trivia_tags [:comment, :doc_comment]

  @type kind :: :bad_shape | :node_in_meta

  @type violation :: %{
          kind: kind(),
          path: [atom()],
          tag: atom(),
          key: atom() | nil,
          arity: non_neg_integer() | nil,
          node: term()
        }

  @doc """
  True iff `ast` satisfies both conformance gates: no `:bad_shape` tuple and no
  `:node_in_meta` subterm. Note this is the strict end-state invariant — real
  Cure surface currently fails it (that is what the corpus tripwire tracks).
  """
  @spec conformant?(term()) :: boolean()
  def conformant?(ast), do: violations(ast) == []

  @doc """
  Every conformance violation in `ast`, in pre-order (outermost first). Each is a
  map with `:kind` (`:bad_shape` | `:node_in_meta`), the `:path` of node tags
  enclosing it (outermost first), the offending `:tag`, and for `:node_in_meta`
  the meta `:key` that hides the subterm.
  """
  @spec violations(term()) :: [violation()]
  def violations(ast), do: ast |> walk([], []) |> Enum.reverse()

  @doc """
  The distinct `{kind, tag, key}` buckets present in `ast` (key is `nil` for
  `:bad_shape`). This is the granularity the corpus tripwire allowlists against —
  robust to stdlib churn (adding another function grows the `param :type` count
  but not the bucket set).
  """
  @spec violation_buckets(term()) :: MapSet.t({kind(), atom(), atom() | nil})
  def violation_buckets(ast) do
    ast
    |> violations()
    |> Enum.map(fn %{kind: kind, tag: tag, key: key} -> {kind, tag, key} end)
    |> MapSet.new()
  end

  @doc """
  A short human-readable line per violation, suitable for a warning or a test
  failure message.
  """
  @spec describe([violation()]) :: String.t()
  def describe([]), do: "no MetaAST-conformance violations"

  def describe(violations) do
    Enum.map_join(violations, "\n", fn
      %{kind: :bad_shape, tag: tag, arity: arity, path: path} ->
        "  * [bad_shape] #{inspect(tag)} (arity #{arity}) at #{path_string(path)}"

      %{kind: :node_in_meta, tag: tag, key: key, path: path} ->
        "  * [node_in_meta] #{inspect(tag)} hides a node in meta :#{key} at #{path_string(path)}"
    end)
  end

  defp path_string(path), do: Enum.map_join(path, ".", &Atom.to_string/1)

  # An atom-headed tuple — the shape of a node. Three outcomes:
  #
  #   * canonical `{tag, keyword_meta, children}` → shape-conformant; check each
  #     meta value for a hidden node (`:node_in_meta`), descend the meta values
  #     (they may nest further nodes), and descend the children slot. The meta
  #     KEYS are never walked.
  #   * non-canonical but HIDES a node → a `:bad_shape` defect; flag and descend.
  #   * non-canonical and hides no node (an MFA `{:erlang, :length, 1}`, a `@group`
  #     argument, a module reference) → opaque leaf data. Metastatic treats it as a
  #     leaf and loses nothing, so it is conformant; do not flag.
  defp walk(node, path, acc)
       when is_tuple(node) and tuple_size(node) >= 1 and is_atom(:erlang.element(1, node)) do
    tag = elem(node, 0)

    cond do
      tag in @trivia_tags ->
        acc

      canonical_node?(node) ->
        acc = walk_meta(elem(node, 1), tag, [tag | path], acc)
        walk(elem(node, 2), [tag | path], acc)

      Enum.any?(non_meta_elements(node), &hides_node?/1) ->
        flag_and_descend(node, tag, path, acc)

      true ->
        acc
    end
  end

  # A tuple that is not node-shaped (e.g. a `{key_node, value_node}` pair): descend
  # into every element.
  defp walk(node, path, acc) when is_tuple(node) do
    node |> Tuple.to_list() |> Enum.reduce(acc, fn el, acc -> walk(el, path, acc) end)
  end

  # A list of children (or any list): walk each element.
  defp walk(list, path, acc) when is_list(list) do
    Enum.reduce(list, acc, fn el, acc -> walk(el, path, acc) end)
  end

  # Primitive leaf (integer, atom, string, nil, …): nothing to descend.
  defp walk(_other, _path, acc), do: acc

  # The meta of a canonical node. For each `{key, value}`: if the value hides a
  # canonical node, that subterm is invisible to Metastatic's children-only
  # traversal — record a `:node_in_meta` violation keyed by `key`. Either way,
  # descend the value (never the key) to catch violations nested deeper. `path`
  # already includes the parent tag.
  defp walk_meta(meta, parent_tag, path, acc) do
    Enum.reduce(meta, acc, fn {key, value}, acc ->
      acc =
        if hides_node?(value) do
          violation = %{
            kind: :node_in_meta,
            path: Enum.reverse(path),
            tag: parent_tag,
            key: key,
            arity: nil,
            node: value
          }

          [violation | acc]
        else
          acc
        end

      walk(value, path, acc)
    end)
  end

  defp flag_and_descend(node, tag, path, acc) do
    violation = %{
      kind: :bad_shape,
      path: Enum.reverse([tag | path]),
      tag: tag,
      key: nil,
      arity: tuple_size(node),
      node: node
    }

    acc = [violation | acc]

    # Descend into every element after the tag. A keyword-list element is treated as
    # a meta slot: walk its VALUES (which may hold nodes) but not its keys, matching
    # how a canonical node's meta is handled. A bad-shape node is itself a
    # normalization target, so we do not additionally emit `:node_in_meta` for its
    # meta-like slots — we only surface violations nested inside.
    node
    |> Tuple.to_list()
    |> tl()
    |> Enum.reduce(acc, fn el, acc ->
      if keyword_list?(el),
        do: walk_meta_values(el, [tag | path], acc),
        else: walk(el, [tag | path], acc)
    end)
  end

  # Descend the value side of each meta pair without emitting `:node_in_meta`
  # (used inside an already-flagged bad-shape node). Keys are never nodes.
  defp walk_meta_values(meta, path, acc) do
    Enum.reduce(meta, acc, fn {_key, value}, acc -> walk(value, path, acc) end)
  end

  # A canonical MetaAST node: 3-tuple, atom tag, keyword-list meta. This is exactly
  # the shape Metastatic's `do_traverse/4` descends into.
  defp canonical_node?(node) do
    is_tuple(node) and tuple_size(node) == 3 and is_atom(elem(node, 0)) and
      is_list(elem(node, 1)) and Keyword.keyword?(elem(node, 1))
  end

  # Does `term` contain a canonical node anywhere traversal would need to reach?
  # This is what separates a malformed NODE (hides real structure — the defect we
  # flag) from opaque leaf DATA that merely happens to be an atom-headed tuple (an
  # MFA, a decorator argument): the latter holds only primitives and hides nothing.
  defp hides_node?(term) when is_tuple(term) do
    cond do
      canonical_node?(term) -> true
      tuple_size(term) >= 1 and is_atom(elem(term, 0)) -> Enum.any?(non_meta_elements(term), &hides_node?/1)
      true -> term |> Tuple.to_list() |> Enum.any?(&hides_node?/1)
    end
  end

  defp hides_node?(term) when is_list(term), do: Enum.any?(term, &hides_node?/1)
  defp hides_node?(_term), do: false

  # A node's elements after the tag, with any meta (keyword-list) slot removed.
  defp non_meta_elements(node) do
    node |> Tuple.to_list() |> tl() |> Enum.reject(&keyword_list?/1)
  end

  # A non-empty keyword list — the shape of a meta slot. `[]` is excluded so an
  # empty children list is still walked (it has nothing to walk, but the intent is
  # to skip META, not empty children).
  defp keyword_list?(term), do: is_list(term) and term != [] and Keyword.keyword?(term)
end
