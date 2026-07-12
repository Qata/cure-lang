defmodule Cure.Compiler.MacroSyntax do
  @moduledoc """
  Reflection bridge between the parser AST and the generic `Std.Syntax` value a
  Tier-3 `computed by` elab operates on (macro-facility design §3). TCB delta
  zero — pure frontend reflection; the elab's output is re-elaborated + kernel
  checked (K3 firewall). This slice handles the Elixir mirror repr; slice 3
  maps it to Core values of `Std.Syntax` and runs the elab.
  """

  @type synlit ::
          {:s_int, integer}
          | {:s_float, float}
          | {:s_str, String.t()}
          | {:s_bool, boolean}
          | {:s_atom, atom}
          | {:s_list, [synlit]}
          | {:s_syntax, repr}
          | {:s_map, [{synlit, synlit}]}
          | :s_opaque
  @type repr ::
          {:syn_node, atom, [{atom, synlit}], [repr]}
          | {:syn_leaf, atom, [{atom, synlit}], synlit}
          | {:syn_raw, synlit}

  # -- to_syntax: parser AST -> repr -----------------------------------------

  # `to_syntax/1` is called recursively over every element found in a node's
  # children list (via `Enum.map(third, &to_syntax/1)`), but not every such
  # element is a well-formed `{tag, meta, third}` triple: an `impossible`
  # match-arm body is the bare atom `nil` (see parse_match_arm_tail/2), and a
  # named-implicit dot pattern (`{name = <expr>}`) is a 4-tuple
  # `{:named_implicit_pat, meta, name, inner}` (see parse_named_implicit_pat/2)
  # -- neither matches either clause below. Rather than crash on real,
  # reachable parser output, fall back to a raw leaf: scalars (like `nil`)
  # round-trip exactly via `synlit`, and non-conforming tuples (like the
  # named-implicit 4-tuple) reflect opaquely, same as an irreducible native
  # term (e.g. a compiled regex) -- honest, not a crash.
  @spec to_syntax(term()) :: repr
  def to_syntax({tag, meta, third}) when is_list(third) do
    {:syn_node, tag, attrs(meta), Enum.map(third, &to_syntax/1)}
  end

  def to_syntax({tag, meta, scalar}) when is_atom(tag) and is_list(meta) do
    {:syn_leaf, tag, attrs(meta), synlit(scalar)}
  end

  def to_syntax(other), do: {:syn_raw, synlit(other)}

  # A node whose semantic meta carries values; drop line/col, keep the rest as
  # {key, synlit}. Unrepresentable meta values become :s_opaque.
  defp attrs(meta) when is_list(meta) do
    for {k, v} <- meta, k not in [:line, :col], do: {k, synlit(v)}
  end

  defp attrs(_), do: []

  defp synlit(v) when is_integer(v), do: {:s_int, v}
  defp synlit(v) when is_float(v), do: {:s_float, v}
  defp synlit(v) when is_binary(v), do: {:s_str, v}
  defp synlit(v) when is_boolean(v), do: {:s_bool, v}
  defp synlit(v) when is_atom(v), do: {:s_atom, v}
  defp synlit(v) when is_list(v), do: {:s_list, Enum.map(v, &synlit/1)}

  # A meta value that is a plain Elixir map (e.g. an `interface`'s
  # `defaults:` table, name -> default-method-body AST -- see
  # parse_interface/1). Representable losslessly as a list of key/value
  # synlit pairs; order is not semantically meaningful for a lookup table.
  defp synlit(v) when is_map(v),
    do: {:s_map, Enum.map(v, fn {k, val} -> {synlit(k), synlit(val)} end)}

  # A meta value that is itself a full AST node (e.g. a binary-segment
  # `size(expr)`/`unit(n)` specifier — see parse_bin_segment/1) rather than a
  # plain scalar. Representable losslessly by recursing through to_syntax, so
  # it does not need to fall back to :s_opaque like a genuinely irreducible
  # native term (e.g. a compiled regex).
  defp synlit({tag, meta, _} = v) when is_atom(tag) and is_list(meta), do: {:s_syntax, to_syntax(v)}

  defp synlit(_), do: :s_opaque

  # -- from_syntax: repr -> parser AST ---------------------------------------

  @spec from_syntax(repr) :: tuple()
  def from_syntax({:syn_node, tag, attrs, kids}) do
    {tag, from_attrs(attrs), Enum.map(kids, &from_syntax/1)}
  end

  def from_syntax({:syn_leaf, tag, attrs, lit}) do
    {tag, from_attrs(attrs), from_synlit(lit)}
  end

  def from_syntax({:syn_raw, lit}), do: from_synlit(lit)

  defp from_attrs(attrs), do: for({k, lit} <- attrs, do: {k, from_synlit(lit)})

  defp from_synlit({:s_int, n}), do: n
  defp from_synlit({:s_float, f}), do: f
  defp from_synlit({:s_str, s}), do: s
  defp from_synlit({:s_bool, b}), do: b
  defp from_synlit({:s_atom, a}), do: a
  defp from_synlit({:s_list, items}), do: Enum.map(items, &from_synlit/1)
  defp from_synlit({:s_syntax, r}), do: from_syntax(r)

  defp from_synlit({:s_map, pairs}),
    do: Map.new(pairs, fn {k, v} -> {from_synlit(k), from_synlit(v)} end)

  defp from_synlit(:s_opaque), do: nil
end
