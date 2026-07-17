defmodule Cure.Compiler.MacroSyntax do
  @moduledoc """
  Reflection bridge between the parser AST and the generic `Std.Syntax` value a
  Tier-3 `computed by` elab operates on (macro-facility design §3). TCB delta
  zero — pure frontend reflection; the elab's output is re-elaborated + kernel
  checked (K3 firewall). This slice handles the Elixir mirror repr; slice 3
  maps it to Core values of `Std.Syntax` and runs the elab.
  """

  @doc """
  Lower internal standard-library macro markers into ordinary parser AST.

  The marker keeps a macro template from recursively matching its own public
  keyword. It disappears here; downstream elaboration sees an ordinary call.
  """
  @spec lower_internal(term()) :: {:ok, tuple()} | :not_internal | {:error, term()}
  def lower_internal({:function_call, meta, []}) when is_list(meta) do
    case Keyword.get(meta, :name) do
      "__optic_lens_first" -> {:ok, {:function_call, Keyword.put(meta, :name, "first_lens"), []}}
      "__optic_lens_second" -> {:ok, {:function_call, Keyword.put(meta, :name, "second_lens"), []}}
      _ -> :not_internal
    end
  end

  def lower_internal(_ast), do: :not_internal

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
          | {:syn_quoted, repr}
          | {:syn_failure, atom, [repr]}

  # -- to_syntax: parser AST -> repr -----------------------------------------

  # `to_syntax/1` is called recursively over every element found in a node's
  # children list (via `Enum.map(third, &to_syntax/1)`), but not every such
  # element is a well-formed `{tag, meta, third}` triple: an `impossible`
  # match-arm body is the bare atom `nil` (see parse_match_arm_tail/2) -- which
  # matches neither clause below. Rather than crash on real, reachable parser
  # output, fall back to a raw leaf: scalars (like `nil`) round-trip exactly via
  # `synlit`, and any non-conforming tuple reflects opaquely, same as an
  # irreducible native term (e.g. a compiled regex) -- honest, not a crash.
  @spec to_syntax(term()) :: repr
  def to_syntax({:quoted_syntax, _meta, [inner]}), do: {:syn_quoted, to_syntax(inner)}

  def to_syntax({tag, meta, third}) when is_list(third) do
    {:syn_node, tag, attrs(meta), Enum.map(third, &to_syntax/1)}
  end

  def to_syntax({tag, meta, scalar}) when is_atom(tag) and is_list(meta) do
    {:syn_leaf, tag, attrs(meta), synlit(scalar)}
  end

  def to_syntax(other), do: {:syn_raw, synlit(other)}

  # -- expansion context -----------------------------------------------------

  @context_field "context"

  @doc """
  The field a computed rule's derived record carries in addition to its holes.

  A Tier-3 elab is otherwise blind to where it was invoked, so a rule with no
  holes (`beam_ops self`) would see nothing at all. The trailing field carries
  the reflected expansion context; a rule that declares a hole of the same name
  keeps its hole (and `MacroValidate` reports the collision).
  """
  @spec record_fields([String.t()]) :: [String.t()]
  def record_fields(syntax_fields), do: Enum.uniq(syntax_fields ++ [@context_field])

  @doc "The reserved derived-record field name."
  @spec context_field() :: String.t()
  def context_field, do: @context_field

  @doc """
  Reflect a macro's expansion context — the callback a use-site sits inside —
  as an ordinary `Std.Syntax` value. `nil` (an ordinary, non-callback use-site)
  reflects as `Raw(SOpaque)`, the same way any absent value does, so the elab's
  field is total.
  """
  @spec context_syntax(map() | nil) :: repr()
  def context_syntax(nil), do: {:syn_raw, :s_opaque}

  def context_syntax(context) when is_map(context) do
    attrs = for {key, value} <- Enum.sort(context), is_atom(key), do: {key, synlit(value)}
    {:syn_node, :callback_context, attrs, []}
  end

  @doc "Attach a reflected expansion context to a macro input's attributes."
  @spec with_context(repr(), map() | nil) :: repr()
  def with_context(repr, nil), do: repr

  def with_context({:syn_node, tag, attrs, kids}, context) when is_map(context),
    do: {:syn_node, tag, attrs ++ [{:expansion_context, {:s_syntax, context_syntax(context)}}], kids}

  def with_context(repr, _context), do: repr

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

  def from_syntax({:syn_quoted, repr}), do: {:quoted_syntax, [], [from_syntax(repr)]}

  def from_syntax({:syn_failure, name, args}),
    do: {:macro_failure, name, Enum.map(args, &from_syntax/1)}

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

  # -- mirror repr <-> Core Std.Syntax values -------------------------------

  @doc "Encode the Elixir mirror representation as a closed Core value."
  @spec to_core(repr()) :: Cure.Core.Term.t()
  def to_core({:syn_node, tag, attrs, kids}),
    do: ctor(:Node, [atom(tag), to_core_attrs(attrs), to_core_list(Enum.map(kids, &to_core/1))])

  def to_core({:syn_leaf, tag, attrs, lit}),
    do: ctor(:Leaf, [atom(tag), to_core_attrs(attrs), to_core_synlit(lit)])

  def to_core({:syn_raw, lit}), do: ctor(:Raw, [to_core_synlit(lit)])

  def to_core({:syn_quoted, syntax}), do: ctor(:Quoted, [to_core(syntax)])

  def to_core({:syn_failure, name, args}),
    do: ctor(:Failure, [atom(name), to_core_list(Enum.map(args, &to_core/1))])

  @doc """
  Encode the ordered children of a macro input as a derived syntax record.

  The record's fields are the rule's holes followed by the reserved `context`
  field (`record_fields/1`), so the encoded constructor carries one argument per
  hole plus the reflected expansion context. A rule that declares its own
  `context` hole owns the name, and no extra argument is appended.
  """
  @spec to_core_record(String.t() | atom(), [String.t()], repr()) :: Cure.Core.Term.t()
  def to_core_record(type_name, syntax_fields, repr),
    do: to_core_record(type_name, syntax_fields, [], repr)

  @spec to_core_record(String.t() | atom(), [String.t()], [String.t()], repr()) :: Cure.Core.Term.t()
  def to_core_record(type_name, syntax_fields, repeated_fields, {:syn_node, _tag, attrs, kids}) do
    name = if is_binary(type_name), do: String.to_atom(type_name), else: type_name

    args =
      syntax_fields
      |> Enum.zip(kids)
      |> Enum.map(fn {field, kid} ->
        if field in repeated_fields, do: to_core_syntax_list(kid), else: to_core(kid)
      end)

    args =
      if @context_field in syntax_fields,
        do: args,
        else: args ++ [to_core(context_attr(attrs))]

    {:ctor, name, args}
  end

  # The parser keeps one child slot per grammar field, so a repeated field is
  # represented as an outer one-element list containing the captured values.
  # Unwrap that field slot before constructing the reflected Cure list.
  defp to_core_syntax_list({:syn_raw, {:s_list, [{:s_list, items}]}}) do
    to_core_list(Enum.map(items, &to_core_syntax_item/1))
  end

  defp to_core_syntax_list({:syn_raw, {:s_list, items}}) do
    to_core_list(Enum.map(items, &to_core_syntax_item/1))
  end

  defp to_core_syntax_list(repr), do: to_core_list([to_core(repr)])

  defp to_core_syntax_item({:s_syntax, repr}), do: to_core(repr)
  defp to_core_syntax_item(lit), do: to_core({:syn_raw, lit})

  defp context_attr(attrs) do
    case List.keyfind(attrs, :expansion_context, 0) do
      {:expansion_context, {:s_syntax, repr}} -> repr
      _ -> {:syn_raw, :s_opaque}
    end
  end

  @doc "Decode a normalized Core value of Std.Syntax into the mirror representation."
  @spec from_core(Cure.Core.Term.t()) :: repr() | {:error, term()}
  def from_core({:ctor, :Node, [{:atom_lit, tag}, attrs, kids]}) do
    with {:ok, attrs} <- from_core_attrs(attrs),
         {:ok, kids} <- from_core_list(kids),
         {:ok, kids} <- map_results(kids, &from_core/1),
         true <- Enum.all?(kids, &syntax_repr?/1) do
      {:syn_node, tag, attrs, kids}
    else
      _ -> {:error, {:invalid_syntax_node, attrs, kids}}
    end
  end

  def from_core({:ctor, :Leaf, [{:atom_lit, tag}, attrs, lit]}) do
    with {:ok, attrs} <- from_core_attrs(attrs),
         {:ok, lit} <- from_core_synlit(lit) do
      {:syn_leaf, tag, attrs, lit}
    else
      _ -> {:error, {:invalid_syntax_leaf, tag}}
    end
  end

  def from_core({:ctor, :Raw, [lit]}) do
    case from_core_synlit(lit) do
      {:ok, lit} -> {:syn_raw, lit}
      error -> error
    end
  end

  def from_core({:ctor, :Quoted, [syntax]}) do
    case from_core(syntax) do
      {:error, _} = error -> error
      syntax -> {:syn_quoted, syntax}
    end
  end

  def from_core({:ctor, :Failure, [{:atom_lit, name}, args]}) do
    with {:ok, args} <- from_core_list(args),
         {:ok, args} <- map_results(args, &from_core/1),
         true <- Enum.all?(args, &syntax_repr?/1) do
      {:syn_failure, name, args}
    else
      _ -> {:error, {:invalid_syntax_failure, name}}
    end
  end

  def from_core(other), do: {:error, {:unsupported_syntax_core, other}}

  defp ctor(name, args), do: {:ctor, name, args}
  defp atom(value), do: {:atom_lit, value}

  defp to_core_attrs(attrs),
    do: to_core_list(Enum.map(attrs, fn {key, lit} -> ctor(:KV, [atom(key), to_core_synlit(lit)]) end))

  defp to_core_list(items), do: Enum.reduce(Enum.reverse(items), ctor(:Nil, []), &ctor(:Cons, [&1, &2]))

  defp to_core_synlit({:s_int, n}), do: ctor(:SInt, [{:int_lit, n}])
  defp to_core_synlit({:s_float, f}), do: ctor(:SFloat, [{:float_lit, f}])

  defp to_core_synlit({:s_str, s}),
    do: ctor(:SStr, [to_core_list(Enum.map(String.to_charlist(s), &{:bounded_lit, &1}))])

  defp to_core_synlit({:s_bool, true}), do: ctor(:SBool, [ctor(:True, [])])
  defp to_core_synlit({:s_bool, false}), do: ctor(:SBool, [ctor(:False, [])])
  defp to_core_synlit({:s_atom, a}), do: ctor(:SAtom, [atom(a)])
  defp to_core_synlit({:s_list, items}), do: ctor(:SList, [to_core_list(Enum.map(items, &to_core_synlit/1))])
  defp to_core_synlit({:s_syntax, syntax}), do: ctor(:SSyntax, [to_core(syntax)])

  defp to_core_synlit({:s_map, pairs}) do
    values = Enum.map(pairs, fn {key, value} -> ctor(:SPair, [to_core_synlit(key), to_core_synlit(value)]) end)
    ctor(:SMap, [to_core_list(values)])
  end

  defp to_core_synlit(:s_opaque), do: ctor(:SOpaque, [])

  defp from_core_attrs(core) do
    with {:ok, entries} <- from_core_list(core),
         {:ok, attrs} <-
           map_results(entries, fn
             {:ctor, :KV, [{:atom_lit, key}, lit]} ->
               with {:ok, lit} <- from_core_synlit(lit), do: {key, lit}

             _ ->
               {:error, :invalid_syntax_attr}
           end) do
      {:ok, attrs}
    else
      _ -> {:error, {:invalid_syntax_attrs, core}}
    end
  end

  defp from_core_list({:ctor, :Nil, []}), do: {:ok, []}

  defp from_core_list({:ctor, :Cons, [head, tail]}) do
    with {:ok, rest} <- from_core_list(tail), do: {:ok, [head | rest]}
  end

  defp from_core_list(_), do: {:error, :invalid_syntax_list}

  defp from_core_synlit({:ctor, :SInt, [{:int_lit, n}]}), do: {:ok, {:s_int, n}}
  defp from_core_synlit({:ctor, :SFloat, [{:float_lit, f}]}), do: {:ok, {:s_float, f}}

  defp from_core_synlit({:ctor, :SStr, [chars]}) do
    with {:ok, chars} <- from_core_list(chars),
         true <- Enum.all?(chars, &match?({:bounded_lit, n} when is_integer(n), &1)) do
      {:ok, {:s_str, chars |> Enum.map(fn {:bounded_lit, n} -> n end) |> List.to_string()}}
    else
      _ -> {:error, :invalid_syntax_string}
    end
  end

  defp from_core_synlit({:ctor, :SBool, [{:ctor, :True, []}]}), do: {:ok, {:s_bool, true}}
  defp from_core_synlit({:ctor, :SBool, [{:ctor, :False, []}]}), do: {:ok, {:s_bool, false}}
  defp from_core_synlit({:ctor, :SAtom, [{:atom_lit, a}]}), do: {:ok, {:s_atom, a}}

  defp from_core_synlit({:ctor, :SList, [items]}) do
    with {:ok, items} <- from_core_list(items),
         {:ok, items} <- map_results(items, &from_core_synlit/1) do
      {:ok, {:s_list, items}}
    end
  end

  defp from_core_synlit({:ctor, :SSyntax, [syntax]}) do
    case from_core(syntax) do
      {:error, _} = error -> error
      syntax -> {:ok, {:s_syntax, syntax}}
    end
  end

  defp from_core_synlit({:ctor, :SMap, [pairs]}) do
    with {:ok, pairs} <- from_core_list(pairs),
         {:ok, pairs} <- map_results(pairs, &from_core_pair/1) do
      {:ok, {:s_map, pairs}}
    end
  end

  defp from_core_synlit({:ctor, :SOpaque, []}), do: {:ok, :s_opaque}
  defp from_core_synlit(_), do: {:error, :invalid_syntax_literal}

  defp from_core_pair({:ctor, :SPair, [key, value]}) do
    with {:ok, key} <- from_core_synlit(key), {:ok, value} <- from_core_synlit(value), do: {key, value}
  end

  defp from_core_pair(_), do: {:error, :invalid_syntax_pair}

  defp syntax_repr?({:syn_node, _, _, _}), do: true
  defp syntax_repr?({:syn_leaf, _, _, _}), do: true
  defp syntax_repr?({:syn_raw, _}), do: true
  defp syntax_repr?({:syn_quoted, _}), do: true
  defp syntax_repr?({:syn_failure, _, _}), do: true
  defp syntax_repr?(_), do: false

  defp map_results(items, fun) do
    Enum.reduce_while(items, {:ok, []}, fn item, {:ok, acc} ->
      case fun.(item) do
        {:ok, value} -> {:cont, {:ok, [value | acc]}}
        {:error, _} = error -> {:halt, error}
        value -> {:cont, {:ok, [value | acc]}}
      end
    end)
    |> case do
      {:ok, values} -> {:ok, Enum.reverse(values)}
      error -> error
    end
  end
end
