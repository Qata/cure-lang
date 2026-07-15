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
  # match-arm body is the bare atom `nil` (see parse_match_arm_tail/2), and a
  # named-implicit dot pattern (`{name = <expr>}`) is a 4-tuple
  # `{:named_implicit_pat, meta, name, inner}` (see parse_named_implicit_pat/2)
  # -- neither matches either clause below. Rather than crash on real,
  # reachable parser output, fall back to a raw leaf: scalars (like `nil`)
  # round-trip exactly via `synlit`, and non-conforming tuples (like the
  # named-implicit 4-tuple) reflect opaquely, same as an irreducible native
  # term (e.g. a compiled regex) -- honest, not a crash.
  @spec to_syntax(term()) :: repr
  def to_syntax({:quoted_syntax, _meta, [inner]}), do: {:syn_quoted, to_syntax(inner)}

  # Preserve the parser's generic identifier-shape fact for source-defined
  # syntax analysis. A reflected macro must distinguish a Pascal constructor
  # head from a lowercase variable without a domain-specific compiler rule.
  def to_syntax({:variable, meta, name}) when is_list(meta) and is_binary(name) do
    extra = [
      {:pascal_case, {:s_bool, pascal_case?(name)}},
      {:constructor_key, {:s_atom, String.to_atom(name <> "/0")}},
      {:variable_name, {:s_atom, String.to_atom(name)}}
    ]

    {:syn_leaf, :variable, attrs(meta) ++ extra, synlit(name)}
  end

  def to_syntax({:function_call, meta, args}) when is_list(meta) and is_list(args) do
    name = Keyword.get(meta, :name)

    extra =
      if is_binary(name),
        do: [
          {:pascal_case, {:s_bool, pascal_case?(name)}},
          {:constructor_key, {:s_atom, String.to_atom(name <> "/" <> Integer.to_string(length(args)))}}
        ],
        else: []

    {:syn_node, :function_call, attrs(meta) ++ extra, Enum.map(args, &to_syntax/1)}
  end

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

  defp pascal_case?(<<first::utf8, _rest::binary>>) when first in ?A..?Z, do: true
  defp pascal_case?(_), do: false

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

  defp from_attrs(attrs) do
    for {k, lit} <- attrs, k not in [:pascal_case, :constructor_key, :variable_name], do: {k, from_synlit(lit)}
  end

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
    do: to_core_record(type_name, syntax_fields, [], repr, %{}, true)

  @spec to_core_record(String.t() | atom(), [String.t()], [String.t()], repr()) :: Cure.Core.Term.t()
  def to_core_record(type_name, syntax_fields, repeated_fields, repr),
    do: to_core_record(type_name, syntax_fields, repeated_fields, repr, %{}, true)

  @spec to_core_record(String.t() | atom(), [String.t()], [String.t()], repr(), map()) :: Cure.Core.Term.t()
  def to_core_record(type_name, syntax_fields, repeated_fields, repr, field_types),
    do: to_core_record(type_name, syntax_fields, repeated_fields, repr, field_types, true)

  @doc "Encode a nested syntax record without the reserved expansion context field."
  @spec to_core_record_without_context(String.t() | atom(), [String.t()], [String.t()], repr()) ::
          Cure.Core.Term.t()
  def to_core_record_without_context(type_name, syntax_fields, repeated_fields, repr),
    do: to_core_record(type_name, syntax_fields, repeated_fields, repr, %{}, false)

  @spec to_core_record_without_context(String.t() | atom(), [String.t()], [String.t()], repr(), map()) ::
          Cure.Core.Term.t()
  def to_core_record_without_context(type_name, syntax_fields, repeated_fields, repr, field_types),
    do: to_core_record(type_name, syntax_fields, repeated_fields, repr, field_types, false)

  defp to_core_record(
         type_name,
         syntax_fields,
         repeated_fields,
         {:syn_node, _tag, attrs, kids},
         field_types,
         include_context?
       ) do
    name = if is_binary(type_name), do: String.to_atom(type_name), else: type_name

    args =
      syntax_fields
      |> Enum.zip(kids)
      |> Enum.map(&to_core_record_field(&1, repeated_fields, field_types))

    args =
      if not include_context? or @context_field in syntax_fields,
        do: args,
        else: args ++ [to_core(context_attr(attrs))]

    {:ctor, name, args}
  end

  defp to_core_record(_type_name, _syntax_fields, _repeated_fields, repr, _field_types, _include_context?),
    do: to_core(repr)

  defp to_core_record_field({field, kid}, repeated_fields, field_types) do
    if field in repeated_fields do
      case Map.get(field_types, field) do
        {:primitive, shape} -> to_core_primitive_list(kid, shape)
        _ -> to_core_syntax_list(kid)
      end
    else
      case Map.get(field_types, field) do
        {:record, nested_name, nested_fields} ->
          nested_repeated =
            nested_fields
            |> Enum.filter(&(&1.cardinality in [:repeated, :one_or_more]))
            |> Enum.map(& &1.name)

          nested_field_types = primitive_field_types(nested_fields)

          to_core_record(
            nested_name,
            Enum.map(nested_fields, & &1.name),
            nested_repeated,
            kid,
            nested_field_types,
            false
          )

        {:primitive, shape} ->
          to_core_primitive(kid, shape)

        _ ->
          to_core(kid)
      end
    end
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

  defp to_core_primitive_list({:syn_raw, {:s_list, [{:s_list, items}]}}, shape),
    do: to_core_list(Enum.map(items, fn item -> to_core_primitive({:syn_raw, item}, shape) end))

  defp to_core_primitive_list({:syn_raw, {:s_list, items}}, shape),
    do: to_core_list(Enum.map(items, fn item -> to_core_primitive({:syn_raw, item}, shape) end))

  defp to_core_primitive_list(repr, shape), do: to_core_list([to_core_primitive(repr, shape)])

  defp to_core_primitive({:syn_leaf, :literal, _attrs, {:s_int, value}}, "Int"), do: {:int_lit, value}
  defp to_core_primitive({:syn_raw, {:s_int, value}}, "Int"), do: {:int_lit, value}
  defp to_core_primitive({:syn_leaf, :literal, _attrs, {:s_float, value}}, "Float"), do: {:float_lit, value}
  defp to_core_primitive({:syn_raw, {:s_float, value}}, "Float"), do: {:float_lit, value}
  defp to_core_primitive({:syn_leaf, :literal, _attrs, {:s_atom, value}}, "Atom"), do: {:atom_lit, value}
  defp to_core_primitive({:syn_raw, {:s_atom, value}}, "Atom"), do: {:atom_lit, value}

  defp to_core_primitive({:syn_leaf, :literal, _attrs, {:s_bool, true}}, "Bool"), do: {:ctor, :True, []}
  defp to_core_primitive({:syn_leaf, :literal, _attrs, {:s_bool, false}}, "Bool"), do: {:ctor, :False, []}
  defp to_core_primitive({:syn_raw, {:s_bool, true}}, "Bool"), do: {:ctor, :True, []}
  defp to_core_primitive({:syn_raw, {:s_bool, false}}, "Bool"), do: {:ctor, :False, []}
  defp to_core_primitive({:syn_raw, {:s_syntax, repr}}, shape), do: to_core_primitive(repr, shape)

  defp to_core_primitive(repr, _shape), do: to_core(repr)

  @doc "Encode a literal capture according to a primitive family shape."
  @spec to_core_primitive_value(repr(), String.t()) :: Cure.Core.Term.t()
  def to_core_primitive_value(repr, shape), do: to_core_primitive(repr, shape)

  defp primitive_field_types(fields) do
    fields
    |> Enum.filter(&(&1.shape in ["Int", "Float", "Atom", "Bool"]))
    |> Map.new(&{&1.name, {:primitive, &1.shape}})
  end

  defp context_attr(attrs) do
    case List.keyfind(attrs, :expansion_context, 0) do
      {:expansion_context, {:s_syntax, repr}} -> repr
      _ -> {:syn_raw, :s_opaque}
    end
  end

  @doc "Decode a normalized Core value of Std.Syntax into the mirror representation."
  @spec from_core(Cure.Core.Term.t()) :: repr() | {:error, term()}
  def from_core(term), do: decode_core(canonicalize_core(term))

  @doc """
  Validate syntax that is about to cross from macro evaluation into elaboration.

  `Std.Syntax.Raw` deliberately permits construction without semantic checks, but
  raw and quoted values are reflection forms rather than executable expansion
  nodes. Keeping this boundary here means malformed advanced syntax gets a
  deterministic macro diagnostic instead of reaching an elaborator catch-all or
  causing a host exception. `Failure` is intentionally accepted because the
  legacy direct-Syntax failure protocol decodes it as an author diagnostic.
  """
  @spec validate_expansion(repr()) :: :ok | {:error, term()}
  def validate_expansion(repr), do: validate_expansion_node(repr, [])

  @doc "Decode the source-level MacroResult wrapper, if present."
  @spec from_core_macro_result(Cure.Core.Term.t()) ::
          {:expanded, repr()}
          | {:rejected, [repr()]}
          | :not_macro_result
          | {:error, term()}
  def from_core_macro_result(term) do
    case canonicalize_core(term) do
      {:ctor, :"Std.Syntax#Expanded", [syntax]} ->
        case from_core(syntax) do
          {:error, _} = error -> error
          repr -> {:expanded, repr}
        end

      {:ctor, :"Std.Syntax#Rejected", [diagnostics]} ->
        case decode_macro_diagnostics(diagnostics) do
          {:ok, values} -> {:rejected, values}
          error -> error
        end

      {:ctor, :"Std.Result#Ok", [syntax]} ->
        case from_core(syntax) do
          {:error, _} = error -> error
          repr -> {:expanded, repr}
        end

      {:ctor, :"Std.Result#Error", [diagnostic]} ->
        case decode_macro_diagnostics(diagnostic) do
          {:ok, values} -> {:rejected, values}
          error -> error
        end

      _ ->
        :not_macro_result
    end
  end

  defp decode_macro_diagnostics(value) do
    case from_core(value) do
      {:error, _} ->
        with {:ok, diagnostics} <- from_core_list(value),
             {:ok, diagnostics} <- map_results(diagnostics, &from_core/1),
             true <- Enum.all?(diagnostics, &syntax_repr?/1) do
          {:ok, diagnostics}
        else
          _ -> {:error, :invalid_macro_diagnostics}
        end

      repr when is_tuple(repr) ->
        if syntax_repr?(repr), do: {:ok, [repr]}, else: {:error, :invalid_macro_diagnostic}
    end
  end

  defp decode_core({:ctor, :"Std.Syntax#Node", [{:atom_lit, tag}, attrs, kids]}) do
    with {:ok, attrs} <- from_core_attrs(attrs),
         {:ok, kids} <- from_core_list(kids),
         {:ok, kids} <- map_results(kids, &from_core/1),
         true <- Enum.all?(kids, &syntax_repr?/1) do
      {:syn_node, tag, attrs, kids}
    else
      _ -> {:error, {:invalid_syntax_node, attrs, kids}}
    end
  end

  defp decode_core({:ctor, :"Std.Syntax#Leaf", [{:atom_lit, tag}, attrs, lit]}) do
    with {:ok, attrs} <- from_core_attrs(attrs),
         {:ok, lit} <- from_core_synlit(lit) do
      {:syn_leaf, tag, attrs, lit}
    else
      _ -> {:error, {:invalid_syntax_leaf, tag}}
    end
  end

  defp decode_core({:ctor, :"Std.Syntax#Raw", [lit]}) do
    case from_core_synlit(lit) do
      {:ok, lit} -> {:syn_raw, lit}
      error -> error
    end
  end

  defp decode_core({:ctor, :"Std.Syntax#Quoted", [syntax]}) do
    case from_core(syntax) do
      {:error, _} = error -> error
      syntax -> {:syn_quoted, syntax}
    end
  end

  defp decode_core({:ctor, :"Std.Syntax#Failure", [{:atom_lit, name}, args]}) do
    with {:ok, args} <- from_core_list(args),
         {:ok, args} <- map_results(args, &from_core/1),
         true <- Enum.all?(args, &syntax_repr?/1) do
      {:syn_failure, name, args}
    else
      _ -> {:error, {:invalid_syntax_failure, name}}
    end
  end

  defp decode_core(other), do: {:error, {:unsupported_syntax_core, other}}

  defp validate_expansion_node({:syn_node, tag, attrs, kids}, path)
       when is_atom(tag) and is_list(attrs) and is_list(kids) do
    with :ok <- validate_attrs(attrs, path),
         :ok <- validate_expansion_children(kids, path) do
      :ok
    end
  end

  defp validate_expansion_node({:syn_leaf, tag, attrs, lit}, path)
       when is_atom(tag) and is_list(attrs) do
    with :ok <- validate_attrs(attrs, path),
         :ok <- validate_synlit(lit, path) do
      :ok
    end
  end

  defp validate_expansion_node({:syn_failure, _name, _args}, _path), do: :ok

  defp validate_expansion_node({:syn_raw, _lit}, path),
    do: {:error, {:raw_syntax_in_expansion, path}}

  defp validate_expansion_node({:syn_quoted, _syntax}, path),
    do: {:error, {:quoted_syntax_in_expansion, path}}

  defp validate_expansion_node(_other, path),
    do: {:error, {:malformed_expansion_syntax, path}}

  defp validate_expansion_children(children, path) do
    children
    |> Enum.with_index()
    |> Enum.reduce_while(:ok, fn {child, index}, :ok ->
      case validate_expansion_node(child, [{:child, index} | path]) do
        :ok -> {:cont, :ok}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp validate_attrs(attrs, path) do
    attrs
    |> Enum.with_index()
    |> Enum.reduce_while(:ok, fn
      {{key, value}, index}, :ok when is_atom(key) ->
        case validate_synlit(value, [{:attribute, key, index} | path]) do
          :ok -> {:cont, :ok}
          {:error, _} = error -> {:halt, error}
        end

      {_attribute, index}, :ok ->
        {:halt, {:error, {:malformed_expansion_attribute, [{:attribute, index} | path]}}}
    end)
  end

  defp validate_synlit({:s_int, value}, _path) when is_integer(value), do: :ok
  defp validate_synlit({:s_float, value}, _path) when is_float(value), do: :ok
  defp validate_synlit({:s_str, value}, _path) when is_binary(value), do: :ok
  defp validate_synlit({:s_bool, value}, _path) when is_boolean(value), do: :ok
  defp validate_synlit({:s_atom, value}, _path) when is_atom(value), do: :ok

  defp validate_synlit({:s_list, values}, path) when is_list(values) do
    Enum.reduce_while(values, :ok, fn value, :ok ->
      case validate_synlit(value, [{:list_item} | path]) do
        :ok -> {:cont, :ok}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp validate_synlit({:s_syntax, syntax}, path),
    do: validate_expansion_node(syntax, [{:syntax_literal} | path])

  defp validate_synlit({:s_map, pairs}, path) when is_list(pairs) do
    Enum.reduce_while(pairs, :ok, fn
      {key, value}, :ok ->
        with :ok <- validate_synlit(key, [{:map_key} | path]),
             :ok <- validate_synlit(value, [{:map_value} | path]) do
          {:cont, :ok}
        else
          {:error, _} = error -> {:halt, error}
        end

      _pair, :ok -> {:halt, {:error, {:malformed_expansion_map, path}}}
    end)
  end

  defp validate_synlit(:s_opaque, _path), do: :ok

  defp validate_synlit(_other, path),
    do: {:error, {:malformed_expansion_literal, path}}

  defp ctor(name, args), do: {:ctor, canonical_ctor(name), args}

  defp canonical_ctor(name) when name in [:True, :False],
    do: Cure.Elab.Name.qualify("Std.Bool", name)

  defp canonical_ctor(name) when name in [:Nil, :Cons],
    do: Cure.Elab.Name.qualify("Std.List", name)

  defp canonical_ctor(name), do: Cure.Elab.Name.qualify("Std.Syntax", name)

  defp canonicalize_core({:ctor, name, args}) do
    base = Cure.Elab.Name.base(name) |> String.to_atom()
    canonical_name = if syntax_ctor?(base), do: canonical_ctor(base), else: name
    {:ctor, canonical_name, Enum.map(args, &canonicalize_core/1)}
  end

  defp canonicalize_core({:app, f, a}), do: {:app, canonicalize_core(f), canonicalize_core(a)}
  defp canonicalize_core({:lam, g, d, b}), do: {:lam, g, canonicalize_core(d), canonicalize_core(b)}
  defp canonicalize_core({:pi, g, d, c}), do: {:pi, g, canonicalize_core(d), canonicalize_core(c)}

  defp canonicalize_core({:data, n, ps, is}),
    do: {:data, n, Enum.map(ps, &canonicalize_core/1), Enum.map(is, &canonicalize_core/1)}

  defp canonicalize_core(other), do: other

  defp syntax_ctor?(name),
    do:
      name in [
        :Node,
        :Leaf,
        :Raw,
        :Quoted,
        :Failure,
        :KV,
        :SInt,
        :SFloat,
        :SStr,
        :SBool,
        :SAtom,
        :SList,
        :SSyntax,
        :SMap,
        :SOpaque,
        :SPair,
        :True,
        :False,
        :Nil,
        :Cons
      ]

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
             {:ctor, :"Std.Syntax#KV", [{:atom_lit, key}, lit]} ->
               with {:ok, lit} <- from_core_synlit(lit), do: {key, lit}

             _ ->
               {:error, :invalid_syntax_attr}
           end) do
      {:ok, attrs}
    else
      _ -> {:error, {:invalid_syntax_attrs, core}}
    end
  end

  defp from_core_list({:ctor, :"Std.List#Nil", []}), do: {:ok, []}

  defp from_core_list({:ctor, :"Std.List#Cons", [head, tail]}) do
    with {:ok, rest} <- from_core_list(tail), do: {:ok, [head | rest]}
  end

  defp from_core_list(_), do: {:error, :invalid_syntax_list}

  defp from_core_synlit({:ctor, :"Std.Syntax#SInt", [{:int_lit, n}]}), do: {:ok, {:s_int, n}}
  defp from_core_synlit({:ctor, :"Std.Syntax#SFloat", [{:float_lit, f}]}), do: {:ok, {:s_float, f}}

  defp from_core_synlit({:ctor, :"Std.Syntax#SStr", [chars]}) do
    with {:ok, chars} <- from_core_list(chars),
         true <- Enum.all?(chars, &match?({:bounded_lit, n} when is_integer(n), &1)) do
      {:ok, {:s_str, chars |> Enum.map(fn {:bounded_lit, n} -> n end) |> List.to_string()}}
    else
      _ -> {:error, :invalid_syntax_string}
    end
  end

  defp from_core_synlit({:ctor, :"Std.Syntax#SBool", [{:ctor, :"Std.Bool#True", []}]}), do: {:ok, {:s_bool, true}}
  defp from_core_synlit({:ctor, :"Std.Syntax#SBool", [{:ctor, :"Std.Bool#False", []}]}), do: {:ok, {:s_bool, false}}
  defp from_core_synlit({:ctor, :"Std.Syntax#SAtom", [{:atom_lit, a}]}), do: {:ok, {:s_atom, a}}

  defp from_core_synlit({:ctor, :"Std.Syntax#SList", [items]}) do
    with {:ok, items} <- from_core_list(items),
         {:ok, items} <- map_results(items, &from_core_synlit/1) do
      {:ok, {:s_list, items}}
    end
  end

  defp from_core_synlit({:ctor, :"Std.Syntax#SSyntax", [syntax]}) do
    case from_core(syntax) do
      {:error, _} = error -> error
      syntax -> {:ok, {:s_syntax, syntax}}
    end
  end

  defp from_core_synlit({:ctor, :"Std.Syntax#SMap", [pairs]}) do
    with {:ok, pairs} <- from_core_list(pairs),
         {:ok, pairs} <- map_results(pairs, &from_core_pair/1) do
      {:ok, {:s_map, pairs}}
    end
  end

  defp from_core_synlit({:ctor, :"Std.Syntax#SOpaque", []}), do: {:ok, :s_opaque}
  defp from_core_synlit(_), do: {:error, :invalid_syntax_literal}

  defp from_core_pair({:ctor, :"Std.Syntax#SPair", [key, value]}) do
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
