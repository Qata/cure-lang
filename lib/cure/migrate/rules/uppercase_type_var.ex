defmodule Cure.Migrate.Rules.UppercaseTypeVar do
  @moduledoc """
  Migration rule: a *free* uppercase identifier in a type-parameter position is
  a type variable and is lowercased to the new edition's convention (spec §5.5).
  This is a `:needs_resolution` rule — an uppercase name in type position parses
  identically to a type constructor (`Int`, a declared `Foo`) and a free type
  variable (`T`); only the per-file `ctx` (built-in + declared + imported type
  names, from `Cure.Migrate.build_ctx/1`) tells them apart. A name in `ctx` is a
  real type and is left untouched; a name not in `ctx` is a type variable and is
  renamed.

  ## Where type positions live

  A function's parameter and return types are carried in the `:function_def`
  node's **meta**, not its children: `params: [{:param, [type: T], name}, …]`
  and `return_type: T`, where each `T` is a type expression — a bare
  `{:variable, [scope: :local], name}` or a `{:function_call, [name: "List"], …}`
  type application (whose constructor name is a meta string, never a variable
  node, so constructors in application position are inherently safe). The rule
  rewrites those meta entries in place.

  ## Consistent rename + collision freshening (spec §7)

  Within one signature every occurrence of a renamed variable becomes the same
  lowercased name. If the lowercased form collides with a name already used in
  that signature (another type variable, e.g. a pre-existing `t`), the binder is
  freshened with the smallest unused numeric suffix — `t` → `t1` → `t2` — checked
  against every name in the signature *and* every rename target already assigned,
  so two renamed binders never merge onto each other either.
  """

  alias Cure.Migrate.Rule

  @doc "The registry entry for this rule."
  @spec rule() :: Rule.t()
  def rule do
    %Rule{
      id: :W_uppercase_type_var,
      description: "a free uppercase type variable is lowercased",
      phase: :needs_resolution,
      tier: :review,
      since: "2026",
      detect_and_rewrite: &detect_and_rewrite/2,
      warning_template: "uppercase type variable will be lowercased"
    }
  end

  @doc false
  @spec detect_and_rewrite(Rule.ast(), Rule.ctx()) :: Rule.result()
  def detect_and_rewrite(ast, ctx) do
    {new_ast, lines} = walk(ast, ctx, [])

    case lines do
      [] -> :no_change
      _ -> {:rewrite, new_ast, Enum.reverse(lines)}
    end
  end

  # ── AST walk: rewrite every function signature, collect warning lines ──────

  defp walk({:function_def, meta, body}, ctx, lines) do
    {new_meta, renamed} = rewrite_signature(meta, ctx)
    lines = if renamed != [], do: [Keyword.get(meta, :line) | lines], else: lines
    {new_body, lines} = walk(body, ctx, lines)
    {{:function_def, new_meta, new_body}, lines}
  end

  defp walk({k, meta, ch}, ctx, lines) when is_list(ch) do
    {new_ch, lines} = walk(ch, ctx, lines)
    {{k, meta, new_ch}, lines}
  end

  defp walk({k, meta, name, inner}, ctx, lines) when is_binary(name) do
    {new_inner, lines} = walk(inner, ctx, lines)
    {{k, meta, name, new_inner}, lines}
  end

  defp walk(l, ctx, lines) when is_list(l) do
    Enum.map_reduce(l, lines, fn child, acc -> walk(child, ctx, acc) end)
  end

  defp walk(other, _ctx, lines), do: {other, lines}

  # ── Signature rewrite ──────────────────────────────────────────────────────

  # Returns {new_meta, renamed_names}. `renamed_names` is [] when nothing changed.
  defp rewrite_signature(meta, ctx) do
    params = Keyword.get(meta, :params, [])
    return_type = Keyword.get(meta, :return_type)

    types =
      (Enum.map(params, &param_type/1) ++ List.wrap(return_type)) |> Enum.reject(&is_nil/1)

    names = Enum.flat_map(types, &type_var_names/1)

    candidates = names |> Enum.filter(&rename?(&1, ctx)) |> Enum.uniq()
    reserved = names |> Enum.reject(&rename?(&1, ctx)) |> MapSet.new()

    rename_map = build_rename_map(candidates, reserved)

    if rename_map == %{} do
      {meta, []}
    else
      new_params = Enum.map(params, &rename_param(&1, rename_map))

      meta =
        meta
        |> Keyword.put(:params, new_params)
        |> put_return_type(return_type, rename_map)

      {meta, Map.keys(rename_map)}
    end
  end

  # Real signatures carry param shapes beyond `{:param, [type: T], name}` (bare
  # variables, dependent binders, …). Only a proper typed `:param` contributes a
  # type expression; every other shape is transparent to this rule.
  defp param_type({:param, pmeta, _name}), do: Keyword.get(pmeta, :type)
  defp param_type(_other), do: nil

  # Rewrite the `:type` of a proper typed param; leave every other param shape
  # (and typeless params) exactly as-is.
  defp rename_param({:param, pmeta, pname} = param, map) do
    case Keyword.fetch(pmeta, :type) do
      {:ok, _type} -> {:param, Keyword.update!(pmeta, :type, &rename_in_type(&1, map)), pname}
      :error -> param
    end
  end

  defp rename_param(other, _map), do: other

  defp put_return_type(meta, nil, _map), do: meta

  defp put_return_type(meta, rt, map) do
    Keyword.put(meta, :return_type, rename_in_type(rt, map))
  end

  # Assign each candidate its lowercased (freshened) target, threading the
  # reserved set so later candidates avoid earlier targets too.
  defp build_rename_map(candidates, reserved) do
    {map, _used} =
      Enum.reduce(candidates, {%{}, reserved}, fn name, {map, used} ->
        target = fresh_lower(name, used)
        {Map.put(map, name, target), MapSet.put(used, target)}
      end)

    map
  end

  # `T` -> `t`; if taken, `t1`, `t2`, … — first form not in `used`.
  defp fresh_lower(name, used) do
    base = String.downcase(name)

    if MapSet.member?(used, base) do
      Stream.iterate(1, &(&1 + 1))
      |> Stream.map(&(base <> Integer.to_string(&1)))
      |> Enum.find(&(not MapSet.member?(used, &1)))
    else
      base
    end
  end

  # ── Type-expression helpers ────────────────────────────────────────────────

  # Every variable name appearing in a type expression, in order.
  defp type_var_names({:variable, _meta, name}) when is_binary(name), do: [name]
  defp type_var_names({_k, _meta, ch}) when is_list(ch), do: Enum.flat_map(ch, &type_var_names/1)
  defp type_var_names(l) when is_list(l), do: Enum.flat_map(l, &type_var_names/1)
  defp type_var_names(_), do: []

  # Rewrite variable nodes whose name is a rename key; recurse into applications.
  defp rename_in_type({:variable, meta, name}, map) when is_binary(name) do
    {:variable, meta, Map.get(map, name, name)}
  end

  defp rename_in_type({k, meta, ch}, map) when is_list(ch) do
    {k, meta, Enum.map(ch, &rename_in_type(&1, map))}
  end

  defp rename_in_type(l, map) when is_list(l), do: Enum.map(l, &rename_in_type(&1, map))
  defp rename_in_type(other, _map), do: other

  # A name is renamed iff it is uppercase-initial (a type-var/constructor spelling)
  # and does NOT resolve to a known type (built-in, declared, or imported).
  defp rename?(name, ctx), do: uppercase_initial?(name) and not MapSet.member?(ctx, name)

  defp uppercase_initial?(<<c, _::binary>>) when c in ?A..?Z, do: true
  defp uppercase_initial?(_), do: false
end
