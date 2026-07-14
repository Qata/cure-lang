# lib/cure/compiler/macro_validate.ex
defmodule Cure.Compiler.MacroValidate do
  @moduledoc """
  Frontend validation of `macro` definitions against the self-proving
  obligations (design 2026-07-11 §3). TCB delta zero — pure analysis over the
  parsed `{:macro_def, …}` AST, upstream of the elaborator.
  """

  alias Cure.Compiler.{MacroFuzz, MacroSyntax}

  @type point :: {:hole_kind, String.t()} | {:keyword, String.t()} | {:failure, String.t()}

  @doc """
  Check a macro's `explain` block covers every structural failure point derived
  from its `syntax`/`literal` rules (design §3.2). Returns `:ok` or
  `{:error, {:missing_diagnosis, uncovered_points}}`.
  """
  @spec check_explain_exhaustive(tuple()) :: :ok | {:error, {:missing_diagnosis, [point]}}
  def check_explain_exhaustive({:macro_def, _meta, rules}) do
    points = derive_points(rules)
    covered = covered_points(rules)

    case Enum.reject(points, &covered?(&1, covered)) do
      [] -> :ok
      uncovered -> {:error, {:missing_diagnosis, uncovered}}
    end
  end

  @doc """
  Enforce all self-proving obligations for the macro definitions in a parsed
  program. The environment is supplied after declaration elaboration so
  computed examples can execute against the module's real signatures.
  """
  @spec check_program(tuple() | list(), Cure.Core.Env.t()) :: :ok | {:error, term()}
  def check_program(ast, env) do
    ast
    |> collect_macro_defs()
    |> Enum.reduce_while(:ok, fn macro_def, :ok ->
      with :ok <- check_reserved_fields(macro_def),
           :ok <- check_explain_if_declared(macro_def),
           :ok <- check_pins_if_explainable(macro_def),
           :ok <- check_examples(macro_def, env),
           :ok <- check_computed_examples(macro_def, env),
           :ok <- check_expansion_proof(macro_def, env) do
        {:cont, :ok}
      else
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  # A handwritten macro may intentionally use the lightweight compatibility
  # surface without an `explain` block. When the author declares that block,
  # enforce the complete self-proving contract; all macros still receive the
  # expansion soundness gate below.
  defp check_explain_if_declared({:macro_def, _meta, rules} = macro_def) do
    if Enum.any?(rules, &(&1[:kind] == :explain)), do: check_explain_exhaustive(macro_def), else: :ok
  end

  defp check_pins_if_explainable({:macro_def, _meta, rules} = macro_def) do
    if Enum.any?(rules, &(&1[:kind] == :explain)), do: check_rules_pinned(macro_def), else: :ok
  end

  # StreamData is a test-only dependency. Structural macro validation remains
  # active in development/release builds; the generative gate runs whenever
  # the optional backend is present (the test environment and CI).
  defp check_expansion_proof(macro_def, env) do
    if Code.ensure_loaded?(StreamData), do: MacroFuzz.check_expansion_proof(macro_def, env), else: :ok
  end

  @doc "Run only the generated expansion gate for transitional classic compiles."
  @spec check_expansion_proofs(tuple() | list(), Cure.Core.Env.t()) :: :ok | {:error, term()}
  def check_expansion_proofs(ast, env) do
    collect_macro_defs(ast)
    |> Enum.reduce_while(:ok, fn macro_def, :ok ->
      case MacroFuzz.check_expansion_proof(macro_def, env) do
        :ok -> {:cont, :ok}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  @doc """
  Check no `computed by` rule declares a hole named `context`.

  A computed rule's derived record carries the reflected expansion context in a
  trailing `context` field, so a hole of that name would take the field's place
  and leave the elab silently blind to where it was invoked. Reserve the name
  and say so, rather than let the hole win in silence.
  """
  @spec check_reserved_fields(tuple()) :: :ok | {:error, {:reserved_syntax_field, String.t(), [String.t()]}}
  def check_reserved_fields({:macro_def, _meta, rules}) do
    field = MacroSyntax.context_field()

    rules
    |> Enum.filter(&(&1[:kind] == :computed))
    |> Enum.filter(&(field in Map.get(&1, :syntax_fields, [])))
    |> Enum.map(& &1.keyword)
    |> case do
      [] -> :ok
      keywords -> {:error, {:reserved_syntax_field, field, keywords}}
    end
  end

  @doc """
  Check every `syntax` rule, including `computed by` rules, carries at least one
  worked example (design §5.1).
  Returns `:ok` or `{:error, {:rule_unpinned, unpinned_keywords}}`.
  """
  @spec check_rules_pinned(tuple()) :: :ok | {:error, {:rule_unpinned, [String.t()]}}
  def check_rules_pinned({:macro_def, _meta, rules}) do
    unpinned =
      rules
      |> Enum.filter(&(&1[:kind] in [:syntax, :computed]))
      |> Enum.filter(&(Map.get(&1, :examples, []) == []))
      |> Enum.map(& &1.keyword)

    case unpinned do
      [] -> :ok
      kws -> {:error, {:rule_unpinned, kws}}
    end
  end

  # Structural Diagnosis: one point per typed hole, per literal segment, AND
  # (for `:syntax` rules) the rule's own dispatch keyword — across all
  # syntax/literal rules, deduped and order-stable.
  #
  # NOTE: a `:syntax` rule's dispatch keyword lives in `rule.keyword`, NOT in
  # `rule.segments` (`segments` is only what follows it). Omitting it would mean
  # the single most common macro-use failure (typing the wrong keyword) could
  # never be required to have an `explain` clause — the plan's own headline
  # example (`syntax every <t: Duration> becomes …`) has NO literal `segments`.
  defp derive_points(rules) do
    rules
    |> Enum.filter(&(&1[:kind] in [:syntax, :literal, :fail]))
    |> Enum.flat_map(fn rule ->
      failure_points =
        case rule do
          %{kind: :fail, name: name} when is_binary(name) -> [{:failure, name}]
          _ -> []
        end

      keyword_points =
        case rule do
          %{kind: :syntax, keyword: kw} when is_binary(kw) -> [{:keyword, kw}]
          _ -> []
        end

      failure_points ++ keyword_points ++ Enum.map(Map.get(rule, :segments, []), &segment_point/1)
    end)
    |> Enum.reject(&is_nil/1)
    |> Enum.uniq()
  end

  defp segment_point({:hole, %{kind: k}}), do: {:hole_kind, k}
  defp segment_point({:lit, w}), do: {:keyword, w}
  defp segment_point(_), do: nil

  # What the explain block covers, as a set of clause points.
  defp covered_points(rules) do
    rules
    |> Enum.filter(&(&1[:kind] == :explain))
    |> Enum.flat_map(& &1.clauses)
    |> Enum.map(& &1.point)
    |> MapSet.new()
  end

  # A `{:category, c}` clause covers a `{:hole_kind, c}` point; a `{:keyword, w}`
  # clause covers a `{:keyword, w}` point.
  defp covered?({:hole_kind, k}, covered), do: MapSet.member?(covered, {:category, k})
  defp covered?({:keyword, w}, covered), do: MapSet.member?(covered, {:keyword, w})
  defp covered?({:failure, name}, covered), do: MapSet.member?(covered, {:category, name})

  defp collect_macro_defs({:macro_def, _meta, _rules} = macro_def), do: [macro_def]

  defp collect_macro_defs({_, _, children}) when is_list(children),
    do: Enum.flat_map(children, &collect_macro_defs/1)

  defp collect_macro_defs(list) when is_list(list),
    do: Enum.flat_map(list, &collect_macro_defs/1)

  defp collect_macro_defs(_other), do: []

  alias Cure.Compiler.Parser
  alias Cure.Elab.MacroExpand

  @doc """
  Check every `syntax` rule's `{:expansion, _}` example actually expands to its
  pinned result, up to α-renaming (design §5.1). `{:type, _}` pins are skipped
  (deferred). Returns `:ok` or `{:error, {:example_mismatch, mismatches}}`.
  """
  @spec check_examples(tuple()) :: :ok | {:error, {:example_mismatch, [map()]}}
  def check_examples(macro_def), do: check_examples(macro_def, nil)

  @doc """
  Check exact and type-only example pins in a module environment.

  Exact pins compare α-normalized surface ASTs. Type-only pins lower their
  expected type and check the expanded expression through the ordinary
  expression elaborator, preserving the module's imports and declarations.
  """
  @spec check_examples(tuple(), Cure.Core.Env.t() | nil) ::
          :ok
          | {:error, {:example_mismatch, [map()]}}
          | {:error, {:example_type_mismatch, [map()]}}
  def check_examples({:macro_def, _meta, rules}, env) do
    results =
      rules
      |> Enum.filter(&(&1[:kind] == :syntax))
      |> Enum.flat_map(fn rule ->
        Enum.map(Map.get(rule, :examples, []), fn %{use_site: use_site, expected: expected} ->
          actual = Parser.expand_example(rules, use_site)
          check_example_pin(rule.keyword, actual, expected, env)
        end)
      end)

    mismatches = for {:mismatch, details} <- results, do: details
    type_failures = for {:type_failure, details} <- results, do: details

    cond do
      type_failures != [] -> {:error, {:example_type_mismatch, type_failures}}
      mismatches != [] -> {:error, {:example_mismatch, mismatches}}
      true -> :ok
    end
  end

  defp check_example_pin(keyword, actual, {:expansion, expected}, _env) do
    if normalize(actual) == normalize(expected) do
      :ok
    else
      {:mismatch, %{keyword: keyword, expected: expected, actual: actual}}
    end
  end

  defp check_example_pin(_keyword, _actual, {:type, _expected}, nil), do: :ok

  defp check_example_pin(keyword, actual, {:type, expected}, env) do
    alias Cure.Core.Context
    alias Cure.Elab.{Declarations, Elaborator}

    case Declarations.lower_type(expected, [], env) do
      {:ok, expected_core} ->
        case Elaborator.elaborate_expr_checked(actual, expected_core, [], Context.empty(env), env) do
          {:ok, _term} -> :ok
          {:error, reason} -> {:type_failure, %{keyword: keyword, expected: expected, actual: actual, reason: reason}}
        end

      {:error, reason} ->
        {:type_failure, %{keyword: keyword, expected: expected, actual: actual, reason: reason}}
    end
  end

  @doc """
  Execute expansion pins attached to `computed by` rules in a module environment.

  The parser deliberately leaves computed uses deferred. This check supplies the
  environment needed by the compile-time executor and reports either a pin
  mismatch or an execution failure without collapsing the latter into a false
  success.
  """
  @spec check_computed_examples(tuple(), Cure.Core.Env.t()) ::
          :ok
          | {:error, {:computed_example_error, [map()]}}
          | {:error, {:example_mismatch, [map()]}}
  def check_computed_examples({:macro_def, _meta, rules}, env) do
    results =
      rules
      |> Enum.filter(&(&1[:kind] == :computed))
      |> Enum.flat_map(fn rule ->
        for %{use_site: use_site, expected: {:expansion, expected}} <- Map.get(rule, :examples, []) do
          actual = Parser.expand_example(rules, use_site)

          case MacroExpand.expand(actual, env) do
            {:ok, expanded} ->
              if normalize(expanded) == normalize(expected) do
                :ok
              else
                {:mismatch, %{keyword: rule.keyword, expected: expected, actual: expanded}}
              end

            {:error, reason} ->
              {:failure, %{keyword: rule.keyword, reason: reason}}
          end
        end
      end)

    failures = for {:failure, details} <- results, do: details
    mismatches = for {:mismatch, details} <- results, do: details

    cond do
      failures != [] -> {:error, {:computed_example_error, failures}}
      mismatches != [] -> {:error, {:example_mismatch, mismatches}}
      true -> :ok
    end
  end

  # α-normalise for example comparison: drop source positions, then collapse
  # `<fresh>` gensym suffixes (`x$0` → `x`) so a template binder and its pin
  # compare equal.
  #
  # A `:variable` node's meta is dropped ENTIRELY (not just line/col): it is
  # provenance about how the identifier was parsed (`scope: :local`,
  # `variant: true`, ...), not part of what the reference denotes. This
  # matters because a `<fresh Name>` marker in BINDER position parses to
  # `{:fresh_name, [line:, col:], name}` (no `scope` key -- that key is only
  # ever attached by the ordinary-identifier parse path) and `freshen/2`'s
  # `apply_freshening` reuses that meta verbatim when rewriting the marker to
  # `{:variable, meta, gensym}`. A hand-written pin's ordinary `h` always
  # carries `scope: :local`. Comparing full meta made every correctly-pinned
  # `<fresh>`-as-binder example spuriously mismatch; the only content that
  # participates in α-equivalence for a variable reference is its (degensym'd)
  # name.
  defp normalize({:variable, _meta, name}) when is_binary(name) do
    {:variable, [], degensym(name)}
  end

  defp normalize({t, meta, children}) when is_list(children) do
    {t, strip_pos(meta), Enum.map(children, &normalize/1)}
  end

  # A scalar-valued node (`:literal`'s {subtype, value} shape — `value` is a raw
  # integer/float/string/bool/atom/char, NOT a list of children) still carries
  # `:line`/`:col` in its meta that must be stripped, exactly like any other node.
  # Without this clause every `:literal` falls through to the catch-all UNCHANGED,
  # so its source position never gets stripped and check_examples rejects almost
  # every real macro example.
  defp normalize({t, meta, value}) when is_list(meta) do
    {t, strip_pos(meta), value}
  end

  defp normalize(other), do: other

  defp strip_pos(meta) when is_list(meta) do
    meta
    |> Enum.reject(fn
      {k, _} when k in [:line, :col] -> true
      _ -> false
    end)
    |> Enum.map(fn
      {k, v} -> {k, normalize_meta_value(v)}
      other -> other
    end)
  end

  defp strip_pos(meta), do: meta

  defp normalize_meta_value(v) when is_tuple(v), do: normalize(v)
  defp normalize_meta_value(v) when is_list(v), do: Enum.map(v, &normalize_meta_value/1)
  defp normalize_meta_value(v), do: v

  defp degensym(name) do
    case Regex.run(~r/^(.+)\$\d+$/, name) do
      [_, base] -> base
      _ -> name
    end
  end
end
