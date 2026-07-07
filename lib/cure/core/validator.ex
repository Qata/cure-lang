defmodule Cure.Core.Validator do
  @moduledoc """
  The Final-Core grammar boundary (Wave 0 / K11a).

  Structurally checks a Core term against the *target* Final-Core grammar (design
  spec §A/§J). Each grammar commitment is a named **clause** with a **mode**:

    * `:off`    — not checked (target shape does not exist in the grammar yet, or
                  the clause is non-structural and enforced elsewhere).
    * `:warn`   — violation detected and reported, not rejected.
    * `:reject` — violation is a hard error.

  Wave-0 runs as pure instrumentation: legacy-detecting clauses `:warn`, the rest
  `:off`, none `:reject`. Each wave flips its clause to `:reject` as the kernel
  stops producing the legacy form. This module never type-checks — that is the
  kernel's job; non-structural clauses (`ctor_signature`, `case_coverage`,
  `usage_relevance`, `no_legacy_reducer`) are registered for completeness but have
  no structural predicate and are enforced in the kernel/reducer when their wave
  lands.
  """

  @type mode :: :off | :warn | :reject
  @type clause :: atom()
  @type config :: %{clause() => mode()}
  @type diagnostic :: %{clause: clause(), mode: mode(), message: String.t(), node: tuple()}

  @clauses [
    :grade_on_binders,
    :usage_relevance,
    :no_eq_node,
    :no_prim_node,
    :no_hole,
    :qualified_syms,
    :ctor_signature,
    :case_coverage,
    :level_expr,
    :no_absurd_node,
    :no_legacy_reducer
  ]

  @wave0_config %{
    grade_on_binders: :off,
    usage_relevance: :off,
    no_eq_node: :warn,
    no_prim_node: :warn,
    no_hole: :warn,
    qualified_syms: :off,
    ctor_signature: :off,
    case_coverage: :off,
    level_expr: :off,
    no_absurd_node: :warn,
    no_legacy_reducer: :off
  }

  @doc "Every registered grammar clause (the executable checklist)."
  @spec clauses() :: [clause()]
  def clauses, do: @clauses

  @doc "The Wave-0 default mode for every clause (pure instrumentation; no :reject)."
  @spec wave0_config() :: config()
  def wave0_config, do: @wave0_config

  @doc "All Core sub-terms of `term`, pre-order (the term itself first)."
  @spec nodes(tuple()) :: [tuple()]
  def nodes(term), do: [term | Enum.flat_map(children(term), &nodes/1)]

  # Immediate Core-term children (NOT the term itself). Both the current binder
  # forms and the future graded 4-tuple forms are matched so the walker survives
  # the later grade reshape. `:case` branches are descended structurally (body
  # only) so a branch tuple is never treated as a node.
  defp children({:pi, dom, cod}), do: [dom, cod]
  defp children({:pi, _grade, dom, cod}), do: [dom, cod]
  defp children({:lam, dom, body}), do: [dom, body]
  defp children({:lam, _grade, dom, body}), do: [dom, body]
  defp children({:sigma, a, b}), do: [a, b]
  defp children({:sigma, _grade, a, b}), do: [a, b]
  defp children({:app, f, a}), do: [f, a]
  defp children({:pair, a, b}), do: [a, b]
  defp children({:fst, p}), do: [p]
  defp children({:snd, p}), do: [p]
  defp children({:data, _n, ps, is}), do: ps ++ is
  defp children({:ctor, _n, args}), do: args
  defp children({:case, s, m, brs}), do: [s, m | Enum.map(brs, fn {_c, _ar, body} -> body end)]
  defp children({:eq, ty, a, b}), do: [ty, a, b]
  defp children({:refl, a}), do: [a]
  defp children({:rewrite, p, m, b}), do: [p, m, b]
  defp children({:prim, _op, args}), do: args
  defp children(_leaf), do: []
end
