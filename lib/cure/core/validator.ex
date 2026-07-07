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

  @doc "Active config for kernel admission; Wave-0 by default, overridable in config/tests."
  @spec check_def_config() :: config()
  def check_def_config, do: Application.get_env(:cure, :final_core_config, @wave0_config)

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

  @doc "Validate `term` against the Wave-0 config."
  @spec validate(tuple()) :: {:ok, [diagnostic()]} | {:error, [diagnostic()]}
  def validate(term), do: validate(term, @wave0_config)

  @doc """
  Validate `term` against `config`. Returns `{:error, rejections}` if any
  `:reject`-mode clause is violated, else `{:ok, warnings}`.
  """
  @spec validate(tuple(), config()) :: {:ok, [diagnostic()]} | {:error, [diagnostic()]}
  def validate(term, config) do
    diags =
      for node <- nodes(term),
          {clause, mode} <- config,
          mode != :off,
          msg = violation(clause, node),
          msg != nil do
        %{clause: clause, mode: mode, message: msg, node: node}
      end

    case Enum.filter(diags, &(&1.mode == :reject)) do
      [] -> {:ok, Enum.filter(diags, &(&1.mode == :warn))}
      rejections -> {:error, rejections}
    end
  end

  # -- clause predicates: node -> nil (ok) | message (violation) --------------
  # Wave-0-active (legacy-form detectors). Match exact node arities so a :case
  # branch never collides with a 2-tuple :refl node.

  defp violation(:no_hole, {:hole, _}), do: "hole present in Core term (K3)"

  defp violation(:no_eq_node, {:eq, _, _, _}), do: "primitive :eq node; use inductive Eq (K1)"
  defp violation(:no_eq_node, {:refl, _}), do: "primitive :refl node; use ctor refl (K1)"
  defp violation(:no_eq_node, {:rewrite, _, _, _}), do: "primitive :rewrite node; use case-sugar (K1)"

  defp violation(:no_prim_node, {:prim, _, _}), do: "primitive :prim node; use delta-globals (K2)"

  defp violation(:no_absurd_node, {:absurd}), do: "absurd node; use empty case (K4)"

  # -- deferred checklist clauses (`:off` in Wave 0, ready to flip) ------------

  # grade_on_binders — current 3-tuple binders carry no grade; the future graded
  # 4-tuple forms ({:pi, grade, dom, cod}) do NOT match and so pass.
  defp violation(:grade_on_binders, {:pi, _, _}), do: "pi binder carries no grade"
  defp violation(:grade_on_binders, {:lam, _, _}), do: "lam binder carries no grade"
  defp violation(:grade_on_binders, {:sigma, _, _}), do: "sigma binder carries no grade"

  # qualified_syms — bare-atom identity instead of a qualified Sym.
  defp violation(:qualified_syms, {:global, n}) when is_atom(n),
    do: "global uses a bare atom, not a qualified symbol (K12)"

  defp violation(:qualified_syms, {:data, n, _, _}) when is_atom(n),
    do: "data family uses a bare atom, not a qualified symbol (K12)"

  defp violation(:qualified_syms, {:ctor, n, _}) when is_atom(n),
    do: "constructor uses a bare atom, not a qualified symbol (K12)"

  # level_expr — integer level instead of a level-expression.
  defp violation(:level_expr, {:type, l}) when is_integer(l),
    do: "universe level is an integer, not a level-expression (K7)"

  # ctor_signature / case_coverage / usage_relevance / no_legacy_reducer are
  # non-structural (need the env / typing / reduction) — enforced in the kernel
  # when their wave lands, never here. They fall through to the catch-all.

  # non-firing fallback for every clause/node not matched above
  defp violation(_clause, _node), do: nil
end
