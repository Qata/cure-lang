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
end
