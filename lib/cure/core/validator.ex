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
    :no_sigma_node,
    :no_rewrite_node,
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
    grade_on_binders: :reject,
    usage_relevance: :off,
    # Phase C flipped `no_eq_node` to :reject even at dev time: the kernel has
    # no `{:eq}`/`{:refl}` clauses left, so any such node in a checked def is a
    # smuggled non-grammar term (firewall breach), not tolerable tech debt.
    # `no_rewrite_node` stays :warn here (dev-time) and rejects at release.
    no_eq_node: :reject,
    # D2 T4b flipped `no_sigma_node` to :reject even at dev time: the kernel has
    # no `{:sigma}`/`{:pair}`/`{:fst}`/`{:snd}` clauses left (T5 strip), so any
    # such node in a checked def is smuggled non-grammar (firewall breach), not
    # tolerable tech debt — same rationale as Phase C's `no_eq_node`.
    no_sigma_node: :reject,
    no_rewrite_node: :warn,
    # K2 flipped `no_prim_node` to :reject even at dev time: the kernel has no
    # `{:prim}`/`{:nprim}` clauses left (arithmetic is registry-keyed builtin-op
    # GLOBALS with certified-δ literal acceleration, spec 2026-07-09), so any
    # such node in a checked def is smuggled non-grammar (firewall breach) —
    # same rationale as Phase C's `no_eq_node` and D2's `no_sigma_node`.
    no_prim_node: :reject,
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

  @doc "The Wave-0 default mode for every clause (instrumentation, except the retired-primitive `no_eq_node` which rejects)."
  @spec wave0_config() :: config()
  def wave0_config, do: @wave0_config

  # The strict *release* grammar: the ratchet applied at the trust boundary
  # (emit / certify / serialize / publish), distinct from the lenient dev-time
  # `check_def_config`. Each landed wave flips its clause to `:reject` here while
  # dev-time checking stays lenient. K3 lands `no_hole: :reject` — no unfilled
  # obligation may escape into a released artifact (holes in erased positions
  # included, since the validator descends where `Erase.erase` would drop them).
  # K4 lands `no_absurd_node: :reject` — the `{:absurd}` node is deleted from final
  # Core; ex-falso is an empty-branch `case` over a provably-uninhabited scrutinee
  # (§H), so no `{:absurd}` term may survive.
  # K1a lands `no_eq_node: :reject` — the primitive `{:eq}`/`{:refl}` identity nodes
  # are dead-producers; no such term may escape into a released artifact (since
  # Phase C this also holds at dev time — see @wave0_config).
  # Phase B/C land `no_rewrite_node: :reject` — every `{:rewrite}` producer was
  # retired (rewrite → J/subst single-branch `:case` transport) and the kernel
  # clauses stripped, so a `{:rewrite}` node in final Core is smuggled grammar.
  # K2 lands `no_prim_node: :reject` — `{:prim}`/`{:nprim}` are stripped from
  # the kernel (builtin-op globals are canonical); explicit here even though
  # wave0 already rejects, so the release ratchet is self-documenting (this was
  # the recorded doc/code drift: §J said :off while wave0 had :warn and release
  # never flipped it).
  @release_config @wave0_config
                  |> Map.put(:no_hole, :reject)
                  |> Map.put(:no_absurd_node, :reject)
                  |> Map.put(:no_eq_node, :reject)
                  |> Map.put(:no_sigma_node, :reject)
                  |> Map.put(:no_rewrite_node, :reject)
                  |> Map.put(:no_prim_node, :reject)

  @doc "The strict Final-Core config enforced at the release/emit boundary (K3+)."
  @spec release_config() :: config()
  def release_config, do: @release_config

  @doc "Active config for kernel admission; Wave-0 by default, overridable in config/tests."
  @spec check_def_config() :: config()
  def check_def_config, do: Application.get_env(:cure, :final_core_config, @wave0_config)

  @doc "All Core sub-terms of `term`, pre-order (the term itself first)."
  @spec nodes(tuple()) :: [tuple()]
  def nodes(term), do: [term | Enum.flat_map(children(term), &nodes/1)]

  # Immediate Core-term children (NOT the term itself). Binders are graded
  # 4-/5-tuples; the grade is not a child. `:case` branches are descended
  # structurally (body only) so a branch tuple is never treated as a node.
  defp children({:pi, _grade, dom, cod}), do: [dom, cod]
  defp children({:lam, _grade, dom, body}), do: [dom, body]
  defp children({:let, _grade, ty, val, body}), do: [ty, val, body]
  defp children({:sigma, a, b}), do: [a, b]
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

  # Fallback for any tuple node NOT explicitly matched above (a genuine leaf like
  # `{:var,_}`/`{:type,_}`/`{:global,_}`/`{:int_lit,_}`, OR an unrecognized/future
  # form such as a graded `:app`/`:ctor` 4-tuple). Descend CONSERVATIVELY into
  # every element that is itself a term-tuple or a list of them, so a forbidden
  # node buried in an unknown wrapper cannot escape the walker (fail-closed).
  # Genuine leaves carry only atoms/ints, so this yields no spurious children.
  defp children(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.flat_map(&term_children/1)

  defp children(_nontuple), do: []

  defp term_children(x) when is_tuple(x), do: [x]

  # Recurse into nested lists. `Enum.filter(xs, &is_tuple/1)` kept only elements that were
  # themselves tuples, so a list OF LISTS of subterms — one level deeper than
  # `validator_unknown_node_test.exs` reaches — was filtered out entirely, and everything
  # inside it escaped a walker whose own comment promises nothing can.
  defp term_children(xs) when is_list(xs), do: Enum.flat_map(xs, &term_children/1)

  defp term_children(_atom_or_scalar), do: []

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

  # no_eq_node covers the two identity-type primitives that are now DEAD-PRODUCERS
  # (K1a): the {:eq} type-former (mk_eq builds inductive {:data,:Equivalent}) and the
  # {:refl} constructor (surface reflexive, symmetry_proof, and bridge_step f3b0e73
  # all build the inductive ctor). Both are :reject in release_config.
  defp violation(:no_eq_node, {:eq, _, _, _}),
    do: "primitive :eq node; use inductive Equivalent (K1)"

  defp violation(:no_eq_node, {:refl, _}),
    do: "primitive :refl node; use ctor reflexive (K1)"

  # no_sigma_node covers the four dependent-pair primitives that are DEAD-PRODUCERS
  # after D2 T2/T3 (%[..] builds the inductive ctor mk_pair, Sigma(..) is the
  # inductive {:data,:Sigma}, .1/.2 are projection globals). :warn while the kernel
  # still carries the clauses (T4a), :reject at release and once T5 strips them.
  defp violation(:no_sigma_node, {:sigma, _, _}),
    do: "primitive :sigma node; use inductive Sigma (D2)"

  defp violation(:no_sigma_node, {:pair, _, _}),
    do: "primitive :pair node; use ctor mk_pair (D2)"

  defp violation(:no_sigma_node, {:fst, _}), do: "primitive :fst node; use projection (D2)"
  defp violation(:no_sigma_node, {:snd, _}), do: "primitive :snd node; use projection (D2)"

  # no_rewrite_node is split out because {:rewrite} is STILL PRODUCED as the
  # transport eliminator (rewrite_plan/symmetry_proof/bridge_step). Retiring it
  # (rewrite→single-branch :case, Phase B) is a structural re-plumbing, so it stays
  # :warn until that lands — flipping it to :reject now would block every
  # rewrite-using program's final Core.
  defp violation(:no_rewrite_node, {:rewrite, _, _, _}),
    do: "primitive :rewrite node; use case-sugar (K1 Phase B)"

  defp violation(:no_prim_node, {:prim, _, _}), do: "primitive :prim node; use delta-globals (K2)"

  defp violation(:no_absurd_node, {:absurd}), do: "absurd node; use empty case (K4)"

  # -- deferred checklist clauses (`:off` in Wave 0, ready to flip) ------------

  # grade_on_binders — a STALE ungraded 3-tuple binder. `Term.term?/1` already
  # rejects these, but Elixir will happily let one flow through a catch-all, so
  # this is the belt to that suspenders. Now `:reject` (was `:off` while the
  # graded reshape was pending).
  defp violation(:grade_on_binders, {:pi, _, _}), do: "pi binder carries no grade"
  defp violation(:grade_on_binders, {:lam, _, _}), do: "lam binder carries no grade"
  defp violation(:grade_on_binders, {:let, _, _, _}), do: "let binder carries no grade"

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
