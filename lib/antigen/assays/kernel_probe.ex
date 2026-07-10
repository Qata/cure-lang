defmodule Antigen.Assays.KernelProbe do
  @moduledoc """
  `kernel/probe` — a coverage-completion vertical for the kernel's def-level and
  inference-mode *defensive* clauses that no term-shaped generator reaches, because
  they are entry points into `check_def`/`validate_certificate`/`check_family`/
  `normalize/3` (not `infer` of a single closed term) or `infer` rejections gated
  out of the live campaign by the runner's `well_formed?` filter.

  Each probe is a real soundness assertion — the kernel MUST return the documented
  verdict for the deliberately-shaped input (reject the ill-typed term, certify the
  body-less builtin op, reject the over-ceiling family, pass the field error through
  the non-family `remap_index_error` clause, …). A wrong verdict is an infection.

  Oracle = the fixed expected outcome per probe (`expected/1`); the payload carries
  only the probe tag, so `Coverage.terms_of` returns `[]` and the challenge bypasses
  the term-well-formedness gate (like `check/verdict`, `serialize/decode`).
  """
  alias Antigen.Challenge
  alias Cure.Core.{Kernel, Builtins, Env, Context, Eval, Inductive, Universe, Quote, Serialize, Certificate}

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :kernel_probe, payload: %{probe: probe}}) do
    got = evaluate(probe)

    if matches?(probe, got) do
      :ok
    else
      {:violation, {:kernel_probe_wrong_verdict, probe, got}}
    end
  end

  # -- the base env: canonical families (Bool/Nat/Eq/Sigma/List) + 25 builtin-ops --
  defp base_env, do: Builtins.seed(Env.empty())

  # -- per-probe kernel invocation (returns the raw kernel result) --
  defp evaluate(:infer_absurd), do: Kernel.infer(ctx(), {:absurd})
  defp evaluate(:infer_fields_only_ctor), do: Kernel.infer(ctx(), {:ctor, :mk_pair, [@z, @z]})
  defp evaluate(:check_ctor_arity), do: Kernel.check(ctx(), {:ctor, :S, [@z, @z]}, Eval.eval(@nat, []))
  defp evaluate(:check_def_unknown), do: Kernel.check_def(base_env(), :nosuchdef)
  defp evaluate(:check_def_builtin_op), do: Kernel.check_def(base_env(), :int_add)
  defp evaluate(:validate_cert_builtin_op), do: Kernel.validate_certificate(base_env(), :int_add)

  defp evaluate(:family_ceiling) do
    fam = Inductive.family(:TooHigh, [], [], Universe.ceiling() + 1)
    Kernel.check_family(base_env(), fam)
  end

  defp evaluate(:normalize_opts), do: Kernel.normalize(ctx(), {:nat_lit, 3}, [])

  # A def whose body is a hole: `check` admits a hole against any type (K3), so
  # check_def succeeds, but the Final-Core validator's `no_hole: :warn` clause
  # produces a warning — driving the warning-emit fold in `run_final_core_validator`.
  defp evaluate(:validator_warn_emit) do
    env = Env.add_def(base_env(), :holey, @nat, {:hole, :h})
    Kernel.check_def(env, :holey)
  end

  # A constructor field whose expected type is a NON-family value (`Int`), checked
  # against a mismatching term: `remap_index_error` must PASS THE ERROR THROUGH
  # (the `:index_mismatch` remap fires only when the expected type is a `:vdata`).
  defp evaluate(:remap_index_passthrough) do
    fam = Inductive.family(:Wrap, [], [], 0)
    ctor = Inductive.ctor(:wrap, [{:v, {:int_type}}], [], [:present], [])
    env = Inductive.declare(base_env(), fam, [ctor])
    Kernel.check(Context.empty(env), {:ctor, :wrap, [{:type, 0}]}, {:vdata, :Wrap, []})
  end

  # `Quote.reify` of a data value whose family is ABSENT from the (non-nil) sig:
  # `split_data_args`'s family-not-found fallback treats every arg as a param
  # rather than crashing (defensive — a value reified against a foreign/partial
  # signature). The lone "unsure" cold line; a real, if rarely-taken, path.
  defp evaluate(:quote_foreign_vdata),
    do: Quote.reify({:vdata, :Ghost, [{:vtype, 0}]}, 0, base_env())

  # Strict-positivity check where the family occurs THROUGH another datatype's
  # constructor field (`Bad`'s ctor takes `Wrap -> Nat`; `Wrap`'s ctor takes
  # `Bad`): `occurs_deep?` must recurse into `Wrap`'s ctors and reject `Bad`.
  defp evaluate(:positivity_through_ctor) do
    env =
      base_env()
      |> Inductive.declare(Inductive.family(:Wrap, [], [], 0),
        [Inductive.ctor(:wrapB, [{:a, {:data, :Bad, [], []}}], [], [:present], [])])
      |> Inductive.declare(Inductive.family(:Bad, [], [], 0),
        [Inductive.ctor(:mkA, [{:f, {:pi, {:data, :Wrap, [], []}, @nat}}], [], [:present], [])])

    Inductive.positive?(env, Inductive.family(:Bad, [], [], 0))
  end

  # Deserialize a term carrying a symbol name that is NOT an already-interned
  # atom (adversarial / foreign serialized input): `sym_atom` must fail cleanly
  # with `:unknown_symbol` rather than mint a new permanent atom.
  defp evaluate(:decode_unknown_symbol) do
    enc = Serialize.encode({:global, :Zqxjw})
    Serialize.decode(String.replace(enc, "Zqxjw", "Zzz_never_interned_9973"))
  end

  # Size-change certification of a self-call that UNDER-APPLIES itself
  # (`f(a,b) = f(a)`): the change-matrix row for the missing argument is `nil`,
  # so `arg_relation(nil, _)` yields `:unknown` and the def is (soundly) rejected.
  defp evaluate(:cert_under_application) do
    body = {:lam, @nat, {:lam, @nat, {:app, {:global, :f}, {:var, 1}}}}
    env = Env.add_def(base_env(), :f, {:pi, @nat, {:pi, @nat, @nat}}, body)
    Certificate.terminating?(:f, body, env)
  end

  # Certification whose forward reach pulls in a DANGLING callee (`f → g → h`,
  # `h` undefined): `callees_env`/`reaches?` must treat the body-less global as a
  # leaf (`_ -> []`) instead of crashing; with no cycle back to `f` it certifies.
  defp evaluate(:cert_dangling_callee) do
    body_f = {:lam, @nat, {:app, {:global, :g}, {:var, 0}}}
    body_g = {:lam, @nat, {:app, {:global, :h}, {:var, 0}}}
    env =
      base_env()
      |> Env.add_def(:f, {:pi, @nat, @nat}, body_f)
      |> Env.add_def(:g, {:pi, @nat, @nat}, body_g)

    Certificate.terminating?(:f, body_f, env)
  end

  defp ctx, do: Context.empty(base_env())

  # -- oracle: the verdict each probe MUST return --
  defp matches?(:infer_absurd, r), do: r == {:error, :absurd_in_reachable_position}
  defp matches?(:infer_fields_only_ctor, r), do: match?({:error, {:ctor_requires_checking_mode, _}}, r)
  defp matches?(:check_ctor_arity, r), do: r == {:error, :ctor_arity}
  defp matches?(:check_def_unknown, r), do: r == {:error, :unknown_global}
  defp matches?(:check_def_builtin_op, r), do: r == :ok
  defp matches?(:validate_cert_builtin_op, r), do: match?({:ok, _}, r)
  defp matches?(:family_ceiling, r), do: r == {:error, :universe_ceiling}
  defp matches?(:normalize_opts, r), do: r == {:nat_lit, 3}
  defp matches?(:validator_warn_emit, r), do: r == :ok
  # The field error must survive unremapped (NOT rewritten to :index_mismatch).
  defp matches?(:remap_index_passthrough, r), do: match?({:error, {:conversion_failure, _, _}}, r)
  defp matches?(:quote_foreign_vdata, r), do: match?({:data, :Ghost, _, _}, r)
  defp matches?(:positivity_through_ctor, r), do: r == {:error, {:non_strictly_positive, :mkA}}
  defp matches?(:decode_unknown_symbol, r), do: match?({:error, {:unknown_symbol, _}}, r)
  # Under-application cannot be certified decreasing → soundly rejected (false).
  defp matches?(:cert_under_application, r), do: r == false
  # No cycle back to `f` through the dangling callee → certified total (true).
  defp matches?(:cert_dangling_callee, r), do: r == true
end
