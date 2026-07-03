defmodule Antigen.Assays.Elab do
  @moduledoc """
  Elaborator completeness + metamorphic assays (property-based testing for the
  `Surface → Core` elaborator rather than the kernel).

    * elab/completeness — a construction-guaranteed well-typed surface program
      MUST elaborate. A `{:error, _}` is an infection: an unsound REJECT (a
      completeness / reach gap), the elaborator-layer analogue of an unsound
      accept. The kernel cannot catch this — it is behaving correctly when it
      rejects a mis-framed Core term the elaborator produced.

    * elab/metamorphic — a typing-preserving transform (α-rename, arm reorder,
      unused binder) MUST NOT change the accept/reject verdict. A divergence is
      an infection, evidence of a de Bruijn / binder-framing bug. This oracle is
      self-contained (no Idris): it compares the elaborator against itself.

    * elab/erasure — a TWO-SIDED pin on the `{0,ω}` relevance check
      (`Cure.Elab.Relevance`, M8.3). Catalog form: the actual accept/reject
      verdict must equal the expected one (so both an under-strict and an
      over-strict check infect). Metamorphic form: `:same` (frame perturbation —
      verdicts agree) or `:flip` (relevance injection — an accepting base must
      become a rejecting variant, proving the check is load-bearing).

  All consume an `:elab_program` challenge and return `:ok | {:violation, _}`.
  """
  alias Antigen.Challenge
  alias Cure.Elab.{Program, Erase}
  alias Cure.Core.{Kernel, Conv, Eval, Context}

  @assay_fuel 500_000
  @real_kernel %{
    elaborate: &Cure.Elab.Program.elaborate/1,
    infer: &Kernel.infer/2,
    check: &Kernel.check/3,
    conv: &Conv.conv_values?/4,
    eval: &Eval.eval/2
  }
  @doc false
  def __real_kernel__, do: @real_kernel

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :elab_program, assay: "elab/completeness", payload: p}) do
    case elaborate(p.src) do
      {:ok, _} -> :ok
      {:error, e} -> {:violation, {:rejected_well_typed, p.id, e}}
      {:raise, e} -> {:violation, {:raised, p.id, e}}
    end
  end

  def run(%Challenge{kind: :elab_program, assay: "elab/metamorphic", payload: p}) do
    base = verdict_bit(elaborate(p.base_src))
    variant = verdict_bit(elaborate(p.variant_src))

    if base == variant do
      :ok
    else
      {:violation, {:verdict_not_invariant, p.id, p.transform, %{base: base, variant: variant}}}
    end
  end

  # elab/erasure — two-sided {0,ω} relevance-check pin. Catalog form: the actual
  # verdict must match the expected one (an under-strict OR over-strict check both
  # infect).
  def run(%Challenge{kind: :elab_program, assay: "elab/erasure", payload: %{expect: expect} = p}) do
    actual = verdict_bit(elaborate(p.src))

    if actual == expect do
      :ok
    else
      {:violation, {:erasure_verdict_wrong, p.id, %{expected: expect, actual: actual}}}
    end
  end

  # elab/erasure — metamorphic form. `:same` = base and variant verdicts must
  # agree (frame-preserving perturbation); `:flip` = an accepting base must become
  # a rejecting variant (the relevance injection is load-bearing).
  def run(%Challenge{kind: :elab_program, assay: "elab/erasure", payload: %{relation: rel} = p}) do
    base = verdict_bit(elaborate(p.base_src))
    variant = verdict_bit(elaborate(p.variant_src))

    ok? =
      case rel do
        :same -> base == variant
        :flip -> base == :accept and variant == :reject
      end

    if ok? do
      :ok
    else
      {:violation, {:erasure_relation_wrong, p.id, p.transform, %{relation: rel, base: base, variant: variant}}}
    end
  end

  # elab/soundness — the emitted core is independently re-checked by the trusted
  # kernel: every def the elaborator produced must type-check at its emitted type.
  def run(%Challenge{kind: :elab_program, assay: "elab/soundness"} = c),
    do: run(c, @real_kernel)

  def run(%Challenge{kind: :elab_program, assay: "elab/soundness", payload: p}, k) do
    case safe_elaborate(k, p.src) do
      {:ok, env} -> check_all_defs(env, k)
      {:error, _} -> :ok                                   # reject -> elab/completeness' job
      {:raise, e} -> {:violation, {:elaborator_raised, p.id, e}}
    end
  end

  defp safe_elaborate(k, src) do
    case k.elaborate.(src) do
      {:ok, env} -> {:ok, env}
      {:error, e} -> {:error, e}
      other -> {:error, {:unexpected, other}}
    end
  rescue
    ex -> {:raise, Exception.message(ex)}
  catch
    kind, reason -> {:raise, {kind, reason}}
  end

  # Fold env.defs in a fixed key order; first infection wins (deterministic).
  defp check_all_defs(env, k) do
    ctx = Context.empty(env)

    env.defs
    |> Enum.sort_by(fn {name, _} -> name end)
    |> Enum.find_value(:ok, fn {name, %{type: ty, body: body}} ->
      if Erase.has_hole?(body) do
        nil                                                # skip incomplete def
      else
        case check_one(k, ctx, name, ty, body) do
          :ok -> nil
          {:violation, _} = v -> v
        end
      end
    end)
  end

  # infer -> Conv (with a check-fallback for checking-mode-only forms, e.g.
  # parameter-bearing constructor bodies the kernel refuses to infer).
  defp check_one(k, ctx, name, ty, body) do
    case k.infer.(ctx, body) do
      {:error, {:ctor_requires_checking_mode, _}} ->
        # Introduction form the kernel only checks (parameter-bearing ctor, etc.):
        # check against the declared type. `check` re-derives the constructor's
        # actual family/args and Conv-compares internally, so a wrong annotation
        # is still caught.
        case k.check.(ctx, body, k.eval.(ty, [])) do
          :ok -> :ok
          {:error, e} -> {:violation, {:core_ill_typed, name, e}}
        end

      {:error, e} ->
        {:violation, {:core_ill_typed, name, e}}

      {:ok, inferred} ->
        ty_v = k.eval.(ty, [])
        if k.conv.(inferred, ty_v, Context.length(ctx), Context.signature(ctx)) do
          :ok
        else
          {:violation, {:type_annotation_wrong, name, %{inferred: inferred, declared: ty}}}
        end
    end
  end

  # Elaborate, normalizing a raised exception into a tagged value so a crash in
  # the elaborator counts as its own infection class rather than aborting the run.
  defp elaborate(src) do
    try do
      case Program.elaborate(src) do
        {:ok, env} -> {:ok, env}
        {:error, e} -> {:error, e}
        other -> {:error, {:unexpected, other}}
      end
    rescue
      ex -> {:raise, Exception.message(ex)}
    catch
      kind, reason -> {:raise, {kind, reason}}
    end
  end

  # Collapse an elaboration result to its accept/reject bit (metamorphic compares
  # only the bit, not the specific error — different arms may report different
  # errors while agreeing on rejection).
  defp verdict_bit({:ok, _}), do: :accept
  defp verdict_bit(_), do: :reject
end
