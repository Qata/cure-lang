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

  Both consume an `:elab_program` challenge and return `:ok | {:violation, _}`.
  """
  alias Antigen.Challenge
  alias Cure.Elab.Program

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
