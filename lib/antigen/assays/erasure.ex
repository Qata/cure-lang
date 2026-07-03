defmodule Antigen.Assays.Erasure do
  @moduledoc """
  Property tests for the untrusted {0,ω} erasure/relevance machinery
  `Cure.Elab.Erase` / `Cure.Elab.Relevance` (spec: antigen-erasure-relevance).

    * erasure/idempotent — `erase∘erase == erase` + hole preservation (V4a).
    * erasure/selective  — erase keeps exactly the :present positions (ctor + app-head).
    * erasure/wellformed — `term?(t) ⟹ term?(erase t)`.
    * relevance/soundness — an :erased binder used relevantly must be rejected.

  Machinery ops go through an injectable @real map (run/2); negative controls
  weaken the code-under-test without touching `Cure.Elab`/`Cure.Core` or :meck.
  """
  alias Antigen.Challenge
  alias Cure.Elab.{Erase, Relevance}
  alias Cure.Core.{Inductive, Env, Term}

  @real %{
    erase: &Erase.erase/2,
    has_hole?: &Erase.has_hole?/1,
    ctor_quantities: &Inductive.ctor_quantities/2,
    get_def: &Env.get_def/2,
    term?: &Term.term?/1,
    relevance_check: &Relevance.check/4
  }
  @doc false
  def __real__, do: @real

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :erasure_term} = c), do: run(c, @real)

  def run(%Challenge{kind: :erasure_term, assay: "erasure/idempotent", payload: %{env: env, term: t}}, k) do
    once = k.erase.(env, t)
    twice = k.erase.(env, once)

    cond do
      k.has_hole?.(t) == false and k.has_hole?.(once) == true -> {:violation, {:hole_introduced, t}}
      twice != once -> {:violation, {:erase_not_idempotent, t}}
      true -> :ok
    end
  end
end
