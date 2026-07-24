defmodule Cure.Elab.EraseRelevanceCollapsibleAgreementGreenGuardTest do
  @moduledoc """
  GREEN_GUARD for FINDING B (erasure-unify cluster): `Cure.Elab.Erase`'s private
  `collapsible_ctor?/3` (lib/cure/elab/erase.ex:190) and
  `Cure.Elab.Relevance`'s private `collapsible_case?/2` (lib/cure/elab/relevance.ex:738)
  are byte-identical judgments ("a case's single branch names its family's ONLY
  constructor, and every one of that constructor's fields is `:erased`")
  maintained as two separate copies. They agree TODAY — there is no live
  behavioral defect to red — but nothing stops them drifting apart on a future
  edit to just one copy.

  This pins the agreement through BOTH modules' PUBLIC entry points
  (`Erase.erase/2` and `Relevance.check/4`), over a table with one collapsible
  family (single ctor, all-erased fields) and one non-collapsible family
  (multiple ctors), by exploiting an OBSERVABLE side effect of each judgment:

    * `Erase.erase/2` on a single-branch `:case` COLLAPSES to the branch body
      (dropping the `:case` node entirely) iff `collapsible_ctor?` is true.
    * `Relevance.check/4` EXEMPTS the scrutinee from the relevance walk iff
      `collapsible_case?` is true — so a case whose scrutinee is an in-scope
      `:erased` parameter is accepted (`:ok`) iff collapsible, and rejected
      (`{:error, {:erased_used_relevantly, …}}`) iff not.

  Passes now (both judgments agree on both families); would go RED the moment
  either private copy's condition drifts from the other's, since the two
  independent observations below would then disagree with each other for the
  same family.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Inductive}
  alias Cure.Elab.{Erase, Relevance}

  @dummy {:data, :Dummy, [], []}
  @motive {:lam, :unrestricted, @dummy, @dummy}

  # Collapsible: `Proof`'s sole constructor `MkProof` has ONE field, erased.
  defp proof_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Proof, [], [], 0), [
      Inductive.ctor(:MkProof, [w: @dummy], [], [:erased])
    ])
  end

  # NOT collapsible: `Bool2` has TWO constructors (even though the branch under
  # test only names one of them).
  defp bool2_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Bool2, [], [], 0), [
      Inductive.ctor(:T2, [], []),
      Inductive.ctor(:F2, [], [])
    ])
  end

  # A single-branch case scrutinising the sole in-scope `:erased` parameter
  # (`{:var, 0}`), whose branch body ignores every field it binds.
  defp erased_scrutinee_case(cname, arity),
    do: {:case, {:var, 0}, @motive, [{cname, arity, {:global, :done}}]}

  defp erased_via_erase?(env, cname, arity) do
    case Erase.erase(env, erased_scrutinee_case(cname, arity)) do
      {:case, _, _, _} -> false
      _collapsed_to_branch_body -> true
    end
  end

  defp exempted_via_relevance?(env, cname, arity) do
    case Relevance.check(env, :f, [:erased], erased_scrutinee_case(cname, arity)) do
      :ok -> true
      {:error, {:erased_used_relevantly, _}} -> false
    end
  end

  test "Erase and Relevance agree: a proof-like single-erased-field ctor collapses AND is exempt" do
    env = proof_env()
    assert erased_via_erase?(env, :MkProof, 1) == true
    assert exempted_via_relevance?(env, :MkProof, 1) == true
  end

  test "Erase and Relevance agree: a multi-constructor family neither collapses nor is exempt" do
    env = bool2_env()
    assert erased_via_erase?(env, :T2, 0) == false
    assert exempted_via_relevance?(env, :T2, 0) == false
  end

  test "the two judgments AGREE with each other across the whole family table" do
    table = [{proof_env(), :MkProof, 1}, {bool2_env(), :T2, 0}]

    for {env, cname, arity} <- table do
      assert erased_via_erase?(env, cname, arity) == exempted_via_relevance?(env, cname, arity),
             "Erase.collapsible_ctor? and Relevance.collapsible_case? DISAGREED for #{cname}/#{arity}"
    end
  end
end
