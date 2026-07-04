defmodule Cure.Core.MotiveWfIndexedEqEndpointTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Kernel}

  # Completeness gap residual (TCB note (2)): the DOMAIN path of `check_motive_wf`
  # was fixed by value-recursion (defc6cb, see MotiveWfIndexedDomainTest), but the
  # Eq-ENDPOINT path still reifies. `infer_type_value_sort`'s `{:veq, ty, a, b}`
  # clause value-recurses on the carrier `ty` yet checks the endpoints with
  # `check(ctx, Quote.reify(a, depth), ty)`. `Quote.reify` collapses
  # `{:vdata, name, args}` → `{:data, name, args, []}` (all args in *params*), so an
  # Eq whose endpoints are INDEXED-family type values (e.g. `Eq(Type, SNat(s),
  # SNat(s))`) re-checks with an arity error and is wrongly rejected `:bad_motive`.
  #
  # Fix (Agda `getNumberOfParameters` / Lean `inductive_val.get_nparams` prior
  # art): SIGNATURE-AWARE `Quote.reify` — thread the family signature so the
  # `{:vdata}` read-back recovers the param/index split. Acceptance must equal a
  # non-lossy reify+infer: a genuinely ill-typed endpoint (not inhabiting the
  # carrier) must STILL be rejected (negative control below).

  @dec {:data, :Dec, [], []}

  # Dec: two nullary ctors. SNat(d:Dec): one Dec index — appears as the Eq endpoint.
  defp base_env do
    Env.empty()
    |> Inductive.declare(Inductive.family(:Dec, [], [], 0),
         [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])])
    |> Inductive.declare(Inductive.family(:SNat, [], [{:d, @dec}], 0),
         [Inductive.ctor(:snat0, [], [{:ctor, :Dcoupled, []}])])
  end

  # SNat(s) with s = the motive/def binder (de Bruijn var0).
  @snat_s {:data, :SNat, [], [{:var, 0}]}

  defp snat(idx), do: {:data, :SNat, [], [idx]}

  # POSITIVE: motive `λs. Eq(Type, SNat(s), SNat(s))` — indexed family as BOTH Eq
  # endpoints; refl-inhabited at each refined index. Rejected (`:bad_motive`) by the
  # reify collapse; must be accepted once reify is signature-aware.
  test "an indexed family as an Eq-endpoint motive is well-formed (was :bad_motive)" do
    motive = {:lam, @dec, {:eq, {:type, 0}, @snat_s, @snat_s}}
    def_type = {:pi, @dec, {:eq, {:type, 0}, @snat_s, @snat_s}}

    body =
      {:lam, @dec,
       {:case, {:var, 0}, motive,
        [
          {:Dcoupled, 0, {:refl, snat({:ctor, :Dcoupled, []})}},
          {:Causal, 0, {:refl, snat({:ctor, :Causal, []})}}
        ]}}

    env = Env.add_def(base_env(), :probe, def_type, body)
    assert :ok == Kernel.check_def(env, :probe)
  end

  # NEGATIVE CONTROL: motive `λs. Eq(Type, Dcoupled, Dcoupled)` — the Eq endpoints
  # are Dec VALUES (constructors), not types, so they do not inhabit the carrier
  # `Type`. Signature-aware reify must STILL reject this (no false positive): the
  # endpoint check is a real `check`, not a blanket accept.
  test "an Eq-endpoint motive whose endpoints do not inhabit the carrier is still rejected" do
    neg_motive = {:lam, @dec, {:eq, {:type, 0}, {:ctor, :Dcoupled, []}, {:ctor, :Dcoupled, []}}}
    def_type = {:pi, @dec, @dec}

    body =
      {:lam, @dec,
       {:case, {:var, 0}, neg_motive,
        [{:Dcoupled, 0, {:type, 0}}, {:Causal, 0, {:type, 0}}]}}

    env = Env.add_def(base_env(), :probe, def_type, body)
    assert {:error, :bad_motive} = Kernel.check_def(env, :probe)
  end
end
