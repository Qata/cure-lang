defmodule Cure.Elab.RewriteAsCaseTest do
  @moduledoc """
  Phase B (identity-type-as-inductive, spec 2026-07-04): `rewrite p in body`
  must desugar to a single-branch inductive `:case` on `p | reflexive(w) -> …`,
  emitting NO primitive `{:rewrite, …}` Core node.

  Two fixtures pin the two shapes the revert of `d44edb8` (`c635e8c`) identified
  as distinct:

    (a) VARIABLE endpoints  — the proof's endpoints are (or reduce through) plain
        variables the branch unifier can substitute (`rw01` shape).
    (b) COMPUTED endpoints  — the proof's endpoints are applications, not
        variables (`frp01_par_assoc` shape). This is the case the naive
        body-shift `rw_case_build` drifted (accept→reject); it MUST still accept
        and carry no `{:rewrite}` node.

  Both are RED today: the current elaborator emits `{:rewrite, …}` for every
  producer site.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program
  alias Cure.Core.{Env, Validator}

  defp rewrite_nodes(env, fn_name) do
    env
    |> Env.get_def(fn_name)
    |> Map.fetch!(:body)
    |> Validator.nodes()
    |> Enum.filter(&match?({:rewrite, _, _, _}, &1))
  end

  # (a) variable-endpoint rewrite: rw01's `plus_zero_right`.
  @variable_src """
  mod RwCaseVar
    type Nat = Z | S(Nat)
    fn plus(m: Nat, n: Nat) -> Nat = match m
      Z() -> n
      S(k) -> S(plus(k, n))
    fn plus_zero_right(n: Nat) -> Equivalent(Nat, plus(n, Z), n) = match n
      Z() -> reflexive(Z)
      S(k) -> rewrite plus_zero_right(k) in reflexive(S(k))
  end
  """

  test "(a) a variable-endpoint rewrite accepts and emits no {:rewrite} node" do
    assert {:ok, env} = Program.elaborate(@variable_src)
    assert rewrite_nodes(env, :plus_zero_right) == [],
           "plus_zero_right body must contain no {:rewrite, …} node after Phase B"
  end

  # (b) computed-endpoint rewrite: a miniature `frp01_par_assoc`. `appAssoc`'s
  # SCons branch rewrites along a proof whose endpoints are `app(…)` applications,
  # not variables — the sentinel that killed the naive attempt.
  @computed_src """
  mod RwCaseComputed
    type Sig = SigC | SigE
    type SList = SNil | SCons(Sig, SList)
    fn app(xs: SList, ys: SList) -> SList = match xs
      SNil() -> ys
      SCons(x, r) -> SCons(x, app(r, ys))
    fn appAssoc(xs: SList, ys: SList, zs: SList) -> Equivalent(SList, app(xs, app(ys, zs)), app(app(xs, ys), zs)) = match xs
      SNil() -> reflexive(app(ys, zs))
      SCons(x, r) -> rewrite appAssoc(r, ys, zs) in reflexive(SCons(x, app(app(r, ys), zs)))
  end
  """

  test "(b) a computed-endpoint rewrite accepts and emits no {:rewrite} node" do
    assert {:ok, env} = Program.elaborate(@computed_src)
    assert rewrite_nodes(env, :appAssoc) == [],
           "appAssoc body (computed endpoints) must contain no {:rewrite, …} node after Phase B"
  end
end
