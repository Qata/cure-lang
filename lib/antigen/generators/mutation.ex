defmodule Antigen.Generators.Mutation do
  @moduledoc """
  Ill-typed Core term generator (spec §5). Each operator builds a self-contained
  CHECKED scaffold — a minimal well-typed enclosing form wrapping exactly one
  construction-guaranteed-wrong subterm — so `Kernel.infer` rejects it at that
  enclosing check (never a bare wrong-headed term, which would infer fine). The
  well-typed filler parts are drawn from the lazy `Term.gen_term`, keeping mutants
  deep and realistic. StreamData-free: built only via `Antigen.Gen`.
  """
  alias Antigen.Gen
  alias Antigen.Generators.Term
  alias Cure.Core.Context

  @operators [:head_swap, :ctor_arg, :index_mismatch, :app_domain,
              :out_of_scope_var, :proj_non_pair, :universe]
  def operators, do: @operators

  # menu term helpers (kernel term literals; do not use SigMenu privates)
  defp z, do: {:ctor, :Z, []}
  defp s(n), do: {:ctor, :S, [n]}
  defp vnil, do: {:ctor, :vnil, []}
  defp nat_t, do: {:data, :Nat, [], []}
  defp vec(i), do: {:data, :Vec, [], [i]}

  # well-typed filler generators
  defp gnat(ctx), do: Term.gen_term(ctx, nat_t())
  defp gvec0(ctx), do: Term.gen_term(ctx, vec(z()))       # : Vec Z
  defp gvec_sz(ctx), do: Term.gen_term(ctx, vec(s(z())))  # : Vec (S Z)

  @doc "Build `{Gen.t(term), fault}` for `kind` in the local context `ctx`."
  @spec build(Context.t(), atom()) :: {Gen.t(), map()}
  def build(ctx, :head_swap) do
    g = Gen.bind(gvec0(ctx), fn v ->
          Gen.bind(gnat(ctx), fn n ->
            Gen.return({:app, {:app, {:global, :plus}, v}, n})  # plus expects Nat, given Vec
          end)
        end)
    {g, %{kind: :head_swap, witness: :head, expected_head: :Nat, injected_head: :Vec, scope: nil}}
  end

  def build(ctx, :ctor_arg) do
    g = Gen.bind(gnat(ctx), fn n ->
          Gen.bind(gvec0(ctx), fn v ->
            Gen.return({:ctor, :vcons, [n, v, vnil()]})  # x should be Nat, given Vec
          end)
        end)
    {g, %{kind: :ctor_arg, witness: :head, expected_head: :Nat, injected_head: :Vec, scope: nil}}
  end

  def build(ctx, :index_mismatch) do
    g = Gen.bind(gnat(ctx), fn n ->
          Gen.bind(gvec_sz(ctx), fn tail ->
            Gen.return({:ctor, :vcons, [z(), n, tail]})  # n=Z ⇒ tail must be Vec Z; given Vec (S Z)
          end)
        end)
    {g, %{kind: :index_mismatch, witness: :index, expected_head: :Z, injected_head: :S, scope: nil}}
  end

  def build(ctx, :app_domain) do
    g = Gen.bind(gvec0(ctx), fn v ->
          Gen.return({:app, {:lam, nat_t(), {:var, 0}}, v})  # (λx:Nat.x) applied to Vec
        end)
    {g, %{kind: :app_domain, witness: :head, expected_head: :Nat, injected_head: :Vec, scope: nil}}
  end

  def build(ctx, :out_of_scope_var) do
    gamma_len = Context.length(ctx)
    g = Gen.bind(Gen.int(0, 3), fn d -> Gen.return({:var, gamma_len + d}) end)  # always ≥ |Γ|
    # witness records the minimal certain out-of-scope index (d = 0).
    {g, %{kind: :out_of_scope_var, witness: :scope, expected_head: nil,
          injected_head: nil, scope: {gamma_len, gamma_len}}}
  end

  def build(_ctx, :proj_non_pair) do
    g = Gen.bind(Gen.int(0, 3), fn k -> Gen.return({:fst, nat_numeral(k)}) end)  # fst on a Nat
    {g, %{kind: :proj_non_pair, witness: :head, expected_head: :Sigma, injected_head: :Nat, scope: nil}}
  end

  def build(_ctx, :universe) do
    t0 = {:type, 0}
    g = Gen.return({:eq, t0, t0, t0})  # Type₀ : Type₁ ⋠ Type₀
    {g, %{kind: :universe, witness: :level, expected_head: {:type, 0},
          injected_head: {:type, 1}, scope: nil}}
  end

  defp nat_numeral(0), do: z()
  defp nat_numeral(k), do: s(nat_numeral(k - 1))
end
