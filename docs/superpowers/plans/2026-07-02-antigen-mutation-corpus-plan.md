# Antigen ill-typed mutation corpus — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a second-polarity soundness corpus to Antigen: generate construction-guaranteed ill-typed Core terms and an inverted "rejection" assay that banks any term the kernel *accepts* as an unsoundness antibody.

**Architecture:** A new `Antigen.Generators.Mutation` builds each mutant as a **self-contained checked scaffold** — a minimal well-typed enclosing eliminator/constructor (or standalone form) wrapping exactly one construction-guaranteed-wrong subterm, with the well-typed filler parts drawn from the existing lazy `Term.gen_term`. This realizes spec §5's "dispatch to a fault operator at a checked node": the scaffold's enclosing form **is** the §3(a) checked position that forces `Kernel.infer` to fail (verified below — all 7 operators reject under `infer`). A new `Antigen.Assays.Mutation` runs `infer` and inverts the verdict: `{:error, _}` = correct rejection = `:ok`; `{:ok, _}` = the kernel accepted an ill-typed term = `{:violation, …}`. Challenge kind `:mutant_term` reuses the existing `Corpus`/`Runner` banking untouched.

**Tech Stack:** Elixir; `Antigen.Gen` reified generator DSL (StreamData-free in generators/assays); `Cure.Core.Kernel` (`infer/2 :: {:ok, Value} | {:error, reason}`).

## Global Constraints

- **Construction-guaranteed ill-typedness (LOCKED):** every mutant's ill-typedness is decidable from the edit itself, never by consulting the kernel-under-test. No differential oracle.
- **StreamData quarantine:** nothing under `lib/antigen/generators/` or `lib/antigen/assays/` may reference `StreamData` (grep-enforced by `test/antigen/architecture_test.exs`). Build only via `Antigen.Gen`.
- **Ghost-authored commits:** `git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>"` with **no** `Co-Authored-By` trailer.
- **One full build/test run at any moment** — never launch concurrent suites (a past concurrent full-suite run caused a kernel panic).
- **Fueled nf:** any `Normalise.nf` call must pass `fuel:` (the mutation gate uses `infer` only, so this generally won't arise, but honor it if added).
- **Assay uses `infer`, so mutants must fail `infer`, not merely mismatch a goal.** Verified constructions (empty ctx, `SigMenu.env_of(:v1)`):

  | `fault.kind` | scaffold term | `Kernel.infer` result |
  |---|---|---|
  | `:head_swap` | `{:app, {:app, {:global,:plus}, VEC}, NAT}` | `{:error, {:foreign_ctor, :vnil}}` |
  | `:ctor_arg` | `{:ctor, :vcons, [NAT_n, VEC, VEC_xs]}` | `{:error, :index_mismatch}` |
  | `:index_mismatch` | `{:ctor, :vcons, [Z, NAT, VEC_SZ]}` (tail index `S Z` ≠ `Z`) | `{:error, :index_mismatch}` |
  | `:app_domain` | `{:app, {:lam, NatT, {:var,0}}, VEC}` | `{:error, {:foreign_ctor, :vnil}}` |
  | `:out_of_scope_var` | `{:var, k}` with `k ≥ length(Γ)` | `{:error, {:unbound_var, k}}` |
  | `:proj_non_pair` | `{:fst, NAT}` | `{:error, :not_a_sigma}` |
  | `:universe` | `{:eq, {:type,0}, {:type,0}, {:type,0}}` | `{:error, {:conversion_failure, {:type,1}, {:type,0}}}` |

  where `NAT`/`VEC`/`VEC_SZ` are well-typed filler terms (`Z = {:ctor,:Z,[]}`, `S(n) = {:ctor,:S,[n]}`, `vnil = {:ctor,:vnil,[]} : Vec Z`, `NatT = {:data,:Nat,[],[]}`). Note the raw kernel reasons **collapse** (`:index_mismatch` covers 3 kinds, `{:foreign_ctor,_}` covers 2) — this is exactly why the diversity metric (Task 7) buckets on `fault.kind`, not the raw reason.

- **`fault` schema** (rides in the `scaffold=` field via `term_to_binary`/`binary_to_term [:safe]`, so every atom in it must be interned in `Challenge.@known_atoms`):
  ```
  %{
    kind: :head_swap | :ctor_arg | :index_mismatch | :app_domain
        | :out_of_scope_var | :proj_non_pair | :universe,
    witness: :head | :index | :level | :scope,
    expected_head: atom | {:type, non_neg_integer} | nil,
    injected_head: atom | {:type, non_neg_integer} | nil,
    scope: {non_neg_integer, non_neg_integer} | nil   # {k, gamma_len} iff witness == :scope
  }
  ```
  Per-operator `fault` values (all kernel-independent witnesses):
  - `:head_swap` → `witness: :head, expected_head: :Nat, injected_head: :Vec`
  - `:ctor_arg` → `witness: :head, expected_head: :Nat, injected_head: :Vec`
  - `:index_mismatch` → `witness: :index, expected_head: :Z, injected_head: :S` (expected tail index ctor vs injected)
  - `:app_domain` → `witness: :head, expected_head: :Nat, injected_head: :Vec`
  - `:out_of_scope_var` → `witness: :scope, expected_head: nil, injected_head: nil, scope: {k, gamma_len}`
  - `:proj_non_pair` → `witness: :head, expected_head: :Sigma, injected_head: :Nat`
  - `:universe` → `witness: :level, expected_head: {:type, 0}, injected_head: {:type, 1}` (actual level 1 ⋠ required 0)

---

## File Structure

- **Create** `lib/antigen/generators/mutation.ex` — `Antigen.Generators.Mutation`: the 7 operators (each returns `{Gen.t(term), fault}`), `applicable/1`, weighted selection, `gen_mutant/2`, `mutant/1` (challenge), `assay_id/0`, `default_gen/0`.
- **Create** `lib/antigen/assays/mutation.ex` — `Antigen.Assays.Mutation`: `run/1`, with an overridable infer seam for the polarity test.
- **Modify** `lib/antigen/challenge.ex` — `:mutant_term` in `@type kind` + `@known_atoms` + `to_pieces/1` + `from_pieces/7`.
- **Modify** `lib/antigen/coverage.ex` — `terms_of/1` clause.
- **Modify** `lib/antigen/runner.ex` — assay registry, `mutation_metrics/1` + health line, `default_gen` wiring.
- **Modify** `lib/mix/tasks/antigen.ex` — `:mutant_term` branch in `default_gen`.
- **Modify** `test/antigen/corpus_replay_test.exs` — `mutation/rejection` in the replay `@registry`.
- **Modify** `test/antigen/seeds.sexp` — bank coverage-deduped `:mutant_term` seeds (Task 9).
- **Create** tests: `test/antigen/generators/mutation_test.exs`, `test/antigen/assays/mutation_test.exs`, `test/antigen/mutation_health_gate_test.exs`.

---

## Task 1: `:mutant_term` challenge kind — serialization round-trip

**Files:**
- Modify: `lib/antigen/challenge.ex:7` (`@type kind`), `:26` (`@known_atoms`), `:125-129` (add `to_pieces` clause after `:typed_term`), `:234-246` (add `from_pieces` clause).
- Test: `test/antigen/challenge_test.exs` (append; or create if absent).

**Interfaces:**
- Consumes: `Corpus.encode_scaffold/1`, `Corpus.decode_scaffold/1`.
- Produces: `Challenge` with `kind: :mutant_term`, `payload: %{sig, ctx, type, term, fault}`; `to_pieces/from_pieces` round-trip.

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/challenge_test.exs
defmodule Antigen.ChallengeTest do
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Corpus}

  test ":mutant_term round-trips through to_pieces/from_pieces incl the fault map" do
    fault = %{kind: :proj_non_pair, witness: :head, expected_head: :Sigma,
              injected_head: :Nat, scope: nil}
    c = Challenge.new(
      kind: :mutant_term, assay: "mutation/rejection", label: :ill_typed,
      payload: %{sig: :v1, ctx: [{:data, :Nat, [], []}],
                 type: {:data, :Nat, [], []},
                 term: {:fst, {:ctor, :Z, []}}, fault: fault}
    )

    {scaffold, pieces} = Challenge.to_pieces(c)
    # simulate the corpus scaffold codec (term_to_binary → binary_to_term [:safe])
    scaffold2 = Corpus.decode_scaffold(Corpus.encode_scaffold(scaffold))
    c2 = Challenge.from_pieces(:mutant_term, c.assay, c.label, nil, nil, scaffold2, pieces)

    assert c2.kind == :mutant_term
    assert c2.payload.fault == fault
    assert c2.payload.term == c.payload.term
    assert c2.payload.ctx == c.payload.ctx
    assert c2.payload.type == c.payload.type
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/antigen/challenge_test.exs`
Expected: FAIL — `to_pieces`/`from_pieces` have no `:mutant_term` clause (FunctionClauseError), or `:mutant_term` not a valid kind.

- [ ] **Step 3: Write minimal implementation**

In `lib/antigen/challenge.ex`, extend `@type kind` (line 7) to add `| :mutant_term`.

Extend `@known_atoms` (line 26 list) — add these (verified against the codebase: `:ill_typed` already present; `:fst/:snd/:pair/:sigma` already interned by `Cure.Core.Serialize`; `:Nat/:Vec/:Bd` already present via `:typed_term`):
```elixir
    :mutant_term, :ill_typed,
    :head_swap, :ctor_arg, :index_mismatch, :app_domain,
    :out_of_scope_var, :proj_non_pair, :universe,
    :head, :index, :level, :scope, :Sigma, :Z, :S
```
(`:ill_typed` is a no-op if already listed — keep the list a set; do not duplicate. `:Z`/`:S` are the index-witness heads for `:index_mismatch`.)

Add `to_pieces` clause (after the `:typed_term` clause, ~line 130):
```elixir
  def to_pieces(%__MODULE__{kind: :mutant_term, payload: p}) do
    %{sig: sig, ctx: ctx, type: type, term: term, fault: fault} = p
    ctx_pieces = ctx |> Enum.with_index() |> Enum.map(fn {t, i} -> {"ctx#{i}", t} end)
    scaffold = %{"sig" => Atom.to_string(sig), "ctx_len" => length(ctx), "fault" => fault}
    {scaffold, ctx_pieces ++ [{"type", type}, {"term", term}]}
  end
```

Add `from_pieces` clause (after the `:typed_term` clause, ~line 247):
```elixir
  def from_pieces(:mutant_term, assay, label, seed, note, scaffold, pieces) do
    pmap = Map.new(pieces)
    len = scaffold["ctx_len"]
    ctx = for i <- (if len == 0, do: [], else: 0..(len - 1)), do: pmap["ctx#{i}"]
    payload = %{
      sig: String.to_existing_atom(scaffold["sig"]),
      ctx: ctx,
      type: pmap["type"],
      term: pmap["term"],
      fault: scaffold["fault"]
    }
    new(kind: :mutant_term, assay: assay, label: label, payload: payload, seed: seed, note: note)
  end
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/antigen/challenge_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/challenge.ex test/antigen/challenge_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): :mutant_term challenge kind — serialization + fault provenance"
```

---

## Task 2: `Coverage.terms_of` for `:mutant_term`

**Files:**
- Modify: `lib/antigen/coverage.ex:27` (add clause mirroring `:typed_term`).
- Test: `test/antigen/coverage_test.exs` (append).

**Interfaces:**
- Produces: `terms_of(%Challenge{kind: :mutant_term})` → `[type, term | ctx]`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/coverage_test.exs  (append inside the existing module, or create)
  test "terms_of extracts type, term and ctx for :mutant_term" do
    c = Antigen.Challenge.new(
      kind: :mutant_term, assay: "mutation/rejection", label: :ill_typed,
      payload: %{sig: :v1, ctx: [{:data, :Nat, [], []}],
                 type: {:data, :Nat, [], []}, term: {:fst, {:ctor, :Z, []}},
                 fault: %{kind: :proj_non_pair, witness: :head,
                          expected_head: :Sigma, injected_head: :Nat, scope: nil}}
    )
    ts = Antigen.Coverage.terms_of(c)
    assert {:fst, {:ctor, :Z, []}} in ts
    assert {:data, :Nat, [], []} in ts
  end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/antigen/coverage_test.exs`
Expected: FAIL — no `:mutant_term` clause (FunctionClauseError).

- [ ] **Step 3: Write minimal implementation**

In `lib/antigen/coverage.ex`, after the `:typed_term` clause (line 27):
```elixir
  def terms_of(%Challenge{kind: :mutant_term, payload: %{ctx: ctx, type: type, term: term}}),
    do: [type, term | ctx]
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/antigen/coverage_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/coverage.ex test/antigen/coverage_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): coverage keying for :mutant_term"
```

---

## Task 3: The 7 fault operators + construction-guarantee test

**Files:**
- Create: `lib/antigen/generators/mutation.ex`.
- Test: `test/antigen/generators/mutation_test.exs`.

**Interfaces:**
- Produces: `Antigen.Generators.Mutation.operators/0 :: [atom]` (the 7 kinds); `build/2 :: (ctx, kind) -> {Gen.t(term), fault}` — each returns a `Gen` of the scaffold term plus its `fault` record. Uses `Antigen.Generators.Term.gen_term/2` for well-typed filler and `Antigen.Generators.SigMenu` for the env; builds menu terms via local private helpers.
- Consumes (Task 4/7): `operators/0`, `build/2`.

**Reference — menu term helpers** (define as module privates in `mutation.ex`; do not depend on `SigMenu` privates):
```elixir
  defp z, do: {:ctor, :Z, []}
  defp s(n), do: {:ctor, :S, [n]}
  defp vnil, do: {:ctor, :vnil, []}          # : Vec Z
  defp nat_t, do: {:data, :Nat, [], []}
  defp vec(i), do: {:data, :Vec, [], [i]}
```

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/generators/mutation_test.exs
defmodule Antigen.Generators.MutationTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.{Mutation, SigMenu}
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.{Context, Kernel}

  defp sample(gen, n), do: B.interp(gen) |> Enum.take(n)

  test "every operator produces a term the kernel REJECTS under infer (construction guarantee)" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)

    for kind <- Mutation.operators() do
      {gen, fault} = Mutation.build(ctx, kind)
      assert fault.kind == kind
      for term <- sample(gen, 20) do
        assert {:error, _} = Kernel.infer(ctx, term),
               "operator #{kind} produced an infer-ACCEPTED term: #{inspect(term)}"
      end
    end
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/antigen/generators/mutation_test.exs`
Expected: FAIL — `Antigen.Generators.Mutation` does not exist (CompileError / UndefinedFunctionError).

- [ ] **Step 3: Write minimal implementation**

```elixir
# lib/antigen/generators/mutation.ex
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
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/antigen/generators/mutation_test.exs`
Expected: PASS (all 7 operators reject under `infer`).

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/generators/mutation.ex test/antigen/generators/mutation_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): 7 construction-guaranteed ill-typed fault operators"
```

---

## Task 4: Invariant-(b) meta-test (kernel-independent witness)

**Files:**
- Test: `test/antigen/generators/mutation_test.exs` (append).

**Interfaces:**
- Consumes: `Mutation.operators/0`, `Mutation.build/2`. No production code — this task proves the `fault` provenance is a *warrant* for ill-typedness computed WITHOUT the kernel. If it fails, the fix is in the Task 3 `fault` records, not here.

- [ ] **Step 1: Write the failing test**

```elixir
  test "each operator's fault carries a kernel-INDEPENDENT witness of ill-typedness" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)

    for kind <- Mutation.operators() do
      {_gen, f} = Mutation.build(ctx, kind)

      case f.witness do
        :head ->
          assert f.expected_head != f.injected_head,
                 "#{kind}: heads must differ (#{inspect(f.expected_head)} vs #{inspect(f.injected_head)})"
        :index ->
          # distinct closed index constructors ⇒ non-convertible, decided syntactically
          assert f.expected_head != f.injected_head
        :level ->
          {:type, req} = f.expected_head
          {:type, act} = f.injected_head
          assert act > req, "#{kind}: injected level must exceed required (predicativity)"
        :scope ->
          {k, gamma_len} = f.scope
          assert k >= gamma_len, "#{kind}: var index must be out of scope"
      end
    end
  end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/antigen/generators/mutation_test.exs --only nothing` then the full file.
Expected before Task-3 records are correct: FAIL. With Task 3 complete it should already PASS — so to see red, temporarily assert the *opposite* is NOT the point. Instead: this test is a **guard**; verify it fails if a `fault` witness is wrong by running: transiently edit `:universe`'s `injected_head` to `{:type, 0}` and confirm FAIL, then revert.

Run: `mix test test/antigen/generators/mutation_test.exs -n` (all). Expected: FAIL on the mutated record, PASS after revert.

- [ ] **Step 3: (no new impl)** — Task 3's `fault` records already satisfy the invariant. If the transient-edit red step above did not fail, the witness logic is too weak; strengthen it before proceeding.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/antigen/generators/mutation_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add test/antigen/generators/mutation_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(antigen): kernel-independent invariant-(b) witness meta-test"
```

---

## Task 5: `gen_mutant` + `mutant/1` challenge + `default_gen`

**Files:**
- Modify: `lib/antigen/generators/mutation.ex` (add `gen_mutant/1`, `mutant/1`, `assay_id/0`, `default_gen/0`, weighted `select/1`).
- Test: `test/antigen/generators/mutation_test.exs` (append).

**Interfaces:**
- Consumes: `Antigen.Generators.Context.gen/1` (context telescope), `SigMenu.env_of/1`, `SigMenu.rebuild_context/2`, `Challenge.new/1`.
- Produces: `mutant/0 :: Gen.t(Challenge)` (`kind: :mutant_term`, `assay: "mutation/rejection"`, `label: :ill_typed`); `assay_id/0 :: "mutation/rejection"`; `default_gen/0 :: Gen.t(Challenge)` (== `mutant/0`, single assay).

- [ ] **Step 1: Write the failing test**

```elixir
  test "mutant/0 emits a well-formed :mutant_term challenge that the kernel rejects" do
    alias Antigen.Challenge
    for c <- sample(Mutation.mutant(), 60) do
      assert %Challenge{kind: :mutant_term, assay: "mutation/rejection", label: :ill_typed, payload: p} = c
      assert p.sig == :v1
      assert p.fault.kind in Mutation.operators()
      env = SigMenu.env_of(:v1)
      ctx = SigMenu.rebuild_context(env, p.ctx)
      assert {:error, _} = Kernel.infer(ctx, p.term)   # generation totality + rejection
    end
  end

  test "a large sample draws at least 5 distinct fault kinds (diversity is reachable)" do
    kinds = sample(Mutation.mutant(), 200) |> Enum.map(& &1.payload.fault.kind) |> Enum.uniq()
    assert length(kinds) >= 5
  end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/antigen/generators/mutation_test.exs`
Expected: FAIL — `Mutation.mutant/0` undefined.

- [ ] **Step 3: Write minimal implementation**

Add to `lib/antigen/generators/mutation.ex`:
```elixir
  alias Antigen.Challenge
  alias Antigen.Generators.{Context, SigMenu}

  def assay_id, do: "mutation/rejection"

  @doc "A `Gen` of a `:mutant_term` challenge."
  @spec mutant() :: Gen.t()
  def mutant do
    env = SigMenu.env_of(:v1)

    Gen.bind(Context.gen(env), fn ctx_types ->
      ctx = SigMenu.rebuild_context(env, ctx_types)

      Gen.bind(select(), fn kind ->
        {term_gen, fault} = build(ctx, kind)

        Gen.bind(term_gen, fn term ->
          Gen.return(
            Challenge.new(
              kind: :mutant_term,
              assay: assay_id(),
              label: :ill_typed,
              payload: %{sig: :v1, ctx: ctx_types, type: goal_of(fault), term: term, fault: fault}
            )
          )
        end)
      end)
    end)
  end

  @spec default_gen() :: Gen.t()
  def default_gen, do: mutant()

  # Uniform weighted choice over all 7 operators (each is self-contained, so all
  # are applicable at every draw — spec §5's "applicable set" is the full set once
  # operators own their checked scaffolds). Equal weights keep the diversity floor
  # (Task 7) comfortably reachable.
  defp select, do: Gen.frequency(Enum.map(@operators, fn k -> {1, Gen.return(k)} end))

  # The challenge-level `type` field is documentation-only (spec §4/§6.1): a
  # nominal goal describing the fault site, never a proven property of the mutant.
  defp goal_of(%{kind: :universe}), do: {:type, 0}
  defp goal_of(%{expected_head: :Nat}), do: nat_t()
  defp goal_of(%{expected_head: :Sigma}), do: {:sigma, nat_t(), nat_t()}
  defp goal_of(%{kind: :index_mismatch}), do: vec(z())
  defp goal_of(_), do: nat_t()
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/antigen/generators/mutation_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/generators/mutation.ex test/antigen/generators/mutation_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): gen_mutant + :mutant_term challenge emission"
```

---

## Task 6: `Antigen.Assays.Mutation` — inverted rejection assay

**Files:**
- Create: `lib/antigen/assays/mutation.ex`.
- Test: `test/antigen/assays/mutation_test.exs`.

**Interfaces:**
- Produces: `Antigen.Assays.Mutation.run/1 :: (Challenge) -> :ok | {:violation, {:accepted_ill_typed, term, fault}}`. Includes an overridable infer seam (`run/2` with an `infer_fun` default) for the polarity test — the default is `&Cure.Core.Kernel.infer/2`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/assays/mutation_test.exs
defmodule Antigen.Assays.MutationTest do
  use ExUnit.Case, async: true
  alias Antigen.Assays.Mutation, as: MA
  alias Antigen.Generators.{Mutation, SigMenu}
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.Context

  defp sample(gen, n), do: B.interp(gen) |> Enum.take(n)

  test "run/1 returns :ok when the kernel correctly rejects the mutant" do
    for c <- sample(Mutation.mutant(), 40), do: assert MA.run(c) == :ok
  end

  test "run/2 flags a violation when the (stubbed) kernel ACCEPTS an ill-typed term" do
    [c | _] = sample(Mutation.mutant(), 1)
    accept = fn _ctx, _term -> {:ok, {:vtype, 0}} end
    assert {:violation, {:accepted_ill_typed, term, fault}} = MA.run(c, accept)
    assert term == c.payload.term
    assert fault == c.payload.fault
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/antigen/assays/mutation_test.exs`
Expected: FAIL — `Antigen.Assays.Mutation` undefined.

- [ ] **Step 3: Write minimal implementation**

```elixir
# lib/antigen/assays/mutation.ex
defmodule Antigen.Assays.Mutation do
  @moduledoc """
  The inverted "rejection" assay (spec §6.1). An ill-typed `:mutant_term` MUST be
  rejected by `Kernel.infer`; a correct rejection (`{:error, _}`) passes (`:ok`),
  and acceptance (`{:ok, _}`) is an unsoundness antibody. Uses `infer` (needs no
  expected type) — its `{:error, _}` is the unambiguous "rejected" signal.
  """
  alias Antigen.Challenge
  alias Antigen.Generators.SigMenu
  alias Cure.Core.Kernel

  @spec run(Challenge.t()) :: :ok | {:violation, tuple()}
  def run(challenge), do: run(challenge, &Kernel.infer/2)

  @doc "Same as `run/1` but with an injectable infer function (test seam)."
  def run(%Challenge{kind: :mutant_term, payload: p}, infer_fun) do
    env = SigMenu.env_of(p.sig)
    ctx = SigMenu.rebuild_context(env, p.ctx)

    case infer_fun.(ctx, p.term) do
      {:error, _reason} -> :ok
      {:ok, _ty} -> {:violation, {:accepted_ill_typed, p.term, p.fault}}
    end
  end
end
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/antigen/assays/mutation_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/assays/mutation.ex test/antigen/assays/mutation_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): inverted mutation/rejection assay"
```

---

## Task 7: Runner integration — registry, diversity gate, health line

**Files:**
- Modify: `lib/antigen/runner.ex` — add registry clause; add `mutation_metrics/1`, `mutation_stamp/1`; print the health line in `explore/1`; add the assay to `assay_module/1`.
- Test: `test/antigen/mutation_health_gate_test.exs`.

**Interfaces:**
- Consumes: `Mutation.mutant/0`, `Mutation.operators/0`, `Assays.Mutation`.
- Produces: `Runner.assay_module_for("mutation/rejection") == Antigen.Assays.Mutation`; `Runner.mutation_metrics(challenges) :: %{reason_diversity: n, survivors: n, mutants_total: n}`; `Runner.mutation_stamp(metrics) :: :healthy | :vacuous`.

**Reference:** the existing `assay_module/1` registry is at `runner.ex:~185`; `health_metrics/1` (the `:typed_term` gate) filters `match?(%Challenge{kind: :typed_term}, _)` — the new metric filters `:mutant_term` analogously, so the two never mix (spec §4 kind-isolation).

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/mutation_health_gate_test.exs
defmodule Antigen.MutationHealthGateTest do
  use ExUnit.Case, async: true
  alias Antigen.{Runner, Generators.Mutation}
  alias Antigen.Backend.StreamData, as: B

  defp sample(gen, n), do: B.interp(gen) |> Enum.take(n)

  test "registry maps mutation/rejection to the mutation assay" do
    assert Runner.assay_module_for("mutation/rejection") == Antigen.Assays.Mutation
  end

  test "mutation_metrics reports diversity ≥ 5, 0 survivors, and stamps healthy" do
    cs = sample(Mutation.mutant(), 200)
    m = Runner.mutation_metrics(cs)
    assert m.mutants_total == 200
    assert m.survivors == 0
    assert m.reason_diversity >= 5
    assert Runner.mutation_stamp(m) == :healthy
  end

  test ":mutant_term challenges are excluded from the :typed_term health gate" do
    cs = sample(Mutation.mutant(), 30)
    # health_metrics filters :typed_term only ⇒ no mutant terms counted
    hm = Runner.health_metrics(cs)
    assert hm.binder_usage == 1.0   # safe_ratio(0,0) ⇒ 1.0 (empty :typed_term subset)
    assert hm.reduction_activity == 1.0
    assert hm.fuel_exhausted_count == 0
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/antigen/mutation_health_gate_test.exs`
Expected: FAIL — `assay_module_for("mutation/rejection")` raises/no clause; `mutation_metrics/1` undefined.

- [ ] **Step 3: Write minimal implementation**

In `lib/antigen/runner.ex`:

Registry (add beside the other `defp assay_module` clauses):
```elixir
  defp assay_module("mutation/rejection"), do: Antigen.Assays.Mutation
```

Metrics + stamp (add near `health_metrics/1`):
```elixir
  @mutation_diversity_floor 5

  @doc "Vacuity metrics over the :mutant_term subset (spec §6.2): fault-kind diversity."
  def mutation_metrics(challenges) do
    ms = Enum.filter(challenges, &match?(%Challenge{kind: :mutant_term}, &1))

    {rejected_kinds, survivors} =
      Enum.reduce(ms, {MapSet.new(), 0}, fn c, {kinds, surv} ->
        case Antigen.Assays.Mutation.run(c) do
          :ok -> {MapSet.put(kinds, c.payload.fault.kind), surv}
          {:violation, _} -> {kinds, surv + 1}
        end
      end)

    %{reason_diversity: MapSet.size(rejected_kinds), survivors: survivors, mutants_total: length(ms)}
  end

  @doc "Vacuity stamp (spec §6.2): diversity-only; survivors are surfaced separately."
  def mutation_stamp(%{reason_diversity: d}),
    do: if(d >= @mutation_diversity_floor, do: :healthy, else: :vacuous)
```

Health line — in `explore/1`, after the existing `antigen health[typed_term]:` IO.puts, add (guard on there being mutant challenges so pure-typed_term runs are unaffected):
```elixir
    mm = mutation_metrics(challenges)
    if mm.mutants_total > 0 do
      IO.puts(
        "antigen health[mutant_term]: reason_diversity=#{mm.reason_diversity} " <>
          "survivors=#{mm.survivors} → #{mutation_stamp(mm)}"
      )
    end
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/antigen/mutation_health_gate_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/runner.ex test/antigen/mutation_health_gate_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): mutation/rejection registry + diversity vacuity gate"
```

---

## Task 8: Wire `:mutant_term` into `mix antigen` default_gen

**Files:**
- Modify: `lib/mix/tasks/antigen.ex` (the `default_gen/0` that composes the Tier-A/B generators).
- Test: `test/antigen/mix_task_test.exs` (append).

**Interfaces:**
- Consumes: `Antigen.Generators.Mutation.mutant/0`.
- Produces: the wired-in `default_gen` draws `:mutant_term` challenges.

- [ ] **Step 1: Write the failing test**

```elixir
  test "the wired-in default_gen draws :mutant_term challenges" do
    gen = Mix.Tasks.Antigen.default_gen()
    kinds = Antigen.Backend.StreamData.interp(gen) |> Enum.take(300) |> Enum.map(& &1.kind) |> Enum.uniq()
    assert :mutant_term in kinds
  end
```
(Add `alias Antigen.Generators.Mutation` / ensure `Mix.Tasks.Antigen.default_gen/0` is public — it is used already by the existing Tier-B test.)

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/antigen/mix_task_test.exs`
Expected: FAIL — no `:mutant_term` in the drawn kinds.

- [ ] **Step 3: Write minimal implementation**

In `lib/mix/tasks/antigen.ex` `default_gen/0`, add a branch to the `Gen.frequency` list:
```elixir
      {1, Antigen.Generators.Mutation.mutant()},
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/antigen/mix_task_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/mix/tasks/antigen.ex test/antigen/mix_task_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): wire :mutant_term into mix antigen default_gen"
```

---

## Task 9: Replay registry + bank `:mutant_term` seeds

**Files:**
- Modify: `test/antigen/corpus_replay_test.exs` (add `mutation/rejection` to the `@registry` map).
- Modify: `test/antigen/seeds.sexp` (bank coverage-deduped `:mutant_term` seeds).

**Interfaces:**
- Consumes: `Antigen.Assays.Mutation`, `Mutation.mutant/0`.
- Produces: banked `:mutant_term` seeds replay to `:ok` (correct rejection), no `{:unknown_assay, _}`.

**Reference:** this is the exact gap that bit Tier-B Task 10 — banked seeds carry an assay id the replay `@registry` map must know, separately from `Runner`'s registry.

- [ ] **Step 1: Write the failing test**

```elixir
# in test/antigen/corpus_replay_test.exs — add to the assertions that every banked
# seed replays without :unknown_assay. First add the registry entry, then verify.
  test "banked :mutant_term seeds replay as correct rejections" do
    seeds = Antigen.Corpus.stream("test/antigen/seeds.sexp") |> Enum.map(fn {:ok, c} -> c end)
    mutants = Enum.filter(seeds, &(&1.kind == :mutant_term))
    assert mutants != [], "no :mutant_term seeds banked yet"
    for c <- mutants, do: assert Antigen.Assays.Mutation.run(c) == :ok
  end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/antigen/corpus_replay_test.exs`
Expected: FAIL — no `:mutant_term` seeds in `seeds.sexp` (empty list assertion), and/or `mutation/rejection` missing from the replay `@registry`.

- [ ] **Step 3: Write minimal implementation**

Add to `corpus_replay_test.exs` `@registry` map:
```elixir
    "mutation/rejection" => Antigen.Assays.Mutation,
```

Bank seeds by running the explorer against a temp corpus, then copy the coverage-deduped `:mutant_term` seeds into `test/antigen/seeds.sexp`:
```bash
MIX_ENV=test mix antigen --count 300 --seeds /tmp/mut_seeds.sexp --corpus /tmp/mut_corpus.sexp
# then append the :mutant_term lines from /tmp/mut_seeds.sexp into test/antigen/seeds.sexp
```
(De-dup is by `Corpus.dedup_key(_, :seed)`; the append is idempotent. Bank ~one seed per distinct fault kind — aim for ≥5 to keep the static diversity meta-test green.)

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/antigen/corpus_replay_test.exs`
Expected: PASS. Also confirm the full replay test (every seed → known assay) stays green.

- [ ] **Step 5: Commit**

```bash
git add test/antigen/corpus_replay_test.exs test/antigen/seeds.sexp
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(antigen): replay registry + banked :mutant_term seeds"
```

---

## Task 10: Acceptance — full suite + explore run

**Files:** none (verification only).

- [ ] **Step 1: Architecture quarantine** — `mix test test/antigen/architecture_test.exs` (confirm `mutation.ex`/`assays/mutation.ex` are StreamData-free). Expected: PASS.
- [ ] **Step 2: Full suite (ONCE, no concurrency)** — `mix test`. Expected: all green (prior 2270 + new tests).
- [ ] **Step 3: Acceptance explore** — `MIX_ENV=test mix antigen --count 500`. Expected: an `antigen health[mutant_term]: reason_diversity=… survivors=0 → healthy` line with `reason_diversity ≥ 5`, and **0 infections** (correct kernel rejects all mutants). Record the exact line for the Stage-5 report.
- [ ] **Step 4:** No commit (verification task). If Step 3 shows any `survivors > 0`, that is a *genuine* finding — STOP and report it (a real unsoundness antibody), do not silence it.

---

## Self-Review

**Spec coverage:** §1 motivation → the inverted assay (Task 6). §2 scope → v1 menu reused (Tasks 3/5). §3 correctness invariant → construction-guarantee test (Task 3) + kernel-independent witness meta-test (Task 4). §4 challenge model → Task 1 (kind/serialization) + Task 2 (coverage) + Task 7 (kind-isolation). §5 fault operators → Task 3 (all 7, verified constructions). §6.1 assay → Task 6. §6.2 diversity gate → Task 7. §7 tests → Tasks 1–9 map to the seven test families. §8 architecture/atoms → Tasks 1, 3, 6, 7, 8. §9 relationship → out of scope (documented as follow-on), no task.

**Placeholder scan:** every code step contains complete, verified code (constructions probed against the real kernel). Task 9's seed-banking is a shell procedure, not a code placeholder.

**Type consistency:** `build/2` returns `{Gen.t, fault}` (Tasks 3→5); `mutant/0` returns `Gen.t(Challenge)` (Tasks 5→7→8); `run/1|2` returns `:ok | {:violation, {:accepted_ill_typed, term, fault}}` (Tasks 6→7); `mutation_metrics/1` shape `%{reason_diversity, survivors, mutants_total}` (Task 7 producer + test). `fault` schema is identical across Tasks 1, 3, 4, 6, 7.

**Note on spec §5 applicability:** the plan flattens §5's site-restricted "applicable set" to "all 7 operators applicable at every draw," because each operator owns its checked scaffold rather than injecting into a drawn `gen_term` node. This preserves every spec *guarantee* (construction-guaranteed ill-typedness, §3(a) checked position via the operator's enclosing form, `fault.kind` diversity) while being less invasive than threading an injection hook through the lazy `gen_term`. The `type` field's site-nominal `goal_of/1` keeps §4's documentation-only contract. Flagged here for the plan reviewer.
