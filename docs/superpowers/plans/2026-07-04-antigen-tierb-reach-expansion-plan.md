# Antigen Tier-B Reach Expansion — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Widen the dependent-term generator's reach (Π/Σ goal seeds + a parametric `List(A)` family), add a `term/erasure_preservation` assay, and add ill-typed mutation operators for the new type formers.

**Architecture:** Three sequential phases, each independently committed. Phase 1 enriches `SigMenu`'s menu (the stream Phases 2–3 consume). Phase 2 marks one arg `:erased` (so erasure isn't the identity) then adds an assay checking `nf(erase t) ≡ erase(nf t)`. Phase 3 adds mutation operators. All work is in `Antigen.*` + the menu; **no kernel/TCB edits**.

**Tech Stack:** Elixir/ExUnit, the reified `Antigen.Gen` DSL, `Cure.Core.{Inductive,Kernel,Normalise,Eval,Conv}`, `Cure.Elab.Erase` (read-only through op-maps).

## Global Constraints

- **`MIX_ENV=test`**, run from worktree root `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/antigen-tier-b`. **One build/test run at a time.**
- **No edits to `Cure.*`** — reached read-only through op-maps. No `:meck`, no new dependency.
- **Ghost-authored commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NEVER a `Co-Authored-By` trailer.
- **StreamData quarantine:** nothing under `Antigen.Generators.*`/`Antigen.Assays.*` may contain the literal `StreamData` token. New generator code uses `Antigen.Gen`.
- **Assays return only `:ok | {:violation, term()}`** (fuel exhaustion is its own tagged violation, never conflated with a mismatch).
- **Full existing suite green each phase** (2732 baseline); every new assay/operator ships a negative control that demonstrably infects.
- **Menu changes are additive to `:v1`** (spec §8-5) — never remove/reshape an existing family/ctor/def, so banked `:v1` seeds replay unchanged.
- **Tests immutable once written** (strict TDD): pass by editing implementation, never by weakening a test.
- Stay on `autopilot/antigen-tier-b`.

## File structure

- `lib/antigen/generators/sig_menu.ex` — `List(A)` family, Π/Σ/List goal seeds, `canon`/`inhabitable?` clauses, `vcons` `:erased` mark.
- `lib/antigen/generators/term.ex` — `intro_rules` clause for `:List`, `@assay_ids` +1.
- `lib/antigen/assays/term.ex` — `term/erasure_preservation` dispatch clause + helpers.
- `lib/antigen/generators/mutation.ex` — `:pair_component`, `:lam_body_type`, `:app_result`, `:type_param_mismatch` operators.
- `lib/antigen/runner.ex` — `assay_module("term/erasure_preservation")` clause.
- `lib/antigen/challenge.ex` — `@known_atoms`: `:List`, `:Nil`, `:Cons`, `:A`, new mutation op atoms.
- Tests: `test/antigen/generators/sig_menu_test.exs` (or existing), `test/antigen/assays/erasure_preservation_test.exs`, `test/antigen/generators/mutation_test.exs`.

---

## PHASE 1 — Richer generator menu

### Task 1: `List(A)` parametric family + atoms

**Files:** `lib/antigen/generators/sig_menu.ex`, `lib/antigen/challenge.ex`, test.

- [ ] **Step 1: Verify the param-family declaration convention.** `List` is the FIRST
  param-bearing family in `SigMenu` (Vec uses an *index*, `params: []`). Before declaring it,
  read `lib/cure/core/inductive.ex` (`family/4`, `ctor/3,4`, `param_count/2`,
  `ctor_quantities/2`) and grep the codebase for any existing param-bearing family
  (`grep -rn "Inductive.family([^,]*, \[{" lib/ test/`) to confirm how a ctor's telescope
  references the family parameter in de Bruijn (the param is an outer binder in scope over
  the ctor telescope). Record the confirmed convention as a comment. Do NOT guess.

- [ ] **Step 2: Write the failing test** — `test/antigen/generators/sig_menu_test.exs` (create if absent):

```elixir
defmodule Antigen.Generators.SigMenuTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.SigMenu
  alias Cure.Core.{Context, Inductive}

  test "env_of(:v1) registers the List(A) family with Nil/Cons" do
    env = SigMenu.env_of(:v1)
    assert Inductive.param_count(env, :List) == 1
    assert Inductive.ctor_quantities(env, :Nil) != nil
    assert Inductive.ctor_quantities(env, :Cons) != nil
  end

  test "List(Nat) is inhabitable and canon gives Nil" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    list_nat = {:data, :List, [SigMenu.nat()], []}
    assert SigMenu.inhabitable?(ctx, list_nat)
    assert SigMenu.canon(ctx, list_nat) == {:ctor, :Nil, []}
  end
end
```

- [ ] **Step 3: Run to verify RED.** `MIX_ENV=test mix test test/antigen/generators/sig_menu_test.exs` → FAIL (`:List` unregistered; `inhabitable?`/`canon` have no `:List` clause).

- [ ] **Step 4: Declare the family** in `env_of(:v1)` (append to the `|> Inductive.declare(...)` chain, using the convention confirmed in Step 1 — the candidate below assumes the family param is de Bruijn `{:var,0}` in the ctor telescope; correct it if Step 1 shows otherwise):

```elixir
      |> Inductive.declare(Inductive.family(:List, [{:A, {:type, 0}}], [], 0),
        [
          Inductive.ctor(:Nil, [], []),
          # Cons : (A) => A -> List(A) -> List(A); family param A is the outer
          # binder, so inside the telescope A is {:var, 0} at the head, shifting
          # as telescope binders are added (confirm indices per Step 1).
          Inductive.ctor(:Cons, [{:hd, {:var, 0}}, {:tl, {:data, :List, [{:var, 1}], []}}], [])
        ])
```

- [ ] **Step 5: Add `canon`/`inhabitable?` clauses** for `:List` (mirror the Vec structure at sig_menu.ex:80-104):

```elixir
  # in inhabitable?/2, before the catch-all `_ -> false`:
      {:data, :List, [a], _} -> inhabitable?(ctx, a)
  # in canon/2:
      {:data, :List, [_a], _} -> {:ctor, :Nil, []}
```

- [ ] **Step 6: Intern atoms** in `lib/antigen/challenge.ex` `@known_atoms` (append):

```elixir
    # Tier-B reach expansion: List parametric family + param binder name
    :List, :Nil, :Cons, :A
```

- [ ] **Step 7: Run to verify GREEN.** `MIX_ENV=test mix test test/antigen/generators/sig_menu_test.exs` → PASS (2).

- [ ] **Step 8: Commit** — `feat(antigen): add List(A) parametric family to the Tier-B menu`

### Task 2: `List` introduction rule + goal seeds

**Files:** `lib/antigen/generators/term.ex`, `lib/antigen/generators/sig_menu.ex`, test.

- [ ] **Step 1: Write the failing test** (append to `sig_menu_test.exs`):

```elixir
  test "gen_term over List(Nat) produces a List constructor" do
    alias Antigen.Generators.Term
    alias Antigen.Backend.StreamData, as: SD
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    gen = Term.gen_term(ctx, {:data, :List, [SigMenu.nat()], []})
    terms = SD.sample(SD.interp(gen), 20)
    assert Enum.all?(terms, fn t -> match?({:ctor, :Nil, []}, t) or match?({:ctor, :Cons, _}, t) end)
    # at least one Cons (non-vacuous) across the sample at reasonable size
  end
```

> Note: this test lives in a `test/` file, so referencing `Antigen.Backend.StreamData` is
> allowed (the quarantine covers only `lib/antigen/{generators,assays}`). Confirm the sample
> helper signature against `backend/stream_data.ex` (`sample(native, count)`); adjust if the
> generator must be `interp`'d then sampled differently.

- [ ] **Step 2: Run to verify RED** — `gen_term` over `List(Nat)` currently hits `intro_rules`' `_other -> []` catch-all and falls back to `canon` (only `Nil`), never `Cons`; or the size-driven path errors. Confirm the failure.

- [ ] **Step 3: Add the `intro_rules` clause** in `term.ex` (before the `_other` catch-all at term.ex:147), mirroring `ctor_rules_for_vec`:

```elixir
  defp intro_rules(ctx, _goal, {:data, :List, [a], _}, size) do
    nil_rule = {2, Gen.return({:ctor, :Nil, []})}

    cons_rules =
      if SigMenu.inhabitable?(ctx, a) do
        [{2,
          Gen.bind(gen(ctx, a, size - 1), fn hd ->
            Gen.bind(gen(ctx, {:data, :List, [a], []}, size - 1), fn tl ->
              Gen.return({:ctor, :Cons, [hd, tl]})
            end)
          end)}]
      else
        []
      end

    [nil_rule | cons_rules]
  end
```

- [ ] **Step 4: Add List goal seeds** in `sig_menu.ex` `goal_types/0`:

```elixir
  def goal_types, do: [nat(), bd(), vec(z()), vec(s(z())),
                       {:data, :List, [nat()], []}, {:data, :List, [bd()], []}]
```

- [ ] **Step 5: Run to verify GREEN** — `MIX_ENV=test mix test test/antigen/generators/sig_menu_test.exs` → PASS (3).

- [ ] **Step 6: Commit** — `feat(antigen): generate List(A) terms + List goal seeds`

### Task 3: Π/Σ goal seeds

**Files:** `lib/antigen/generators/sig_menu.ex`, test.

- [ ] **Step 1: Write the failing test** (append to `sig_menu_test.exs`):

```elixir
  test "goal_types includes a Pi and a Sigma seed, each inhabitable, canon total" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    seeds = SigMenu.goal_types()
    assert Enum.any?(seeds, &match?({:pi, _, _}, &1))
    assert Enum.any?(seeds, &match?({:sigma, _, _}, &1))
    for g <- seeds do
      assert SigMenu.inhabitable?(ctx, g), "non-inhabitable seed: #{inspect(g)}"
      # canon must not raise
      assert SigMenu.canon(ctx, g)
    end
  end

  test "gen_term over a Pi goal produces a lambda" do
    alias Antigen.Generators.Term
    alias Antigen.Backend.StreamData, as: SD
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    gen = Term.gen_term(ctx, {:pi, SigMenu.nat(), SigMenu.nat()})
    terms = SD.sample(SD.interp(gen), 10)
    assert Enum.any?(terms, &match?({:lam, _, _}, &1))
  end
```

- [ ] **Step 2: Run to verify RED** — `goal_types` has no `:pi`/`:sigma` seed today.

- [ ] **Step 3: Add Π/Σ seeds** to `goal_types/0` (Σ of inhabitables; keep the index closed):

```elixir
  def goal_types, do: [nat(), bd(), vec(z()), vec(s(z())),
                       {:data, :List, [nat()], []}, {:data, :List, [bd()], []},
                       {:pi, nat(), nat()}, {:pi, nat(), bd()},
                       {:sigma, nat(), nat()}]
```

> `{:sigma, nat(), nat()}` (a non-dependent pair `Nat × Nat`) is the safe minimal Σ seed —
> its `b` doesn't reference the bound var, so `subst0` is trivial and inhabitability is
> `inhabitable?(nat()) ∧ inhabitable?(nat())` = true. A `{:sigma, nat(), vec({:var,0})}`
> (dependent) seed is a richer follow-up but risks a stuck Vec index at canon; keep it out
> unless Step 1's inhabitability check passes for it.

- [ ] **Step 4: Run to verify GREEN** — PASS (5). The `intro_rules` for `:pi`/`:sigma` already exist (term.ex:104-122), so no generator change is needed.

- [ ] **Step 5: Health gate + differential trio** — `MIX_ENV=test mix test test/antigen/typed_term_meta_test.exs test/antigen/health_gate_test.exs` → PASS (the richer menu must not tank binder-usage/reduction-activity floors, and the three differential assays stay green over the deeper stream). If a floor regresses, investigate before proceeding (do NOT lower the floor).

- [ ] **Step 6: Commit** — `feat(antigen): add Pi/Sigma goal seeds to the Tier-B menu`

---

## PHASE 2 — `erasure_preservation` assay

### Task 4: Mark `vcons`'s `n` argument `:erased` (precondition)

**Files:** `lib/antigen/generators/sig_menu.ex`, test.

- [ ] **Step 1: Write the failing test** (append to `sig_menu_test.exs`):

```elixir
  test "vcons declares its length witness n as :erased (so erase is not the identity)" do
    env = SigMenu.env_of(:v1)
    assert Inductive.ctor_quantities(env, :vcons) == [:erased, :present, :present]
  end
```

- [ ] **Step 2: Run to verify RED** — `vcons` currently declares no quantities (defaults all-`:present`).

- [ ] **Step 3: Add the quantity vector** to the `vcons` declaration in `env_of(:v1)` (sig_menu.ex:38):

```elixir
          Inductive.ctor(:vcons, [{:n, nat()}, {:x, nat()}, {:xs, vec({:var, 1})}], [s({:var, 2})],
            [:erased, :present, :present])
```

- [ ] **Step 4: Run to verify GREEN** — PASS. Then **run the FULL suite** (`MIX_ENV=test mix test`) — marking `n` erased changes `Erase.erase` behavior but NOT `vcons`'s arity/types (spec §4/§8-5), so `Kernel.infer`/`check`/`Term.term?` and banked-seed replay must be unaffected. Expect 0 failures. If the differential trio or a banked seed breaks, STOP — the additive-only assumption was wrong; investigate.

- [ ] **Step 5: Commit** — `feat(antigen): mark vcons length witness :erased (enables non-vacuous erasure testing)`

### Task 5: `term/erasure_preservation` assay + negative control

**Files:** `lib/antigen/assays/term.ex` (or new `erasure_preservation.ex`), `lib/antigen/generators/term.ex` (`@assay_ids`), `lib/antigen/runner.ex`, test.

- [ ] **Step 1: Confirm the erase/nf/quote API** — read `assays/term.ex`'s existing
  `term/normalization` clause to see exactly how it calls `Normalise` (does it `nf` a Core
  term directly, or `eval` then `quote`?), the fuel constant (`@assay_fuel`), and how it
  detects `:fuel_exhausted`. `erasure_preservation` must use the SAME nf/quote entry point on
  both `erase(t)` and `t` so the comparison is apples-to-apples. Also confirm
  `Cure.Elab.Erase.erase/2`'s arity (`(env, term)`) and that `p.ctx`/`p.type` give the env.

- [ ] **Step 2: Write the failing tests** — `test/antigen/assays/erasure_preservation_test.exs`:

```elixir
defmodule Antigen.Assays.ErasurePreservationTest do
  use ExUnit.Case, async: false
  alias Antigen.Assays.Term, as: TermAssay   # or Antigen.Assays.ErasurePreservation
  alias Antigen.{Challenge}
  alias Antigen.Generators.SigMenu
  alias Cure.Core.Context

  defp ch(term, type) do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    Challenge.new(kind: :typed_term, assay: "term/erasure_preservation",
      label: :positive, payload: %{term: term, type: type, ctx: ctx, sig: :v1}, seed: 1)
  end

  test "real erase preserves nf on a vcons term (erased n dropped, commutation holds)" do
    # Vec 1 built with vcons: {:ctor,:vcons,[Z, Z, vnil]} : Vec (S Z)
    t = {:ctor, :vcons, [{:ctor, :Z, []}, {:ctor, :Z, []}, {:ctor, :vnil, []}]}
    ty = {:data, :Vec, [], [{:ctor, :S, [{:ctor, :Z, []}]}]}
    assert TermAssay.run(ch(t, ty)) == :ok
  end

  test "negative control: an erase stub that drops a :present arg infects" do
    t = {:ctor, :vcons, [{:ctor, :Z, []}, {:ctor, :Z, []}, {:ctor, :vnil, []}]}
    ty = {:data, :Vec, [], [{:ctor, :S, [{:ctor, :Z, []}]}]}
    # stub: drop the FIRST kept arg from any ctor (breaks commutation vs real nf)
    bad_erase = fn _env, {:ctor, c, [_ | rest]} -> {:ctor, c, rest}
                   _env, other -> other end
    k = %{TermAssay.__real_erase_ops__() | erase: bad_erase}
    assert {:violation, {:erasure_not_preserved, _}} = TermAssay.run(ch(t, ty), k)
  end
end
```

> The exact op-map accessor name (`__real_erase_ops__` vs extending the existing
> `@real_kernel`) is pinned in Step 3 — match whatever `assays/term.ex` already exposes;
> if it exposes `@real_kernel` via a `__real__/0`, extend that map with `erase`.

- [ ] **Step 3: Run to verify RED** — no `term/erasure_preservation` dispatch clause; `run` raises/FunctionClause.

- [ ] **Step 4: Implement the assay** — add to `assays/term.ex`. Extend the op-map with `erase: &Cure.Elab.Erase.erase/2`; add the dispatch clause (formulation (a), spec §8-2):

```elixir
  defp dispatch("term/erasure_preservation", ctx, p, _inferred, k) do
    env = Context.env(ctx)
    erased = k.erase.(env, p.term)
    with {:ok, nf_erased} <- nf_or_fuel(erased, ctx),
         {:ok, nf_t} <- nf_or_fuel(p.term, ctx),
         erased_nf_t = k.erase.(env, nf_t) do
      cond do
        Serialize.encode(nf_erased) == Serialize.encode(erased_nf_t) -> :ok
        true -> {:violation, {:erasure_not_preserved, %{lhs: nf_erased, rhs: erased_nf_t}}}
      end
    else
      {:fuel, stage} -> {:violation, {:fuel_exhausted, stage}}
    end
  end
```

> `nf_or_fuel/2` wraps the normalize call, returning `{:ok, term}` or `{:fuel, stage}` —
> model it on how `term/normalization` already distinguishes fuel exhaustion (Step 1). The
> LHS is `nf(erase t)`, the RHS is `erase(nf t)` (commutation). Compare via `Serialize.encode`
> (canonical) rather than raw `==` to match the existing assays' comparison discipline.

- [ ] **Step 5: Wire** — add `"term/erasure_preservation"` to `Term.@assay_ids` (term.ex) and a `assay_module("term/erasure_preservation")` clause in `runner.ex`.

- [ ] **Step 6: Run to verify GREEN** — PASS (2). The baseline passes (real erase commutes with nf on the erased-n vcons term); the negative control infects (the drop-a-present-arg stub breaks commutation).

- [ ] **Step 7: Full suite** — `MIX_ENV=test mix test` → 0 failures.

- [ ] **Step 8: Commit** — `feat(antigen): term/erasure_preservation assay (nf∘erase ≡ erase∘nf, finds erase corruption)`

---

## PHASE 3 — Ill-typed mutation for the new type formers

### Task 6: `pair_component` operator (self-wrapped)

**Files:** `lib/antigen/generators/mutation.ex`, `lib/antigen/challenge.ex`, test.

- [ ] **Step 1: Read** `mutation.ex`'s existing `build/2` clauses + the `wrap`/`@wrappers`/`deepen` machinery (esp. the `:pair` wrapper `wrap(inner, :pair, filler) = {:app, {:lam, sig(), z()}, {:pair, inner, filler}}`) and `operators/0`. Confirm `sig()`/`nat_t()` helpers.

- [ ] **Step 2: Write the failing test** — `test/antigen/generators/mutation_test.exs` (append or create):

```elixir
  test "pair_component builds a check-embedded ill-typed pair the kernel rejects" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    mutant = Mutation.build(ctx, :pair_component)
    # never a bare :pair (would crash Kernel.infer) — must be app-wrapped
    refute match?({:pair, _, _}, mutant)
    assert {:error, _} = Kernel.infer(ctx, mutant)
  end
```

- [ ] **Step 3: Run to verify RED** — `build(ctx, :pair_component)` undefined (FunctionClause).

- [ ] **Step 4: Implement** — add to `mutation.ex` (and `:pair_component` to `operators/0`):

```elixir
  def build(ctx, :pair_component) do
    # Σ Nat. Nat expects both components Nat; put a Bd in the first slot, embedded
    # in an identity application against the sigma type so Kernel.infer type-CHECKS
    # the pair (a bare :pair has NO infer clause — it would crash, spec §5).
    sigma_t = {:sigma, nat_t(), nat_t()}
    bad_pair = {:pair, {:ctor, :T, []}, {:ctor, :Z, []}}   # T : Bd, not Nat
    {:app, {:lam, sigma_t, {:var, 0}}, bad_pair}
  end
```

> Confirm `nat_t()`/`sig()` helper names against Step 1; use the existing ones.

- [ ] **Step 5: Run to verify GREEN** — PASS. The mutant is app-wrapped and `Kernel.infer` rejects it (checks `bad_pair` against `Σ Nat.Nat`, `T : Bd ≠ Nat`).

- [ ] **Step 6: Load-bearing analog check** — add a test that the WELL-TYPED analog (same wrapper, a valid `{:pair, Z, Z}`) is ACCEPTED, proving the operator genuinely ill-types:

```elixir
  test "pair_component's well-typed analog is accepted (operator genuinely ill-types)" do
    env = SigMenu.env_of(:v1); ctx = Context.empty(env)
    good = {:app, {:lam, {:sigma, {:data,:Nat,[],[]}, {:data,:Nat,[],[]}},
                   {:var, 0}}, {:pair, {:ctor,:Z,[]}, {:ctor,:Z,[]}}}
    assert {:ok, _} = Kernel.infer(ctx, good)
  end
```

- [ ] **Step 7: Intern atoms** — `:pair_component` in `challenge.ex` `@known_atoms` (mutants bank via `explore/1`).

- [ ] **Step 8: Commit** — `feat(antigen): pair_component mutation operator (Sigma component type mismatch)`

### Task 7: `lam_body_type` / `app_result` operators (codomain break)

**Files:** `lib/antigen/generators/mutation.ex`, `lib/antigen/challenge.ex`, test.

- [ ] **Step 1: Write the failing test** (append to `mutation_test.exs`):

```elixir
  test "app_result builds a function whose result violates its declared codomain, rejected" do
    env = SigMenu.env_of(:v1); ctx = Context.empty(env)
    mutant = Mutation.build(ctx, :app_result)
    assert {:error, _} = Kernel.infer(ctx, mutant)
  end
```

- [ ] **Step 2: Run to verify RED.**

- [ ] **Step 3: Implement** — a λ claiming codomain `Nat` but returning `Bd`, forced by ascription/application so `infer` sees the mismatch (distinct from `app_domain`, which breaks the *domain*):

```elixir
  def build(_ctx, :app_result) do
    # (λ x:Nat. T) : Nat -> Nat  applied to Z  — body T : Bd violates codomain Nat.
    # Wrap the lambda so its declared Pi type is checked against the Bd-typed body.
    bad_fun = {:lam, nat_t(), {:ctor, :T, []}}           # body T : Bd, not Nat
    pi_t = {:pi, nat_t(), nat_t()}
    {:app, {:lam, pi_t, {:app, {:var, 0}, {:ctor, :Z, []}}}, bad_fun}
  end
```

> Confirm this construction makes `Kernel.infer` reject at the codomain check (the inner
> `{:lam, nat_t, T}` checked against `pi_t = Nat->Nat` fails because `T : Bd`). If `infer`
> instead accepts (because it infers the lam's type from the body as `Nat->Bd` and the outer
> app just mismatches differently), adjust so the rejection is specifically a codomain
> violation — the point is a codomain fault class `app_domain` cannot produce (spec §5). If a
> single clean codomain-only construction proves elusive, keep `app_result` and drop the
> separate `lam_body_type` (one genuine codomain operator suffices); record the decision.

- [ ] **Step 4: GREEN** + analog-accepted test (well-typed `(λx:Nat.Z)` version accepted).

- [ ] **Step 5: Intern** `:app_result` (and `:lam_body_type` if kept) in `@known_atoms`; add to `operators/0`.

- [ ] **Step 6: Commit** — `feat(antigen): app_result mutation operator (Pi codomain mismatch)`

### Task 8: `type_param_mismatch` operator (List parameter)

**Files:** `lib/antigen/generators/mutation.ex`, `lib/antigen/challenge.ex`, test.

- [ ] **Step 1: Write the failing test** (append):

```elixir
  test "type_param_mismatch: Cons of a wrong-param element into List(Nat), rejected" do
    env = SigMenu.env_of(:v1); ctx = Context.empty(env)
    mutant = Mutation.build(ctx, :type_param_mismatch)
    refute match?({:ctor, :Cons, _}, mutant)   # never bare (param-ctor → :ctor_requires_checking_mode)
    assert {:error, _} = Kernel.infer(ctx, mutant)
  end
```

- [ ] **Step 2: Run to verify RED.**

- [ ] **Step 3: Implement** — embed a `Cons (T:Bd) Nil : List(Nat)` where the kernel CHECKS it against `List(Nat)` (a bare param-ctor would hit `:ctor_requires_checking_mode` for the good analog too — spec §5). Decide deepen-compat per §5 (submit pre-wrapped, no deepen — record):

```elixir
  def build(_ctx, :type_param_mismatch) do
    list_nat = {:data, :List, [nat_t()], []}
    # Cons (T:Bd) Nil — element T : Bd violates the List(Nat) parameter
    bad_cons = {:ctor, :Cons, [{:ctor, :T, []}, {:ctor, :Nil, []}]}
    {:app, {:lam, list_nat, {:var, 0}}, bad_cons}   # forces CHECK of bad_cons : List(Nat)
  end
```

- [ ] **Step 4: GREEN** + analog-accepted test: the well-typed `Cons Z Nil : List(Nat)` (same wrapper) is accepted — proving both that the operator ill-types AND that Task 1's `List` family type-checks a correct `Cons` in check mode.

- [ ] **Step 5: Intern** `:type_param_mismatch` in `@known_atoms`; add to `operators/0`.

- [ ] **Step 6: Commit** — `feat(antigen): type_param_mismatch mutation operator (List parameter mismatch)`

---

## Task 9: Full-suite verification (Stage 5 gate)

- [ ] **Step 1: Quarantine** — `MIX_ENV=test mix test test/antigen/architecture_test.exs` → PASS (no `StreamData` token in the new assay/generator code).
- [ ] **Step 2: Full suite (single run)** — `MIX_ENV=test mix test` → 0 failures (2732 baseline + new tests). If any pre-existing test fails, STOP — a menu/atom edit regressed something.
- [ ] **Step 3: Restore side effects** — `git checkout -- test/antigen/seeds.sexp 2>/dev/null; git status --short` (the generator may have banked new `:typed_term`/`:mutant_term` seeds during the run — per the standing corpus-expansion instruction those are intentional expansions; if `seeds.sexp` grew with valid new seeds, that is expected, KEEP them and commit separately; only revert if the diff is spurious). Confirm the tree state is intentional.
- [ ] **Step 4:** (Report is Stage 5 of autopilot — written separately.)

## Self-review (against spec)

- **Spec §3 richer menu** → Tasks 1–3 (List family, List gen+seeds, Π/Σ seeds). ✓
- **Spec §4 erasure_preservation + the `:erased` precondition** → Task 4 (vcons `:erased` FIRST) then Task 5 (assay, formulation (a), fuel class, negative control). ✓
- **Spec §5 three mutation constructions with the self-wrap/no-bare requirements** → Tasks 6 (pair_component app-wrapped), 7 (app_result codomain), 8 (type_param_mismatch check-embedded). Each has the load-bearing analog-accepted test (spec §9). ✓
- **Spec §8-1 (List intro-only, no eliminator)** → Task 2 adds intro rule only; no case-eliminator. ✓
- **Spec §8-5 (additive `:v1`)** → Tasks 1/4 are additive; Task 4 Step 4 explicitly re-runs the full suite to confirm banked replay unaffected. ✓
- **Spec §6 invariants** → no `Cure.*` edits; quarantine (Task 9); `:ok|{:violation}` only (fuel its own class); atoms interned (Tasks 1/6/7/8); health gate (Task 3 Step 5). ✓
- **First-param-family risk** → Task 1 Step 1 verifies the `Inductive` param convention before declaring (no guess). ✓
- **No placeholders:** every code step shows code; the two genuinely source-dependent spots (param de Bruijn convention, exact nf/fuel entry point) are explicit verify-first steps, not hand-waves.
