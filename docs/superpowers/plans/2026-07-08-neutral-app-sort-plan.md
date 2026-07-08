# Neutral-Application Sort Inference (Sigma D1) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Land the D1 kernel enabler — `check_motive_wf` accepts neutral type-valued applications (`b(first(p))`-shaped motives) via a reify+infer clause, plus the §2.4 defensive `{:pair,…}` infer clause — spec `docs/superpowers/specs/2026-07-08-neutral-app-sort-design.md` (hardened `fb68e84`).

**Architecture:** Exactly two new clauses in `lib/cure/core/kernel.ex` (TCB — blanket-approved as Agda/Lean-aligned, FULL verification gate mandatory): an `infer_type_value_sort` clause that reifies the neutral application signature-aware and accepts only if the kernel's own term-level `infer/2` yields `{:vtype, l}`, and a one-line defensive `infer(_, {:pair,_,_})` rejection. Plus: unit tests, an Antigen antibody (accept pin + Malformed reject seed), and a new `sg` differential-oracle cluster.

**Tech Stack:** Elixir, `Cure.Core.{Kernel,Quote,Context,Eval}`, ExUnit, Antigen, `mix cure.oracle` + idris2.

## Global Constraints (every task implicitly includes these)

- Working dir: `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/kernel-parity-batch`, branch `autopilot/kernel-parity-batch`. **Never read or edit files under the parent checkout `/Users/ch/Develop/esp32-beam/cure-lang/lib/…` — an earlier agent did and produced confidently wrong facts (spec §0's stale-scout warning).**
- **TCB scope:** `lib/cure/core/kernel.ex` gains exactly the two spec'd clauses; NOTHING else under `lib/cure/core/` changes. No changes to `lib/cure/elab/*` (the feature is kernel-side; surface forms already exist), `lib/cure/types/*`, `lib/cure/compiler/*` (non-dependent decoy pipeline).
- Strict red-green TDD; tests behavioral and immutable once green. ONE mix command at a time, ever (past concurrent run caused a kernel panic). Full gates run ONCE, alone, in Task 4.
- Git: commit per task; EVERY commit `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`; NO trailers; explicit-pathspec staging only.
- **`mix cure.oracle` may be run exactly once, in Task 3, with the cluster argument `sg` only** (`mix cure.oracle sg`) — it regenerates only `test/oracle/sg/verdicts.json` (spec §3.4, review-verified). Never run it bare or with another cluster. If it unexpectedly modifies any OTHER cluster's verdicts.json (`git status` check after), `git checkout -- test/oracle/<other>/verdicts.json` and STOP-and-report.
- Prereq: `~/Develop/Idris2/build/exec/idris2` must exist (the oracle shells out to it). If missing → STOP-and-report (do not skip the oracle task).
- STOP-and-report: any oracle divergence on sg01 (either direction); any existing test failing at any point; any need to touch a third place in kernel.ex; the accept-probe still rejecting after both clauses land.

## File Structure

- `lib/cure/core/kernel.ex` — the two clauses (Task 1).
- `test/cure/elab/dependent_eliminator_test.exs` — NEW: surface probe + hand-built-Core negatives (Task 1).
- `lib/antigen/generators/malformed.ex` — one new reject seed in `malformation/0` (Task 2).
- `test/antigen/neutral_app_motive_test.exs` — NEW: accept/reject antibody pins through the real kernel (Task 2).
- `test/oracle/sg/sg01_dependent_second.{cure,idr}` + generated `verdicts.json` — NEW (Task 3).

---

### Task 1: the two kernel clauses, with staged red evidence

**Files:**
- Modify: `lib/cure/core/kernel.ex` (`infer_type_value_sort` clauses at ~606-665; `infer/2` clauses region)
- Test: `test/cure/elab/dependent_eliminator_test.exs` (new)

- [ ] **Step 0: Pre-flight (read-only)**

1. Confirm `kernel.ex` can reference `Quote` (grep `alias Cure.Core` in kernel.ex; if `Quote` is not in the alias list, use the fully-qualified `Cure.Core.Quote.reify/3` in the new clause instead of adding an alias line — keep the diff to the two clauses).
2. Confirm `Quote.reify/3`'s public signature `reify(value, depth \\ 0, sig \\ nil)` (`lib/cure/core/quote.ex:40`) and that `{:vneutral, n}` dispatches to the private `reify_neutral/3` (quote.ex:76).
3. Confirm `infer/2` has no `{:pair,_,_}` clause (grep `def infer` clause heads).

- [ ] **Step 1: Write the failing tests**

```elixir
defmodule Cure.Elab.DependentEliminatorTest do
  @moduledoc """
  Spec 2026-07-08-neutral-app-sort (Sigma D1): motives applying a type-family
  head — `b(first(p))` — sort via reify+infer (kernel.ex napp clause); adversarial
  motives reject cleanly (defensive {:pair,…} infer clause). Surface probes drive
  Program.elaborate; the §2.4 crash probe hand-builds Core against Kernel.infer.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Eval, Kernel}
  alias Cure.Elab.Program

  @probe """
  mod P
    type Nat = Z | S(Nat)
    type MySigma(a: Type, b: (a) -> Type) indices ()
      mk_pair : (x: a) -> b(x) -> MySigma(a, b)
    fn first({a: Type}, {b: (a) -> Type}, p: MySigma(a, b)) -> a = match p
      mk_pair(x, y) -> x
    fn second({a: Type}, {b: (a) -> Type}, p: MySigma(a, b)) -> b(first(p)) = match p
      mk_pair(x, y) -> y
  end
  """

  test "D1 probe: dependent second projection elaborates (b(first(p)) motive)" do
    assert {:ok, _env} = Program.elaborate(@probe)
  end

  test "negative: non-type-valued head in type position still rejects" do
    src = """
    mod P
      type Nat = Z | S(Nat)
      type MySigma(a: Type, b: (a) -> Type) indices ()
        mk_pair : (x: a) -> b(x) -> MySigma(a, b)
      fn bad({a: Type}, {b: (a) -> Type}, {g: (a) -> Nat}, p: MySigma(a, b)) -> g(first(p)) = match p
        mk_pair(x, y) -> y
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end

  test "negative: ill-typed argument to the type-family head still rejects" do
    src = """
    mod P
      type Nat = Z | S(Nat)
      type Other = Mk
      type MySigma(a: Type, b: (a) -> Type) indices ()
        mk_pair : (x: a) -> b(x) -> MySigma(a, b)
      fn bad({b: (Other) -> Type}, p: MySigma(Nat, ?)) -> b(Z()) = Z()
    end
    """

    # The exact surface framing may need adjustment (see latitude note); the
    # requirement is: a type-position application whose argument does not match
    # the head's domain is rejected, not accepted.
    assert {:error, _} = Program.elaborate(src)
  end

  # §2.4 crash probe: hand-built Core, driven straight at Kernel.infer. The
  # motive applies its own Nat-typed binder — head resolves, but for the PAIR
  # variant the argument is a pair literal in a non-Σ domain, which (post-napp
  # clause) routes check→infer on a bare {:pair,…}.
  describe "§2.4 adversarial motives reject cleanly (never crash)" do
    defp nat_env do
      {:ok, env} = Program.elaborate("mod P\n  type Nat = Z | S(Nat)\nend\n")
      env
    end

    defp bad_motive_case(motive) do
      {:case, {:ctor, :Z, []}, motive, [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:ctor, :Z, []}}]}
    end

    test "motive applying a non-function head rejects :bad_motive" do
      ctx = Context.empty(nat_env())
      nat = {:data, :Nat, [], []}
      motive = {:lam, nat, {:app, {:var, 0}, {:ctor, :Z, []}}}
      assert {:error, :bad_motive} = Kernel.infer(ctx, bad_motive_case(motive))
    end

    test "motive applying a head to a pair literal rejects :bad_motive (no FunctionClauseError)" do
      ctx = Context.empty(nat_env())
      nat = {:data, :Nat, [], []}
      motive = {:lam, nat, {:app, {:var, 0}, {:pair, {:ctor, :Z, []}, {:ctor, :Z, []}}}}
      assert {:error, :bad_motive} = Kernel.infer(ctx, bad_motive_case(motive))
    end
  end
end
```

Latitude (report every use): the two surface negatives pin *rejection*, not a specific tag — if a fixture fails to parse/elaborate for an incidental surface reason (e.g. the `?`-placeholder or implicit framing in the third test), adjust the FIXTURE to the nearest expressible form that still applies a wrong-domain / non-type head in type position; if no such surface form exists, replace that test with a hand-built-Core equivalent in the §2.4 describe block and note it. The probe test and both §2.4 tests are NOT adjustable. If the ctor atom for the hand-built cases is namespaced (`:"P.Z"`), resolve it the way `test/cure/elab/named_implicit_tail_test.exs`'s `ctor_atom/2` helper does.

- [ ] **Step 2: Run — capture the pre-change baseline**

Run: `mix test test/cure/elab/dependent_eliminator_test.exs`
Expected TODAY: the D1 probe FAILS (`{:error, :bad_motive}` where `{:ok, _}` expected); both surface negatives PASS (already reject); **both §2.4 tests PASS** (the napp value hits the fallthrough → `:bad_motive` — the crash path does not exist yet). Record all five outcomes.

- [ ] **Step 3: Add ONLY the `infer_type_value_sort` napp clause**

Insert after the `{:vneutral, {:nvar, level}}` clause (~kernel.ex:613-620), exactly as spec §2:

```elixir
  # A neutral APPLICATION is a valid type iff the kernel's own term-level
  # judgement says so: reify the spine back to a term (signature-aware, so a
  # {:vdata,…} argument keeps its param/index split — quote.ex split_data_args)
  # and infer it. infer/2's {:app, f, a} rule resolves the head's type (ctx var
  # or signature global), CHECKS each argument against the instantiated Pi
  # domain, and returns the codomain — full validation, nothing trusted from
  # the (untrusted) elaborator that assembled the motive. Accept only a
  # {:vtype, l} result: `b(first(p))` with `b : (a) -> Type` sorts at l; a
  # non-type codomain stays :not_a_type_value.
  defp infer_type_value_sort(ctx, {:vneutral, {:napp, _, _} = neutral}) do
    term = Quote.reify({:vneutral, neutral}, Context.length(ctx), Context.signature(ctx))

    case infer(ctx, term) do
      {:ok, {:vtype, level}} -> {:ok, level}
      _ -> {:error, :not_a_type_value}
    end
  end
```

(Use `Cure.Core.Quote.reify` fully qualified if Step 0.1 found no alias.)

- [ ] **Step 4: Run — capture the mid-point crash (the §2.4 necessity proof)**

Run: `mix test test/cure/elab/dependent_eliminator_test.exs`
Expected NOW: the D1 probe PASSES; the non-function-head §2.4 test still passes (`ensure_pi` on a Nat head fails inside `infer` → `:not_a_type_value` → `:bad_motive`); **the pair-literal §2.4 test CRASHES with `FunctionClauseError` (no `infer/2` clause for `{:pair,…}`)**. Capture the exact exception — this is the red evidence that the defensive clause is load-bearing, not decorative.

- [ ] **Step 5: Add the defensive `infer` clause**

Next to `infer/2`'s `{:fst,_}`/`{:snd,_}` clauses:

```elixir
  # Pairs are check-only (see check/3 against {:vsigma,…}); an infer position can
  # only be reached by an adversarial reified motive (spec 2026-07-08-neutral-app-
  # sort §2.4) — reject explicitly instead of crashing on a missing clause.
  def infer(_ctx, {:pair, _, _}), do: {:error, :pair_not_inferable}
```

- [ ] **Step 6: Run to verify all green, then the kernel neighborhood**

Run: `mix test test/cure/elab/dependent_eliminator_test.exs` — expected 5 tests, 0 failures.
Then (one at a time): `mix test test/cure/core/` — expected all pass (273+); `mix test test/cure/elab/` — expected all pass (440+, includes the new 5).

- [ ] **Step 7: Commit**

```bash
git add -- lib/cure/core/kernel.ex test/cure/elab/dependent_eliminator_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(kernel): sort neutral type-valued applications via reify+infer (Sigma D1 enabler; defensive pair infer clause)" \
  -- lib/cure/core/kernel.ex test/cure/elab/dependent_eliminator_test.exs
```

---

### Task 2: Antigen antibody

**Files:**
- Modify: `lib/antigen/generators/malformed.ex` (one entry in the `malformation/0` frequency list, next to the existing `case_bad_motive` entries at ~line 65-67)
- Test: `test/antigen/neutral_app_motive_test.exs` (new)

- [ ] **Step 1: Write the failing antibody test**

```elixir
defmodule Antigen.NeutralAppMotiveTest do
  @moduledoc """
  D1 antibody (spec 2026-07-08-neutral-app-sort §3.2): the kernel accepts a
  motive applying a type-family head (the enlarged accept set) and still rejects
  non-type-valued heads — pinned through the REAL kernel, no shims.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Eval, Kernel}
  alias Cure.Elab.Program

  defp nat_env do
    {:ok, env} = Program.elaborate("mod P\n  type Nat = Z | S(Nat)\nend\n")
    env
  end

  # ctx: [ b : (Nat) -> Type ]  (level 0)
  defp ctx_with_type_family(env) do
    pi = Eval.eval({:pi, {:data, :Nat, [], []}, {:type, 0}}, [])
    Context.extend(Context.empty(env), pi)
  end

  test "accept pin: a motive applying a type-family variable sorts (case infers)" do
    ctx = ctx_with_type_family(nat_env())
    nat = {:data, :Nat, [], []}
    # b is de Bruijn var 1 UNDER the motive's own binder (v : Nat is var 0).
    motive = {:lam, nat, {:app, {:var, 1}, {:var, 0}}}

    # Branch bodies must inhabit b(idx) — impossible to write closed, so use a
    # scrutinee-free acceptance probe: check_motive_wf alone gates the motive;
    # drive it via infer on a case whose branches are themselves neutral-typed.
    # Simplest fully-checkable form: branches returning `b(...)`-typed values do
    # not exist closed, so pin acceptance at the motive-wf boundary by asserting
    # the case does NOT fail with :bad_motive (it must fail LATER, in branch
    # checking, with a branch-related error — proving motive-wf passed).
    kase = {:case, {:ctor, :Z, []}, motive, [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:ctor, :Z, []}}]}

    assert {:error, err} = Kernel.infer(ctx, kase)
    refute err == :bad_motive, "motive-wf should now accept the neutral-app motive; got :bad_motive"
  end

  test "reject pin: a motive applying a NON-function head still fails :bad_motive" do
    ctx = Context.empty(nat_env())
    nat = {:data, :Nat, [], []}
    motive = {:lam, nat, {:app, {:var, 0}, {:ctor, :Z, []}}}
    kase = {:case, {:ctor, :Z, []}, motive, [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:ctor, :Z, []}}]}

    assert {:error, :bad_motive} = Kernel.infer(ctx, kase)
  end
end
```

(The accept pin's discrimination logic — "fails, but NOT with `:bad_motive`" — is deliberate: a fully inhabitable neutral-app case needs a `b`-instance value, which is what the Task 1 surface probe covers end-to-end; this pin isolates the motive-wf boundary itself. If ctor atoms are namespaced, use the `ctor_atom` resolution pattern. If branch-body checking rejects with something surprising, record the actual tag in the assertion message — the pin is `!= :bad_motive`.)

- [ ] **Step 2: Run to verify the red**

Run: `mix test test/antigen/neutral_app_motive_test.exs`
Expected: with Task 1 landed, BOTH may already pass (the antibody pins the landed behavior — red-before-Task-1 is impossible since Task 1 precedes; the "red" evidence for this task is instead the generator step below). If the accept pin fails WITH `:bad_motive`, Task 1 is broken — STOP.

- [ ] **Step 3: Add the Malformed generator seed**

In `lib/antigen/generators/malformed.ex`'s `malformation/0` frequency list, next to the existing `case_bad_motive` entries (~65-67):

```elixir
      {1,
       tagged(
         case_bad_motive({:lam, @nat, {:app, {:var, 0}, @z}}),
         "case motive applies a non-function (Nat-typed) head — napp reject path"
       )},
```

- [ ] **Step 4: Run the Antigen suite (scoped, then whole)**

Run: `mix test test/antigen/` — expected: all pass (490 + 2 new = 492; the Malformed seed feeds existing `"term/rejection"` assays — if the frequency-list addition changes any seeded-run expectations pinned elsewhere, that is a STOP, not an edit).

- [ ] **Step 5: Commit**

```bash
git add -- lib/antigen/generators/malformed.ex test/antigen/neutral_app_motive_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "test(antigen): neutral-app motive antibody — accept pin + malformed napp reject seed" \
  -- lib/antigen/generators/malformed.ex test/antigen/neutral_app_motive_test.exs
```

---

### Task 3: differential-oracle `sg` cluster

**Files:**
- Create: `test/oracle/sg/sg01_dependent_second.cure`, `test/oracle/sg/sg01_dependent_second.idr`
- Generated: `test/oracle/sg/verdicts.json` (by the oracle run — never hand-written)

- [ ] **Step 1: Author the pair**

`sg01_dependent_second.cure` — mirror the framing of an existing accept fixture (read `test/oracle/guard/guard01_simple.cure` for the house format), content = the Task 1 probe module.

`sg01_dependent_second.idr`:

```idris
%default total

data MySigma : (a : Type) -> (b : a -> Type) -> Type where
  MkPair : (x : a) -> b x -> MySigma a b

first : MySigma a b -> a
first (MkPair x y) = x

second : (p : MySigma a b) -> b (first p)
second (MkPair x y) = y
```

- [ ] **Step 2: Run the oracle for this cluster ONLY, alone**

Run: `mix cure.oracle sg`
Expected: sg01 → cure `accept`, idris `accept`, relation `same`, written to `test/oracle/sg/verdicts.json`. Then `git status` — confirm NO other cluster's verdicts.json changed (if one did: `git checkout -- <it>` and STOP-and-report). Any divergence on sg01 (either direction) = STOP-and-report per the oracle contract — do not mark `cure_stricter`, do not edit fixtures to force agreement.

- [ ] **Step 3: Replay green**

Run: `mix test test/oracle_replay_test.exs`
Expected: all pass, including the new sg row.

- [ ] **Step 4: Commit**

```bash
git add -- test/oracle/sg/sg01_dependent_second.cure test/oracle/sg/sg01_dependent_second.idr test/oracle/sg/verdicts.json
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "test(oracle): sg cluster — dependent second projection typechecks (same/same)" \
  -- test/oracle/sg/sg01_dependent_second.cure test/oracle/sg/sg01_dependent_second.idr test/oracle/sg/verdicts.json
```

---

### Task 4: full gate + final verification

- [ ] **Step 1: Full gates (ONE at a time, alone, in this order)**

1. `mix test test/antigen/` — expected: 492, 0 failures.
2. `mix test` — expected: ~3245 (3238 + 5 + 2, recount from actual red-step outputs; oracle replay included), 0 failures. One known non-reproducible Antigen-seed flake: exactly one Antigen seed failure → re-run once alone; if unreproduced, note honestly. Anything else = STOP.

- [ ] **Step 2: Final verification**

- `git diff <task1-commit>~1 HEAD -- lib/cure/core/` shows ONLY the two kernel.ex clauses (+ their comments) — nothing else under core.
- `git diff --stat <task1-commit>~1 HEAD -- lib/cure/elab/ lib/cure/types/ lib/cure/compiler/` — empty except nothing at all (no elab change is expected in this initiative).
- `git log --format='%an %ae' <task1-commit>~1..HEAD` — only `Made In Heaven madeinheaven@madeinheaven.com`.

---

## Self-review notes (spec-coverage map)

- §2 clause → Task 1 Step 3 (verbatim, signature-aware reify per hardened §2.2). §2.4 defensive clause + demonstrable necessity → Task 1 Steps 4-5 (mid-point crash captured). §3.1 red-green → Task 1 Steps 2/4/6. §3.2 antibody (accept pin + Malformed reject seed, precedents DepMatch/Malformed per spec) → Task 2. §3.3 full suites → Tasks 2/4. §3.4 oracle → Task 3 (single-cluster discipline + divergence STOP). §4's five tests → Task 1 (probe + 2 surface negatives + 2 hand-built §2.4). §6.5 diff criterion → Task 4 Step 2.
- Latitude is confined to: surface framing of the two adjustable negatives, ctor-atom namespacing, and recount of gate totals — all report-required.
- D2 (Sigma retirement) is the chained follow-up; its scout inventory must be re-swept in-worktree (spec §5 note).
