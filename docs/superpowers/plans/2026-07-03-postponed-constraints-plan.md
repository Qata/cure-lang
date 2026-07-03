# Postponed/Suspended Constraints (#11) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give Cure's elaborator unifier a constraint-postponement queue with retry-on-progress and a weak/strong-rigid occurs-check split, so it accepts inputs Idris accepts via postponement — E-layer only, no TCB.

**Architecture:** Add a `constraints` queue to `MetaCtx` (unify.ex); `unify` suspends (enqueue + return `{:ok, ctx}`) instead of failing on the two postponable cases (flex-flex, weak-rigid occurs); a `drain_constraints/1` retry-all fixpoint runs at the **application-telescope boundary** (`finish_ctor_app`/`finish_global_app` in elaborator.ex, the existing `MetaCtx.new()` consumers) right before their `zonk`/`has_meta?` gate. **First-cut granularity is the application telescope already threaded today** — NOT a new definition-wide `MetaCtx` threading (spec §3.5 prerequisite; the larger threading is explicitly deferred).

**Tech Stack:** Elixir; Cure compiler (`lib/cure/elab/*`); differential oracle (`mix cure.oracle`, `idris2 --check`); ExUnit.

## Global Constraints

- **Layer: E only.** Touch `lib/cure/elab/unify.ex`, `lib/cure/elab/elaborator.ex`, `test/**`, `docs/**`. **No `lib/cure/core/*` diff** (verify at the gate with `git diff --stat`). No TCB, no Antigen antibody required (kernel re-checks every term; postponement is completeness-only).
- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO `Co-Authored-By`, no Claude signature.
- **Explicit-pathspec staging only:** `git add -- <path>` / `git commit -- <path>`. NEVER `git add -A` / `git add .` (a concurrent agent may share this worktree).
- **One build at a time.** Never two `mix` suites concurrently. Prefer scoped `mix test <file>`; full `mix test` runs once, alone, at the final gate.
- **Oracle discipline:** verdicts come from `mix cure.oracle postpone`, never hand-written; freeze into `test/oracle/postpone/verdicts.json`; `mix test test/oracle_replay_test.exs` green before any commit that touches a fixture.
- **`mix run` is unavailable** for ad-hoc elaboration probes (throws `unknown registry: Cure.Pipeline.Events.Registry`). To dump a Cure rejection reason, use a throwaway **test-env** module that calls `Cure.Elab.Program.elaborate/1` and `IO.inspect`s the error, run via `mix test`.
- **Tests immutable once green;** behavioral (assert verdicts/classifications, not internal call shapes).

## File Structure

- `lib/cure/elab/unify.ex` — `MetaCtx` struct + queue helpers (module 1); `Unify.occurs_rigidity/3` (replaces `occurs?/3`), postponement triggers in `do_unify_struct`/`solve_strengthened`, `Unify.drain_constraints/1` (module 2).
- `lib/cure/elab/elaborator.ex` — `finish_ctor_app` (:3271) and `finish_global_app` (:3651): insert a `drain_constraints/1` step before the existing `zonk`/`has_meta?` gate.
- `test/cure/elab/unify_postpone_test.exs` — NEW unit tests (queue helpers, `occurs_rigidity`, `drain_constraints`).
- `test/oracle/postpone/postpone0{1,2,3,4}_*.{cure,idr}` + `verdicts.json` — NEW oracle probes.

---

## Task 1 — RISK GATE: construct & verify the failing oracle probe(s)

**This task gates the whole feature.** It is a spike, not a code change. If no genuine divergence reproduces, **HALT** (write `AUTOPILOT-STATE.md`, notify) — do not build machinery no probe exercises.

**Files:**
- Create: `test/oracle/postpone/postpone02_weak_rigid_occurs.cure` + `.idr` (primary — most reachable per spec §3.2: bare `?a =? f(?a)` needs no spine-head helper)
- Create: `test/oracle/postpone/postpone01_flex_flex.cure` + `.idr` (secondary — flex-flex across args of ONE application, telescope granularity)
- Create (throwaway, deleted at task end): `test/zzz_probe_test.exs`

**Interfaces:**
- Produces: at least one frozen divergent fixture with a verified Cure rejection reason, consumed as the red test in Task 5.

- [ ] **Step 1: Author `postpone02` (bare weak-rigid occurs).** Write a paired `.cure`/`.idr` (`.idr` carries `%default total`, no `module` line) expressing the SAME program: a definition where an inferred implicit `?a` must unify with `f(?a)` for an `f` that is eliminable/cancelling (so the occurrence is weakly-rigid), and `?a` becomes determined by a later argument in the same application. Faithful transliteration — same signature both sides. Model it on `test/oracle/dep/dep07_higher_order_family.{cure,idr}` for shape.

- [ ] **Step 2: Author `postpone01` (flex-flex within one application telescope).** A single application `g(x, y)` whose dependent parameter types force a flex-flex constraint between two metavars created while elaborating `x`, resolved while elaborating `y`. (If this proves to need unequal-arity meta spines / a spine-head helper — spec §3.2 bullet 1 — note that and lean on `postpone02` as the gate probe.)

- [ ] **Step 3: Run the oracle.** `mix cure.oracle postpone` — records Cure and Idris verdicts into `test/oracle/postpone/verdicts.json`.

- [ ] **Step 4: Verify the divergence is genuine (not confounded).** For each probe Cure rejects, dump the ACTUAL rejection reason via the throwaway test:
```elixir
# test/zzz_probe_test.exs
defmodule ZzzProbeTest do
  use ExUnit.Case
  test "dump reason" do
    src = File.read!("test/oracle/postpone/postpone02_weak_rigid_occurs.cure")
    {:ok, ast} = Cure.Compiler.Parser.parse(src)   # adjust to real parse entrypoint
    IO.inspect(Cure.Elab.Program.elaborate(ast), label: ">>> REJECT", limit: :infinity)
  end
end
```
Run `mix test test/zzz_probe_test.exs`. Confirm the reason is a unification/occurs/unsolved failure on the intended term — NOT an arity error, parse error, or unrelated elaboration failure. If confounded, fix the probe and re-run.

- [ ] **Step 5: Gate decision.**
  - If ≥1 probe shows **Idris accept + Cure reject for the right reason** → the gap is real. Keep the divergent probe(s); for any that reproduce, the relation is transiently `cure_stricter` with reason "postponement not yet implemented (#11)". Proceed.
  - If **neither** reproduces (Idris also rejects, or Cure already accepts both) → **HALT.** Write `AUTOPILOT-STATE.md` (stage, what was tried, the verdicts, why no reach). Notify. Stop.

- [ ] **Step 6: Delete the throwaway test.** `git rm`/`rm test/zzz_probe_test.exs` (never commit it).

- [ ] **Step 7: Commit the probe fixtures.**
```bash
git add -- test/oracle/postpone/
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "test(oracle): #11 postpone probes — divergence gate (idris accept / cure reject)"
```
Expected: `verdicts.json` shows the divergence; replay (`mix test test/oracle_replay_test.exs`) is green against the newly frozen fixtures.

---

## Task 2 — `MetaCtx` constraint-queue field + pure helpers

**Files:**
- Modify: `lib/cure/elab/unify.ex` (MetaCtx module, :12–:52)
- Test: `test/cure/elab/unify_postpone_test.exs`

**Interfaces:**
- Produces: `MetaCtx.postpone/6`, `MetaCtx.constraints/1`, `MetaCtx.clear_constraints/1`, `MetaCtx.put_constraints/2`; struct field `constraints: []`. Consumed by Tasks 3–5.

- [ ] **Step 1: Write the failing test.**
```elixir
# test/cure/elab/unify_postpone_test.exs
defmodule Cure.Elab.UnifyPostponeTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.MetaCtx

  test "postpone/constraints/clear/put round-trip" do
    c = MetaCtx.new()
    assert MetaCtx.constraints(c) == []
    c = MetaCtx.postpone(c, {:meta, 0}, {:meta, 1}, 0, nil, :flex_flex)
    c = MetaCtx.postpone(c, {:meta, 2}, {:ctor, :Z, []}, 1, nil, :weak_rigid_occurs)
    assert length(MetaCtx.constraints(c)) == 2
    {c0, list} = MetaCtx.clear_constraints(c)
    assert MetaCtx.constraints(c0) == []
    assert length(list) == 2
    c1 = MetaCtx.put_constraints(c0, Enum.take(list, 1))
    assert length(MetaCtx.constraints(c1)) == 1
  end
end
```

- [ ] **Step 2: Run it, verify it fails.** `mix test test/cure/elab/unify_postpone_test.exs` — Expected: FAIL (`postpone/6` undefined).

- [ ] **Step 3: Implement.** In the `MetaCtx` module: add `constraints: []` to `defstruct` (and the `@type t`); add:
```elixir
@doc "Append a suspended constraint (a deferred unify_d call) for later retry."
def postpone(%__MODULE__{constraints: cs} = ctx, a, b, depth, sig, reason),
  do: %{ctx | constraints: cs ++ [{a, b, depth, sig, reason}]}

def constraints(%__MODULE__{constraints: cs}), do: cs
def clear_constraints(%__MODULE__{constraints: cs} = ctx), do: {%{ctx | constraints: []}, cs}
def put_constraints(%__MODULE__{} = ctx, list), do: %{ctx | constraints: list}
```

- [ ] **Step 4: Run tests, verify pass.** `mix test test/cure/elab/unify_postpone_test.exs` — Expected: PASS. Also run `mix test test/cure/elab/unify_test.exs` (or the existing unify test file) to confirm the struct change is non-breaking.

- [ ] **Step 5: Commit.**
```bash
git add -- lib/cure/elab/unify.ex test/cure/elab/unify_postpone_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(elab): MetaCtx constraint-postponement queue + helpers (#11)"
```

---

## Task 3 — `occurs_rigidity/3` (weak/strong/none classification), behavior-preserving

**Files:**
- Modify: `lib/cure/elab/unify.ex` (`occurs?/3` at :382 → `occurs_rigidity/3`; callers at :166, :335)
- Test: `test/cure/elab/unify_postpone_test.exs`

**Interfaces:**
- Consumes: nothing new.
- Produces: `Unify.occurs_rigidity(id, t, ctx) :: :strong | :weak | :none`. This task keeps EXISTING behavior (callers treat `:strong`/`:weak` exactly as the old `true`, `:none` as old `false`) so all current tests stay green; the `:weak → postpone` wiring lands in Task 5.

- [ ] **Step 1: Write the failing classification test.** Build Core terms by hand and assert the class. `id` is the target meta id.
```elixir
test "occurs_rigidity classifies strong/weak/none" do
  alias Cure.Elab.{MetaCtx, Unify}
  ctx = MetaCtx.new()
  m = {:meta, 0}
  # none: target absent
  assert Unify.occurs_rigidity(0, {:ctor, :Z, []}, ctx) == :none
  # strong: under a data constructor
  assert Unify.occurs_rigidity(0, {:ctor, :S, [m]}, ctx) == :strong
  # weak: under another metavar's application spine
  assert Unify.occurs_rigidity(0, {:app, {:meta, 1}, m}, ctx) == :weak
  # weak: under a projection
  assert Unify.occurs_rigidity(0, {:fst, m}, ctx) == :weak
  # strong dominates weak when both present
  assert Unify.occurs_rigidity(0, {:ctor, :S, [{:fst, m}, m]}, ctx) == :strong
end
```

- [ ] **Step 2: Run it, verify it fails.** `mix test test/cure/elab/unify_postpone_test.exs` — Expected: FAIL (`occurs_rigidity/3` undefined).

- [ ] **Step 3: Implement `occurs_rigidity/3`** per spec §3.3. Walk `force(t, ctx)` with a mode arg. Strong-preserving heads: `:ctor`, `:data`, `:pi`, `:lam`, `:sigma`, `:pair`, `:eq`, `:refl` (constructors/type-formers). Weak-inducing heads: `:app` with a non-constructor function, `:fst`, `:snd`, `:prim`. `{:meta, ^id}` → current mode; `{:meta, _other}` → recurse into its args in `:weak`. **No shape silently defaulted** — an unlisted tuple shape is treated as strong-preserving (conservative). Combine children by strength (`:strong` > `:weak` > `:none`). Keep the sketch:
```elixir
def occurs_rigidity(id, t, ctx), do: occ(id, force(t, ctx), :strong)
defp occ(id, {:meta, id2}, mode), do: (if id2 == id, do: mode, else: :none)
defp occ(id, {:ctor, _, args}, mode), do: combine(Enum.map(args, &occ(id, force_shallow(&1), mode)))
# ... strong-preserving heads pass `mode` down; weak-inducing heads pass `weaken(mode)` = :weak
# ... generic tuple/list fallthrough = strong-preserving walk (conservative)
defp combine(list), do: Enum.reduce(list, :none, &max_strength/2)  # :strong > :weak > :none
```
(Exact per-shape recursion table is pinned during implementation against unify.ex:354–377's `escapes?` enumeration; mirror its structural coverage so no shape is missed.)

- [ ] **Step 4: Rewire the two callers behavior-preservingly.**
  - `miller_solve` (:166): replace `false <- occurs?(id, body, ctx)` with a guard that treats `:none` as OK and `:strong`/`:weak` as the old occurs-failure (`:fallthrough`). (Task 5 will special-case `:weak`.)
  - `solve_strengthened` (:334): `case occurs_rigidity(id, t, ctx) do :none -> put_solution; _ -> {:error, {:occurs_check, id, t}} end`. (Task 5 splits `:weak → postpone`.)

- [ ] **Step 5: Run tests, verify pass + no regression.** `mix test test/cure/elab/unify_postpone_test.exs test/cure/elab/unify_test.exs` — Expected: PASS (classification correct AND existing unify behavior unchanged).

- [ ] **Step 6: Commit.**
```bash
git add -- lib/cure/elab/unify.ex test/cure/elab/unify_postpone_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(elab): occurs_rigidity/3 strong/weak/none classification (behavior-preserving) (#11)"
```

---

## Task 4 — `drain_constraints/1` retry-all fixpoint driver

**Files:**
- Modify: `lib/cure/elab/unify.ex` (Unify module — add `drain_constraints/1`)
- Test: `test/cure/elab/unify_postpone_test.exs`

**Interfaces:**
- Consumes: `MetaCtx` queue helpers (Task 2); internal `unify_d/5`.
- Produces: `Unify.drain_constraints(ctx) :: {:ok, MetaCtx.t()} | {:error, reason}`. Consumed by Task 5.

- [ ] **Step 1: Write failing tests — solves a pinnable queue; terminates+rejects a stalled queue.**
```elixir
test "drain solves a constraint pinned by an existing solution" do
  alias Cure.Elab.{MetaCtx, Unify}
  # ?0 already solved to Z; a suspended (?0 =? ?1) should pin ?1 := Z on retry
  ctx = MetaCtx.new() |> MetaCtx.put_solution(0, {:ctor, :Z, []})
  ctx = MetaCtx.postpone(ctx, {:meta, 0}, {:meta, 1}, 0, nil, :flex_flex)
  assert {:ok, ctx2} = Unify.drain_constraints(ctx)
  assert MetaCtx.constraints(ctx2) == []
  assert MetaCtx.solution(ctx2, 1) == {:ctor, :Z, []}
end

test "drain terminates and rejects a stalled queue (no infinite loop)" do
  alias Cure.Elab.{MetaCtx, Unify}
  # two unsolved bare metas, nothing to pin them → stall
  ctx = MetaCtx.new()
  ctx = MetaCtx.postpone(ctx, {:ctor, :S, [{:meta, 0}]}, {:ctor, :Z, []}, 0, nil, :flex_flex)
  assert {:error, {:unsolved_constraints, _}} =
           Task.async(fn -> Unify.drain_constraints(ctx) end) |> Task.await(2_000)
end
```
(The `Task.await(2_000)` makes a hang a test FAILURE, not a suite hang — the termination witness.)

- [ ] **Step 2: Run, verify fail.** `mix test test/cure/elab/unify_postpone_test.exs` — Expected: FAIL (`drain_constraints/1` undefined).

- [ ] **Step 3: Implement** the §3.4 fixpoint: `clear_constraints`, retry each via `unify_d(a,b,ctx,sig,depth)`, propagate `{:error,…}`, compute `progress? = map_size(solutions_after) > map_size(solutions_before)`; loop while non-empty AND progress; stalled non-empty → `{:error, {:unsolved_constraints, still}}`.

- [ ] **Step 4: Run, verify pass.** `mix test test/cure/elab/unify_postpone_test.exs` — Expected: PASS (both, incl. termination within 2 s).

- [ ] **Step 5: Commit.**
```bash
git add -- lib/cure/elab/unify.ex test/cure/elab/unify_postpone_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(elab): drain_constraints/1 retry-all fixpoint driver (#11)"
```

---

## Task 5 — Wire postponement triggers + drain at the telescope boundary (oracle red-green)

**Files:**
- Modify: `lib/cure/elab/unify.ex` (`solve_strengthened` `:weak → postpone`; flex-flex trigger in `do_unify_struct`; possibly a `spine_head/1` helper if `postpone01` needs it)
- Modify: `lib/cure/elab/elaborator.ex` (`finish_ctor_app` :3271, `finish_global_app` :3651 — drain before the `zonk`/`has_meta?` gate)
- Test (red): the Task-1 oracle probes, now expected to flip to accept.

**Interfaces:**
- Consumes: `postpone/6`, `occurs_rigidity/3`, `drain_constraints/1`.
- Produces: the verdict flips on `postpone01`/`postpone02` (→ `same` accept/accept); `postpone03`/`postpone04` still reject.

- [ ] **Step 1: Red — the probe(s) still reject.** `mix cure.oracle postpone` then inspect: the divergent probe(s) from Task 1 are still `cure_stricter` (Cure reject). This is the standing red.

- [ ] **Step 2: Wire `solve_strengthened` `:weak → postpone`.** `case occurs_rigidity(id, t, ctx) do :none -> put_solution(...); :weak -> {:ok, MetaCtx.postpone(ctx, {:meta, id}, t, depth, nil, :weak_rigid_occurs)}; :strong -> {:error, {:occurs_check, id, t}} end`. NOTE: `solve_strengthened/3` currently has no `depth` param — thread the caller's `depth` in (it is available at the `solve/4` call site) or capture the strengthened term at depth 0 (verify which frame the retry needs; the constraint must retry at the same depth the terms were forced at — see §3.1/§3.4).

- [ ] **Step 3: Wire the flex-flex trigger** in `do_unify_struct`: when both forced sides are metavariable-headed spines and Miller dispatch already fell through, `{:ok, MetaCtx.postpone(ctx, t1, t2, depth, sig, :flex_flex)}` instead of the mismatch error. Add a `spine_head/1` helper (walk `{:app, f, _}` to the head) to make "both sides meta-headed" a single decision (spec §3.2 bullet 1). Guard: only fire when the head is an UNSOLVED meta (solved metas are `force`d away upstream).

- [ ] **Step 4: Wire the drain at both telescope boundaries.** In `finish_ctor_app` (:3271) and `finish_global_app` (:3651), immediately BEFORE `all = Enum.map(chosen, &Unify.zonk(&1, mctx))`, insert:
```elixir
case Unify.drain_constraints(mctx) do
  {:ok, mctx} -> # fall through to the existing zonk + has_meta? gate with drained mctx
  {:error, reason} -> {:error, {:unsolved_constraints, reason}}  # or the ctor/global name-tagged error
end
```
Rebind `mctx` to the drained one so the subsequent `zonk` uses solutions found during drain.

- [ ] **Step 5: Green — verify the flip + no regression.** `mix cure.oracle postpone`:
  - `postpone01`, `postpone02` → now `same` (accept/accept).
  - `postpone03` (strong-rigid cycle) → still reject/reject.
  - `postpone04` (never-pinned) → still reject/reject.
  Update `verdicts.json` via the oracle (never by hand). Then `mix test test/oracle_replay_test.exs` — Expected: PASS. Then run the existing dep/guard/match oracle replays are covered by the single replay test (it auto-discovers all `test/oracle/*`) — confirm no other cluster regressed.

- [ ] **Step 6: Run the unit tests too.** `mix test test/cure/elab/unify_postpone_test.exs` — Expected: PASS (Task 2–4 behavior intact).

- [ ] **Step 7: Commit.**
```bash
git add -- lib/cure/elab/unify.ex lib/cure/elab/elaborator.ex test/oracle/postpone/
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(elab): postpone flex-flex + weak-rigid occurs, drain at telescope boundary (#11)"
```

---

## Task 6 — Roadmap update + final verification gate

**Files:**
- Modify: `docs/superpowers/specs/2026-07-02-idris-parity-roadmap.md` (§2 row #11)

- [ ] **Step 1: Update roadmap row #11** from open → **landed**: name the four probes (`postpone01`–`04`), the app-telescope granularity + the deferred definition-wide threading, the retry-all fixpoint, the weak/strong occurs split, and the no-TCB / kernel-backstop note. Mark the deferred items (definition-wide threading, pruning, Σ-flattening, blocker-keyed wakeup) as follow-ups.

- [ ] **Step 2: No-TCB verification.** `git diff --stat main -- lib/cure/core/` — Expected: EMPTY (no kernel change). If non-empty, STOP — a TCB change slipped in.

- [ ] **Step 3: Full suite, once, alone.** `mix test` — Expected: all green (including `test/oracle_replay_test.exs` and `test/cure/elab/unify_postpone_test.exs`). Record the pass count.

- [ ] **Step 4: Commit.**
```bash
git add -- docs/superpowers/specs/2026-07-02-idris-parity-roadmap.md
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "docs(spec): #11 postponed constraints landed (app-telescope cut) — roadmap update"
```

---

## Self-Review

**Spec coverage:** §2 risk gate → Task 1. §3.1 queue → Task 2. §3.3 occurs_rigidity → Task 3. §3.4 drain → Task 4. §3.2 triggers + §3.5 telescope-boundary integration → Task 5. §5 probes → Tasks 1 & 5. §9 DoD (no-TCB, roadmap, full suite) → Task 6. §3.5 prerequisite resolved by committing to app-telescope granularity (deferring definition-wide threading) — reflected in Task 5 Step 4 and the roadmap update.

**Placeholder scan:** The `occurs_rigidity` per-shape recursion (Task 3 Step 3) and the `solve_strengthened` depth-threading (Task 5 Step 2) are the two spots left as "pin against the code during implementation" — both name the exact enumeration/call site to pin against (unify.ex:354–377; the `solve/4` call site), so they are directed, not vague. The probe CONTENT (Task 1) is genuinely discovery-driven (the whole point of the gate) — acceptable.

**Type consistency:** constraint tuple `{a, b, depth, sig, reason}` is identical across §3.1, Task 2, Task 4, Task 5. `drain_constraints/1 :: {:ok, ctx} | {:error, reason}` consistent. `occurs_rigidity/3 :: :strong | :weak | :none` consistent across Tasks 3 & 5.

**Risk:** Task 1 may HALT (no reachable divergence). That is a designed, acceptable outcome — the plan makes it explicit rather than building blind. Task 5's flex-flex trigger may need the `spine_head` helper; if `postpone01` proves unreachable at telescope granularity, `postpone02` (bare weak-occurs) carries the gate and `postpone01` is deferred with pruning (spec §8).
