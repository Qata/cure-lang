# Weak-Head Normalization Before Unification (#11, pivoted) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans (inline) to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Make Cure's elaborator unifier reduce both sides to weak-head normal form before structural comparison, so reducible redexes (e.g. `plus(Z, ?m)` → `?m`) are handled, reaching dependent-inference inputs Idris accepts. E-layer only; reuses the trusted `Normalise.whnf` unchanged; no TCB.

**Architecture:** In `Cure.Elab.Unify`, add a meta-aware whnf (substitute unsolved metavariables with opaque-global placeholders → `Normalise.whnf` → reverse-map) and call it on both sides at the start of the unify step, recursing on the reduced terms only if a side changed (Lean's reduce-then-recurse loop). No `MetaCtx` change, no constraint queue, no `occurs?` change.

**Tech Stack:** Elixir; Cure compiler (`lib/cure/elab/unify.ex`, `lib/cure/core/normalise.ex` — read-only reuse); differential oracle (`mix cure.oracle`, `idris2 --check`); ExUnit.

## Global Constraints

- **Layer: E only.** Touch `lib/cure/elab/unify.ex`, `test/**`, `docs/**`. **No `lib/cure/core/*` diff** (verify at the gate: `git diff --stat main -- lib/cure/core/` is empty). No TCB, no Antigen antibody (kernel re-checks; reduction reused is already trusted).
- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO `Co-Authored-By`, no Claude signature.
- **Explicit-pathspec staging only:** `git add -- <path>`. NEVER `git add -A`/`.` (a concurrent agent may share this worktree).
- **One build at a time.** Never two `mix` suites concurrently. Prefer scoped `mix test <file>`; full `mix test` once, alone, at the gate.
- **Oracle discipline:** verdicts from `mix cure.oracle whnf`, never hand-written; freeze into `test/oracle/whnf/verdicts.json`; `mix test test/oracle_replay_test.exs` green before any fixture-touching commit.
- **`mix run` unavailable** for probes (throws `unknown registry: Cure.Pipeline.Events.Registry`). Dump Cure reasons via a throwaway test-env module calling `Cure.Elab.Program.elaborate/1`.
- **Tests immutable once green**; behavioral.

## File Structure

- `lib/cure/elab/unify.ex` — NEW `whnf_meta_aware/3` (or `/4`) private helper in the `Unify` module; a reduction step inserted into `unify_d/5` (unify.ex:101) between `force_d` and `do_unify`.
- `test/cure/elab/unify_whnf_test.exs` — NEW unit tests for the meta-aware whnf helper.
- `test/oracle/whnf/whnf0{1,2,3,4}_*.{cure,idr}` + `verdicts.json` — NEW oracle probes.

---

## Task 1 — Author + freeze the oracle probes (gate already passed empirically)

The reachability gate passed during the pivot (verified `cure=reject
{:cannot_unify, plus(Z,?0), S(Z)}` / `idris=accept`). This task re-creates the
probes cleanly under `test/oracle/whnf/`, adds the two negatives, and freezes.

**Files:**
- Create: `test/oracle/whnf/whnf01_computed_index.{cure,idr}`,
  `whnf02_two_arg_shared_index.{cure,idr}`, `whnf03_stuck_meta_neg.{cure,idr}`,
  `whnf04_concrete_mismatch_neg.{cure,idr}`
- Create (throwaway, deleted at task end): `test/zzz_probe_test.exs`

**Interfaces:**
- Produces: frozen `test/oracle/whnf/verdicts.json` — `whnf01`/`whnf02`
  `cure=reject,idris=accept` (pre-fix); `whnf03`/`whnf04` `reject/reject`.
  Consumed as the red/regression tests in Task 3.

- [ ] **Step 1: Author `whnf01_computed_index`** (verified confound-free during pivot):
```
# whnf01_computed_index.cure
mod Whnf01
  type Nat = Z | S(Nat)
  fn plus(a: Nat, b: Nat) -> Nat = match a
    Z() -> b
    S(k) -> S(plus(k, b))
  type Vec indices (n: Nat)
    vz : Vec(Z)
    vs : Vec(k) -> Vec(S(k))
  fn needlen({m: Nat}, v: Vec(plus(Z, m)), r: Nat) -> Nat = r
  fn use() -> Nat = needlen(vs(vz()), Z())
end
```
```
-- whnf01_computed_index.idr
%default total
data Nat2 = Z | S Nat2
plus : Nat2 -> Nat2 -> Nat2
plus Z n = n
plus (S k) n = S (plus k n)
data Vec : Nat2 -> Type where
  VZ : Vec Z
  VS : Vec k -> Vec (S k)
needlen : {m : Nat2} -> Vec (plus Z m) -> Nat2 -> Nat2
needlen _ r = r
use : Nat2
use = needlen (VS VZ) Z
```

- [ ] **Step 2: Author `whnf02_two_arg_shared_index`** — same as `whnf01` but the
  function is `twovec({m}, w: Vec(plus(Z, m)), v: Vec(m), r: Nat) -> Nat = r` and
  `use() = twovec(vs(vz()), vs(vz()), Z())`; `.idr` transliterates identically
  (`twovec : {m} -> Vec (plus Z m) -> Vec m -> Nat2 -> Nat2`).

- [ ] **Step 3: Author `whnf03_stuck_meta_neg`** — the genuinely-stuck negative:
  `stuck({m}, v: Vec(plus(m, Z)), r: Nat) -> Nat = r`, `use() = stuck(vs(vz()),
  Z())`. `plus(m, Z)` is stuck on `?m` (meta in the scrutinee position) — nothing
  determines `?m`. `.idr` transliterates. EXPECT reject/reject (Idris: unsolved
  `m`; Cure: `cannot_unify`/unsolved-meta on the stuck neutral).

- [ ] **Step 4: Author `whnf04_concrete_mismatch_neg`** — reduction succeeds but
  reduced forms differ: `mismatch(v: Vec(plus(Z, Z))) -> Nat = Z()` applied to a
  `vs(vz()) : Vec(S(Z))`, forcing `plus(Z,Z)=Z =? S(Z)` → genuine disequality.
  (No implicit needed; both sides concrete.) `.idr` transliterates. EXPECT
  reject/reject. Guards that whnf-then-compare still rejects real mismatches.

- [ ] **Step 5: Run the oracle.** `mix cure.oracle whnf` → writes
  `test/oracle/whnf/verdicts.json`.

- [ ] **Step 6: Verify reasons (not confounds).** Throwaway test dumping
  `Cure.Elab.Program.elaborate(File.read!("…cure"))` for each probe:
```elixir
# test/zzz_probe_test.exs
defmodule ZzzProbeTest do
  use ExUnit.Case
  for n <- ~w(whnf01_computed_index whnf02_two_arg_shared_index whnf03_stuck_meta_neg whnf04_concrete_mismatch_neg) do
    test "reason #{n}" do
      IO.inspect(Cure.Elab.Program.elaborate(File.read!("test/oracle/whnf/#{unquote(n)}.cure")),
        label: ">>> #{unquote(n)}", limit: :infinity)
    end
  end
end
```
`mix test test/zzz_probe_test.exs`. CONFIRM: `whnf01`/`whnf02` reject with a
`{:cannot_unify, plus(Z, {:meta,_}), …}` / `{:index_mismatch, …}` reason (NOT
erasure `{:erased_used_relevantly}` — do not return the implicit; NOT
`{:unsolved_metavariables, :vz}` — the monomorphic `Vec` has no element-type
meta). `whnf03` reject with a stuck-`plus(m,Z)` unify/unsolved reason; `whnf04`
reject with a `Z =? S(Z)` mismatch. If any reason is a confound, fix the probe
and re-run before freezing.

- [ ] **Step 7: Delete the throwaway test** (`rm test/zzz_probe_test.exs`; never commit it).

- [ ] **Step 8: Replay + commit.** `mix test test/oracle_replay_test.exs`
  (Expected PASS — fixture keys match the four paired files). Then:
```bash
git add -- test/oracle/whnf/
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "test(oracle): #11 whnf probes — computed-index inference (reject; idris accept)"
```

---

## Task 2 — Meta-aware whnf helper (TDD unit)

**Files:**
- Modify: `lib/cure/elab/unify.ex` (Unify module — add `whnf_meta_aware/…`)
- Test: `test/cure/elab/unify_whnf_test.exs`

**Interfaces:**
- Consumes: `Cure.Core.Normalise.whnf/3` (or the lower `Eval.eval` +
  `Normalise.whnf_value/3` + `Quote.reify/2` trio — pin during Step 3 against the
  actual signatures; `Normalise.whnf/3` at normalise.ex:26 takes a
  `Core.Context.t()`); `MetaCtx` solutions (via existing `zonk/2`).
- Produces: `Unify.whnf_meta_aware(term, ctx, sig)` (and `depth` if needed) ::
  `Core.Term.t()` — the whnf of `term` with unsolved metas preserved as neutrals,
  or the (zonked) input unchanged on `:fuel_exhausted`/any anomaly. Consumed by
  Task 3.

- [ ] **Step 1: Write failing unit tests.**
```elixir
# test/cure/elab/unify_whnf_test.exs
defmodule Cure.Elab.UnifyWhnfTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{MetaCtx, Unify}
  # Build a signature with `plus` defined (pin exact sig-construction against how
  # Program/Declarations build the signature — Step 3). `sig`/`ctx` fixtures here.

  test "whnf reduces plus(Z, ?m) to ?m (meta passes through)" do
    # plus(Z, ?0) must reduce to {:meta, 0}
    t = {:app, {:app, {:global, :plus}, {:ctor, :Z, []}}, {:meta, 0}}
    assert Unify.whnf_meta_aware(t, ctx_with_plus(), sig_with_plus()) == {:meta, 0}
  end

  test "whnf leaves plus(?m, Z) stuck (meta in scrutinee position)" do
    t = {:app, {:app, {:global, :plus}, {:meta, 0}}, {:ctor, :Z, []}}
    assert Unify.whnf_meta_aware(t, ctx_with_plus(), sig_with_plus()) == t
  end

  test "whnf on a meta-free reducible term matches Normalise.whnf" do
    t = {:app, {:app, {:global, :plus}, {:ctor, :Z, []}}, {:ctor, :S, [{:ctor, :Z, []}]}}
    assert Unify.whnf_meta_aware(t, ctx_with_plus(), sig_with_plus()) == {:ctor, :S, [{:ctor, :Z, []}]}
  end
end
```
(The `ctx_with_plus`/`sig_with_plus` fixtures build a Core context/signature in
which `plus` is a certified-total global — pin their construction in Step 3 by
reading how `test/cure/core/*` or `test/oracle` build signatures; if that is
heavyweight, drive these three cases through `Cure.Elab.Program.elaborate/1` on a
tiny module instead, asserting acceptance — but a direct unit on the helper is
preferred.)

- [ ] **Step 2: Run, verify fail.** `mix test test/cure/elab/unify_whnf_test.exs`
  — Expected: FAIL (`whnf_meta_aware/3` undefined).

- [ ] **Step 3: Implement `whnf_meta_aware/…`.**
  1. `z = zonk(term, ctx)` (apply known solutions).
  2. `{subst, map} = replace_metas_with_placeholders(z)` — walk `z`; each
     remaining `{:meta, id}` → `{:global, :"$meta$#{id}"}`, recording `id` in
     `map` (a MapSet or map placeholder-atom→id; the atom prefix `"$meta$"` is not
     a legal Cure identifier, so no collision with a user global).
  3. `reduced = Normalise.whnf(core_ctx, subst, delta: :certified, stuck_cases: :preserve)`
     — build `core_ctx` from `sig` (+ `depth` neutral env) per normalise.ex:26-33.
     On `:fuel_exhausted` → return `z` (fallback).
  4. `restore_placeholders(reduced)` — walk; each `{:global, :"$meta$" <> _}` →
     `{:meta, id}` via `map` (or by parsing the id out of the atom). Return it.
  Structural walks (steps 2 & 4) must cover every subterm-bearing Core shape —
  mirror `Unify.zonk/2`'s generic tuple/list walk (unify.ex:407-414) so no shape
  is missed.

- [ ] **Step 4: Run, verify pass.** `mix test test/cure/elab/unify_whnf_test.exs`
  — Expected: PASS (all three).

- [ ] **Step 5: Commit.**
```bash
git add -- lib/cure/elab/unify.ex test/cure/elab/unify_whnf_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(elab): meta-aware whnf (placeholder reuse of Normalise.whnf) (#11)"
```

---

## Task 3 — Wire whnf into the unify step (oracle red-green)

**Files:**
- Modify: `lib/cure/elab/unify.ex` (`unify_d/5` at :101)
- Test (red): the Task-1 oracle probes.

**Interfaces:**
- Consumes: `whnf_meta_aware/…` (Task 2).
- Produces: `whnf01`/`whnf02` flip to accept; `whnf03`/`whnf04` stay reject.

- [ ] **Step 1: Red — probes still reject.** `mix cure.oracle whnf`; confirm
  `whnf01`/`whnf02` still `cure=reject` (standing red before the wire-in).

- [ ] **Step 2: Wire whnf into `unify_d/5`.** Currently:
  `do_unify(force_d(t1, ctx, depth), force_d(t2, ctx, depth), ctx, sig, depth)`.
  Change to: whnf both forced sides via `whnf_meta_aware`; if EITHER changed,
  re-enter `unify_d` on the reduced pair (bounded: whnf is idempotent, so the
  recursion terminates when neither side changes); else fall through to
  `do_unify` exactly as today. Guard against infinite recursion by comparing
  pre/post terms (`reduced == forced` → no change → structural). Only reduce when
  `sig != nil` (whnf needs the signature; `sig == nil` callers keep today's
  behavior).

- [ ] **Step 3: Green — verify the flip + negatives hold.** `mix cure.oracle whnf`:
  `whnf01`, `whnf02` → `cure=accept` (now `same`); `whnf03`, `whnf04` → still
  `reject/reject`. Update `verdicts.json` via the oracle (never by hand).

- [ ] **Step 4: Replay + no regression.** `mix test test/oracle_replay_test.exs`
  (auto-discovers ALL `test/oracle/*` — confirms no other cluster: dep, guard,
  match, rewrite, with, etc. regressed). Then the unit tests:
  `mix test test/cure/elab/unify_whnf_test.exs test/cure/elab/unify_test.exs`.
  Also run the unifier-adjacent suites that exercise `do_unify`/`solve`:
  `mix test test/cure/elab/unify_meta_completeness_test.exs test/cure/elab/miller_unify_test.exs test/cure/elab/higher_order_unify_test.exs`
  (pin the exact existing filenames by `ls test/cure/elab/`; run whichever exist).
  Expected: all PASS.

- [ ] **Step 5: Commit.**
```bash
git add -- lib/cure/elab/unify.ex test/oracle/whnf/
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(elab): whnf both sides before structural unification (#11)"
```

---

## Task 4 — Roadmap update + final verification gate

**Files:**
- Modify: `docs/superpowers/specs/2026-07-02-idris-parity-roadmap.md` (§2 row #11)

- [ ] **Step 1: Update roadmap row #11** → **landed (whnf-before-compare)**: name
  the four `whnf` probes, the meta-aware-whnf mechanism (placeholder reuse of the
  trusted `Normalise.whnf`, no TCB), the kernel-backstop note, and that
  postponement is deferred as a secondary follow-up. Note the pivot from the
  superseded postponement design.

- [ ] **Step 2: No-TCB verification.** `git diff --stat main -- lib/cure/core/`
  — Expected: EMPTY. If non-empty, STOP.

- [ ] **Step 3: Full suite, once, alone.** `mix test` — Expected: all green
  (oracle replay + unit + everything). Record the pass count.

- [ ] **Step 4: Commit.**
```bash
git add -- docs/superpowers/specs/2026-07-02-idris-parity-roadmap.md
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "docs(spec): #11 whnf-before-unification landed — roadmap update"
```

---

## Self-Review

**Spec coverage:** §2 probes → Task 1. §3.2 meta-aware whnf → Task 2. §3.1 wire
at unify step → Task 3. §9 DoD (no-TCB, roadmap, full suite) → Task 4. §3.4
does-not-fix (stuck) → `whnf03` negative. §3.2 fuel fallback → Task 2 Step 3 +
unit intent.

**Placeholder scan:** The two "pin against the code" spots — the `core_ctx`
construction from `sig`+`depth` (Task 2 Step 3) and the unit-test signature
fixture (Task 2 Step 1) — both name the exact functions to pin against
(`Normalise.whnf` normalise.ex:26-33; `Program`/`Declarations` sig-building).
Directed, not vague.

**Type consistency:** `whnf_meta_aware(term, ctx, sig) :: Core.Term.t()`
consistent across Tasks 2 & 3. Placeholder atom prefix `"$meta$"` consistent
(sub + restore). Recurse-on-change guard (`reduced == forced`) consistent.

**Risk:** the `core_ctx`/`depth` plumbing for `Normalise.whnf` is the one
non-trivial unknown; Task 2's unit tests (which build the exact `plus(Z,?m)`
term) force it correct via red-green before any wiring. If `Normalise.whnf`
cannot be driven at the needed depth cleanly, the fallback (`return zonked input`)
degrades gracefully to today's behavior — never a crash or a wrong accept.
