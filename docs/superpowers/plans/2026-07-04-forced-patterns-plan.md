# Forced / Dot Patterns + Forced-Argument Erasure — Implementation Plan (#5)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make Cure accept dependent matches where matching a constructor forces an equation between the scrutinee's index variables (Agda's `unifyIndices` Solution step), and add explicit `.e` dot-pattern syntax plus forced-argument erasure.

**Architecture:** Four layers, in dependency order. **K** — teach the kernel index unifier (`bind_index`/`unify_one` in `kernel.ex`) to *resolve-before-bind* a same-key conflict into a forced scrutinee-variable substitution instead of silently dropping it as `:undecided`. **E** — route that forced substitution into branch context+goal before body elaboration (this is what flips the reach probes), elaborate `{:forced_pattern,…}` dot patterns, and erase forced arguments in `Cure.Elab.Erase`. **P** — add a leading-`:dot` prefix case to the shared expression parser producing `{:forced_pattern,…}`, guarded by a semantic pattern-position check. Verified by the differential oracle (cluster `dotpat`) plus kernel/parser/erase unit tests and the mandatory Antigen TCB gate.

**Tech Stack:** Elixir; Cure dependent elaborator (`lib/cure/elab/*`) + kernel (`lib/cure/core/*`) + parser (`lib/cure/compiler/parser.ex`); differential oracle (`mix cure.oracle`, `idris2 --check`); Antigen (`lib/antigen/*`, `test/antigen/*`).

## Global Constraints

- **Source of truth:** the hardened spec `docs/superpowers/specs/2026-07-04-forced-patterns-design.md`. Read it before Task 2.
- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO `Co-Authored-By`, no Claude signature.
- **Explicit-pathspec staging only:** `git add -- <path>` / `git commit -- <path>`; NEVER `git add -A`/`git add .` (a concurrent agent may share this worktree).
- **One build at a time:** never run two `mix` suites concurrently. Prefer scoped `mix test <file>`; run the full suite once, alone, only at the gates (Task 4, Task 8).
- **TCB HARD-STOP:** the K change (Task 2) touches `lib/cure/core/kernel.ex`. It is pre-approved *only because it aligns `unify_indices` with Agda's Solution step* and *only conditional on passing Task 4's full gate* (new Antigen antibody + full Antigen suite + full test suite). If Task 4 fails, STOP and report — do not paper over.
- **Tests immutable once green.** Behavioral, not implementation-coupled.
- **Branch:** stay on `autopilot/lean-shape-matching` in this worktree.
- **`dp01`/`dp02` are blocked** by the independent auto-generalization defect (spec §1.2) — they are committed to the cluster marked `cure_stricter` with a reason and are NOT expected to flip in this plan. `dp01b` is the primary reach probe.
- **macOS has no `timeout`.** To bound a possibly-hanging elaboration, wrap it in `Task.async`/`Task.yield(t, ms)` + `Task.shutdown(t, :brutal_kill)` (never a shell `timeout`).

---

### Task 1: `dotpat` oracle cluster — red baseline

Author the probe fixtures and freeze today's (pre-fix) verdicts, establishing the red baseline. No production code changes.

**Files:**
- Create: `test/oracle/dotpat/dp01b_forced_eq_min.cure` + `.idr` (primary reach probe)
- Create: `test/oracle/dotpat/dp03_vect_head.cure` + `.idr` (reach probe, monomorphic)
- Create: `test/oracle/dotpat/dp04_absurd_distinct.cure` + `.idr` (regression guard — already passes)
- Create: `test/oracle/dotpat/dp01_forced_eq.cure` + `.idr`, `dp02_explicit_dot.cure` + `.idr` (blocked — kept as `cure_stricter`)
- Generated: `test/oracle/dotpat/verdicts.json` (via `mix cure.oracle dotpat`)

**Interfaces:**
- Produces: the `dotpat` cluster consumed by `test/oracle_replay_test.exs` (auto-discovered) and by later tasks' re-runs.

- [ ] **Step 1: Write `dp01b` (the non-confounded reach probe).**

`test/oracle/dotpat/dp01b_forced_eq_min.cure`:
```cure
mod Dp01b
  type Nat = Z | S(Nat)
  type SameLen indices (n: Nat, m: Nat)
    same : SameLen(k, k)
  fn cong({a: Nat}, {b: Nat}, p: SameLen(a, b)) -> SameLen(S(a), S(b)) = match p
    same() -> same()
end
```

`test/oracle/dotpat/dp01b_forced_eq_min.idr` — **faithful** form (spec §1.2 caveat: keep `a`/`b` implicit; do NOT spell them as separately-named top-level LHS patterns, which Idris rejects for an unrelated naming quirk):
```idris
%default total

data Nat2 = Z | S Nat2

data SameLen : Nat2 -> Nat2 -> Type where
  Same : SameLen k k

cong : {a : Nat2} -> {b : Nat2} -> SameLen a b -> SameLen (S a) (S b)
cong Same = Same
```

- [ ] **Step 2: Write `dp03` (Vec head — length index forces `S n`).**

`test/oracle/dotpat/dp03_vect_head.cure`:
```cure
mod Dp03
  type Nat = Z | S(Nat)
  type Vec(t: Type) indices (n: Nat)
    vnil : Vec(t, Z)
    vcons : (h: t) -> (r: Vec(t, k)) -> Vec(t, S(k))
  fn vhead({n: Nat}, v: Vec(Nat, S(n))) -> Nat = match v
    vcons(h, r) -> h
end
```
`test/oracle/dotpat/dp03_vect_head.idr`:
```idris
%default total

data Nat2 = Z | S Nat2

data Vec : Nat2 -> Type -> Type where
  VNil : Vec Z a
  VCons : a -> Vec k a -> Vec (S k) a

vhead : {n : Nat2} -> Vec (S n) Nat2 -> Nat2
vhead (VCons h r) = h
```
> Note: `Type`-param family, but `vhead` matches only `vcons` (non-empty). If `dp03` trips the auto-generalization defect at *declaration* time (Vec's `vcons` repeats no free index var, so it should be fine — `vcons`'s result index `S(k)` uses `k` once), keep it; if it unexpectedly fails at declaration, downgrade it to a monomorphic `Vec` over a fixed element type in Step 6 triage and note it.

- [ ] **Step 3: Write `dp04` (absurd/distinct — regression guard, already passing).**

`test/oracle/dotpat/dp04_absurd_distinct.cure`: a total function matching a `Vec` known to be non-empty (`Vec(Nat, S(n))`) that only lists the `vcons` branch and omits `vnil` — the `vnil` branch's result index `Z` clashes with the scrutinee index `S(n)`, so coverage accepts without a `vnil` arm via the existing Conflict clause:
```cure
mod Dp04
  type Nat = Z | S(Nat)
  type Vec(t: Type) indices (n: Nat)
    vnil : Vec(t, Z)
    vcons : (h: t) -> (r: Vec(t, k)) -> Vec(t, S(k))
  fn total_head({n: Nat}, v: Vec(Nat, S(n))) -> Nat = match v
    vcons(h, r) -> h
end
```
`.idr` analogue with `vhead (VCons h r) = h` and no `VNil` clause (Idris accepts by impossibility).
> `dp04` and `dp03` may be structurally identical; if so, keep only `dp03` and drop `dp04`, recording in the commit message that the Conflict-clause guard is already covered by `dp03`. Decide during Step 6 based on the actual verdicts.

- [ ] **Step 4: Write `dp01`/`dp02` (blocked) fixtures.**

`dp01_forced_eq.cure` = the spec §1.1 `Dp01` source verbatim. `dp02_explicit_dot.cure` = same but the forced index written as a dot pattern once §4.2 lands (for now, a copy of `dp01` with a comment `# TODO: dot syntax after Task 5`). Both `.idr` files use the faithful implicit form. These are expected `reject`(cure)/`accept`(idris) today.

- [ ] **Step 5: Run the oracle to generate verdicts.**

Run: `mix cure.oracle dotpat`
Expected: `dp01b` `cure=reject` (`{:unsolved_metavariables, _}`) / `idris=accept`; `dp03` `cure=reject`/`idris=accept`; `dp04` `cure=accept`/`idris=accept`; `dp01`/`dp02` `cure=reject`/`idris=accept`.

- [ ] **Step 6: Triage + set relations in `verdicts.json`.**

For each `reject`/`accept` divergence, set `relation: "cure_stricter"` with an honest `reason`:
- `dp01b`: `"forced-pattern gap (#5): matching `same` should force b:=a but the elaborator drops the equation; fixed by Task 2+3"`.
- `dp03`: `"forced-index gap (#5): vcons match should force the length index; fixed by Task 2+3"`.
- `dp01`/`dp02`: `"blocked by the independent auto-generalization defect (spec §1.2), NOT by forced patterns; do not flip in #5"`.
- `dp04` (if kept): `relation: "same"` (already `accept`/`accept`).

Confirm no `cure=accept`/`idris=reject` anywhere (that would be a soundness surprise — STOP and report if seen).

- [ ] **Step 7: Replay green, then commit.**

Run: `mix test test/oracle_replay_test.exs`
Expected: PASS (the `cure_stricter` entries are consistent because each has a reason + `cure=reject`).
```bash
git add -- test/oracle/dotpat/
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(oracle): dotpat cluster — forced-pattern reach probes (red baseline) (#5)" -- test/oracle/dotpat/
```

---

### Task 2: K — resolve-before-bind Solution step in the kernel unifier (TCB)

Teach `bind_index` to resolve a same-key conflict by unifying old-vs-new instead of degrading to `:undecided`, producing a forced scrutinee-variable substitution. Kernel unit tests are the red-green here (the oracle probe does not flip until Task 3).

**Files:**
- Modify: `lib/cure/core/kernel.ex` (`bind_index/3` → `/4`, its call sites in `unify_one`, and the `reduce_index_pairs`/`unify_spine` threading; lines ~801-859)
- Test: `test/cure/core/unify_indices_test.exs` (create)

**Interfaces:**
- Consumes: nothing new.
- Produces: `unify_indices/4` verdict `{:solved, subst}` where `subst` may now contain **scrutinee-var keys** (`key >= arity`) mapping to a forced term, in addition to the existing ctor-arg keys (`key < arity`). Contract otherwise unchanged (`:trivial`/`:impossible` cases preserved).

- [ ] **Step 1: Write the failing kernel unit test.**

`test/cure/core/unify_indices_test.exs`. `unify_indices/4` is private; test it through the public `branch_unify/4` (`kernel.ex:770`), which reuses it. Build a context and a `SameLen`-shaped signature via `Cure.Elab.Program.elaborate/1` of the `Dp01b` module (returns the `Core.Env`), then call `Kernel.branch_unify(ctx, :SameLen, :same, scrut_index_values)` where the scrutinee indices are two distinct outer neutral vars `a`,`b`.

```elixir
defmodule Cure.Core.UnifyIndicesTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Kernel, Context}
  alias Cure.Elab.Program

  @src "mod M\n  type Nat = Z | S(Nat)\n  type SameLen indices (n: Nat, m: Nat)\n    same : SameLen(k, k)\nend\n"

  defp sig, do: (fn -> {:ok, s} = Program.elaborate(@src); s end).()

  test "matching `same : SameLen(k,k)` against SameLen(a,b) forces b := a" do
    s = sig()
    # ctx with two outer vars a=(:var,0), b=(:var,1) of type Nat, over signature s.
    ctx = Context.new(s) |> Context.push_var(...Nat...) |> Context.push_var(...Nat...)
    # scrutinee index VALUES for [a, b] in ctx (neutral vars), most-recent-first per branch_unify.
    scrut = [ {:vneutral, {:nvar, 0}}, {:vneutral, {:nvar, 1}} ]
    assert {:solved, subst} = Kernel.branch_unify(ctx, :SameLen, :same, scrut)
    # `same` has arity 1 (the implicit `k`); the forced entry keys the OUTER var (>= arity).
    # Exactly one of a/b is forced to the other; assert a forced scrutinee-var entry exists.
    forced = subst |> Map.to_list() |> Enum.filter(fn {k, _v} -> k >= 1 end)
    assert forced != []
    assert {_k, {:var, _}} = hd(forced)   # forced to the other scrutinee var
  end
end
```
> The executor must fill the `Context.new/push_var` calls with the real API (check `lib/cure/core/context.ex` for the constructor + `push_var`/`extend` and the `Nat` type value; mirror `test/cure/elab/unify_whnf_test.exs`'s signature-building style). The behavioral assertion — a forced `key >= arity` entry appears — is the immutable contract.

- [ ] **Step 2: Run it — verify RED.**

Run: `mix test test/cure/core/unify_indices_test.exs`
Expected: FAIL — today `bind_index(0, b, %{0 => a})` returns `:undecided` (kernel.ex:855), so `subst = %{0 => a}` has no `key >= arity` forced entry.

- [ ] **Step 3: Implement resolve-before-bind.**

Thread `arity` into `bind_index` (rename to `bind_index/4`) and replace the `true -> :undecided` same-key branch (kernel.ex:855) with a recursive resolve:

```elixir
defp unify_one({:var, i}, s, arity, subst) when i < arity, do: bind_index(i, s, arity, subst)
defp unify_one(r, {:var, j}, arity, subst) when j >= arity, do: bind_index(j, r, arity, subst)
# ... other unify_one clauses unchanged ...

defp bind_index(key, term, arity, subst) do
  cond do
    occurs_index?(key, term) -> :undecided
    Map.has_key?(subst, key) ->
      old = Map.get(subst, key)
      cond do
        old == term -> {:ok, subst}
        rigid_index?(old) and rigid_index?(term) and head_key(old) != head_key(term) -> :impossible
        true ->
          # Resolve-before-bind (Agda Solution step): the key is already pinned to
          # `old`, so this pair really asserts `old =? term`. Re-unify them; for two
          # distinct scrutinee vars this routes through unify_one clause 2 and binds
          # the outer var (a forced equation). Terminates: see Task 4 measure (b).
          unify_one(old, term, arity, subst)
      end
    true -> {:ok, Map.put(subst, key, term)}
  end
end
```
> All existing `bind_index(k, t, subst)` call sites become `bind_index(k, t, arity, subst)`. No other clause changes. `unify_one(old, term, arity, subst)` for `old={:var,ja}` (ja>=arity), `term={:var,jb}` (jb>=arity) matches clause 2 → `bind_index(jb, {:var,ja}, arity, subst)` → fresh key → `{:ok, put jb=>a}` = forced `b ↦ a`.

- [ ] **Step 4: Run the unit test — verify GREEN.**

Run: `mix test test/cure/core/unify_indices_test.exs`
Expected: PASS.

- [ ] **Step 5: Add guard tests (occurs-cycle + injectivity + no-regression).**

Add to the same file: (a) an occurs-cycle case (`same : SameLen(k, S(k))`-style if expressible; else a hand-built index vector) asserting the verdict stays `{:solved,_}`-without-cycle or `:undecided`, never a cyclic bind; (b) a same-constructor injectivity case still decomposes; (c) a case with a genuine rigid-head clash still returns `:impossible`; (d) a plain ctor-arg-only match (e.g. `vcons`) still returns the same `{:solved, %{ctor-arg => term}}` as before (no forced entries when none are induced). Run the file; all PASS.

- [ ] **Step 6: Run the kernel + core test directory (scoped regression).**

Run: `mix test test/cure/core/`
Expected: PASS (no kernel regression). If any pre-existing core test changed verdict, STOP — the K change altered established behavior; investigate before proceeding.

- [ ] **Step 7: Commit.**
```bash
git add -- lib/cure/core/kernel.ex test/cure/core/unify_indices_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(kernel): resolve-before-bind forced-equation Solution step in unify_indices (#5)" -- lib/cure/core/kernel.ex test/cure/core/unify_indices_test.exs
```

---

### Task 3: E — route the forced substitution into branch context + goal

Make the elaborator apply forced scrutinee-var (`key >= arity`) substitution entries to the branch context and goal *before* elaborating the branch body, so the body's implicit-argument solve succeeds. This is the task that flips `dp01b`/`dp03`.

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` (`specialize_branch_context_subst/2` ~line 1287 and the branch-goal refinement that consumes the `branch_unify` verdict ~lines 1219/1701/2686)
- (Kernel side `specialize_branch_context/2` at `kernel.ex:885` already applies subst via `replace_branch_vars`; verify it handles `key >= arity` keys — if it already keys uniformly on `{:var, i}` it needs no change.)

**Interfaces:**
- Consumes: `{:solved, subst}` from Task 2 (now with forced `key >= arity` entries).
- Produces: branch bodies elaborated against a goal/context with the forced equation applied.

- [ ] **Step 1: Re-run the oracle — confirm `dp01b`/`dp03` still red (different reason).**

Run: `mix cure.oracle dotpat`
Expected: `dp01b`/`dp03` still `cure=reject`. The forced subst now exists (Task 2) but the elaborator does not yet route it, so the body's `{:unsolved_metavariables,_}` (or a conversion failure) persists. Capture the exact current error for `dp01b` with the bounded-`Task` harness (Global Constraints) — it is the RED marker for this task.

- [ ] **Step 2: Locate + read the branch-elaboration path.**

Read `elaborator.ex` around `specialize_branch_context_subst/2` (1285-1300), the `branch_unify` call sites (1219, 1701), and the branch-goal construction (2686+). Confirm whether `specialize_branch_context_subst` filters subst keys by range (only `< arity`) or applies all `{:var, k}` keys. The fix is to ensure **all** keys (including `>= arity` forced entries) are applied to (a) the branch context types and (b) the expected branch goal, before the body is elaborated.

- [ ] **Step 3: Implement the routing.**

Extend `specialize_branch_context_subst` (and the goal-refinement sibling) to apply forced scrutinee-var entries. If it currently rebuilds the context via `replace_branch_vars(term, subst)` keyed uniformly on `{:var,k}`, the change may be as small as removing a `k < arity` filter or extending the goal-substitution to use the same `subst`. Whatever the concrete shape, the outcome must be: in the `same()`/`vcons` branch, the goal `SameLen(S(a), S(b))` is refined to `SameLen(S(a), S(a))` (forced `b ↦ a`) so the body `same()` type-checks.

- [ ] **Step 4: Run the oracle — verify GREEN flip.**

Run: `mix cure.oracle dotpat`
Expected: `dp01b` `cure=accept`/`idris=accept`; `dp03` `cure=accept`/`idris=accept`. `dp01`/`dp02` still `reject` (blocked — unchanged). No `cure=accept`/`idris=reject`.

- [ ] **Step 5: Set relations `same`, replay, scoped elab regression.**

Edit `verdicts.json`: `dp01b`/`dp03` → `relation: "same"`, empty `reason`. Keep `dp01`/`dp02` as `cure_stricter` (blocked).
Run: `mix test test/oracle_replay_test.exs test/cure/elab/`
Expected: PASS — the flip holds AND no other cluster/elaborator test regresses. (`test/cure/elab/` covers the whnf/miller/dependent-match suites; a regression here means the forced-subst routing broke an existing match.)

- [ ] **Step 6: Commit.**
```bash
git add -- lib/cure/elab/elaborator.ex test/oracle/dotpat/verdicts.json
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): route forced scrutinee-var substitution into branch goal (#5)" -- lib/cure/elab/elaborator.ex test/oracle/dotpat/verdicts.json
```

---

### Task 4: TCB GATE — Antigen antibody + full Antigen + full suite

The K change (Task 2) is soundness-critical. This gate must pass before the feature is considered sound. **Run suites one at a time.**

**Files:**
- Create/modify: an Antigen antibody under `test/antigen/` (or `lib/antigen/`) targeting the refined `unify_indices` — follow the pattern of the existing antibody added for the bool_elim / lazy-unfolding TCB changes (grep `test/antigen/` for the most recent kernel-change antibody as the template).

**Interfaces:**
- Consumes: the refined `unify_indices` from Task 2.

- [ ] **Step 1: Write the antibody.**

The antibody must witness the spec §4.1 obligations:
- **Termination of the resolve-before-bind chase** — construct **chained** forced bindings (a scrutinee var forced through ≥2 intermediate already-bound keys in one branch), asserting `unify_indices` returns (does not loop). Use the bounded-`Task` harness to assert termination within a time budget.
- **No multi-key binding cycle** — construct two pairs that could mutually bind (`i ↦ {:var,j}` and a chase proposing `j ↦ {:var,i}`) and assert the verdict is not a cyclic substitution (either resolves consistently or `:undecided`/`:impossible`, never a subst with `i↦j` and `j↦i`).
- **No normal-form collapse** — assert that a forced entry is produced ONLY when the two indices are the same ctor-scope variable's image (property test over generated index vectors: if `unify_indices` returns a forced `key >= arity` entry `k ↦ t`, then substituting `t` for `k` makes the original two index vectors convertible). Reuse the project's StreamData-backed Antigen generator style.

- [ ] **Step 2: Run the antibody.**

Run: `mix test test/antigen/<new_antibody>_test.exs` (exact path per the file created)
Expected: PASS.

- [ ] **Step 3: Run the full Antigen suite (alone).**

Run: `mix test test/antigen/`
Expected: PASS. A failure here means the kernel change broke a metatheory invariant — STOP and report; do not proceed to surface layers.

- [ ] **Step 4: Run the full test suite (alone).**

Run: `mix test`
Expected: PASS (all prior green tests + the new ones). If any regression, STOP and diagnose before Task 5.

- [ ] **Step 5: Commit.**
```bash
git add -- test/antigen/<new_antibody>_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(antigen): antibody for forced-equation unify_indices (TCB gate) (#5)" -- test/antigen/<new_antibody>_test.exs
```

---

### Task 5: P — explicit `.e` dot-pattern syntax

Add a leading-`:dot` prefix case to the shared expression parser producing `{:forced_pattern, meta, expr}`, plus a semantic check rejecting it outside pattern positions.

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (`parse_prefix` `case token.type do` at ~203-338: add a `:dot ->` clause; and the pattern-consuming validation site named in Step 3)
- Test: `test/cure/compiler/dot_pattern_parse_test.exs` (create)

**Interfaces:**
- Produces: `{:forced_pattern, meta, expr_ast}` AST node in pattern position, consumed by Task 6.

- [ ] **Step 1: Write failing parser tests.**

`test/cure/compiler/dot_pattern_parse_test.exs`: (a) parsing a match arm `same(.a) -> ...` yields an arm whose pattern arg is `{:forced_pattern, _, {:identifier … "a"}}` (or the project's var-AST shape — check an existing parse test for the exact node); (b) `.(S(k))` parses the parenthesised compound form; (c) **negative**: a bare `.x` used as an ordinary *expression* (e.g. `let y = .x`) is rejected (`{:forced_pattern_not_in_pattern, _}` or the chosen error); (d) **non-regression**: `Std.String.from_int(5)` still parses to the existing `{:attribute_access,…}` chain, unaffected.

- [ ] **Step 2: Run — verify RED.**

Run: `mix test test/cure/compiler/dot_pattern_parse_test.exs`
Expected: FAIL — today a leading `.` hits the `parse_prefix` catch-all `{:unexpected_token,…}` (parser.ex:333-336).

- [ ] **Step 3: Implement the `:dot` prefix clause + semantic guard.**

Add to `parse_prefix`'s `case token.type do`:
```elixir
:dot ->
  {inner, state} = parse_forced_inner(advance(state))   # `.x` → var; `.(expr)` → parenthesised expr
  {{:forced_pattern, meta(token), inner}, state}
```
`parse_forced_inner` reads either a parenthesised `parse_expr` (`.(…)`) or a single primary (identifier/literal). Then add the **semantic** guard: at the site(s) that consume a parsed match-arm / clause pattern AST (find where arms are validated/lowered — grep for where `parse_match_arm`'s result is turned into elaborator input), reject a `{:forced_pattern,…}` that appears where an ordinary expression is expected, and (for Task 6) allow it only as a constructor-application argument in pattern position. Name that site in a code comment. Infix `.` (module paths) is untouched — it is handled in `parse_infix`'s `handle_infix_op` `:dot ->` (parser.ex:476-482) and never reaches this prefix clause.

- [ ] **Step 4: Run — verify GREEN.**

Run: `mix test test/cure/compiler/dot_pattern_parse_test.exs`
Expected: PASS (all four cases).

- [ ] **Step 5: Scoped parser regression + commit.**

Run: `mix test test/cure/compiler/`
Expected: PASS.
```bash
git add -- lib/cure/compiler/parser.ex test/cure/compiler/dot_pattern_parse_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser): leading-dot forced-pattern syntax (#5)" -- lib/cure/compiler/parser.ex test/cure/compiler/dot_pattern_parse_test.exs
```

---

### Task 6: E — elaborate `{:forced_pattern,…}` dot patterns

Elaborate a dot pattern at a constructor-argument position: elaborate its expression and assert convertibility with the value index-unification determined; reject on mismatch; bind no new variable; record the forced Core term.

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` (constructor-arm pattern elaboration — where a ctor pattern's argument patterns are processed)
- Create: `test/oracle/dotpat/dp02b_explicit_dot.cure` + `.idr` (positive, non-blocked `SameLen` shape with an explicit correct dot), `test/oracle/dotpat/dp06_dot_mismatch_neg.cure` + `.idr` (negative)

**Interfaces:**
- Consumes: `{:forced_pattern,…}` from Task 5; the forced value from Task 2's subst.
- Produces: `{:forced_pattern_mismatch, written, determined}` error on disagreement; forced positions recorded for Task 7.

- [ ] **Step 1: Write the probes (RED).**

`dp02b_explicit_dot.cure`: the `Dp01b` `cong` but matching `same()` with the forced index written explicitly, e.g. `same() -> ...` is already nullary; instead use a family where the forced position is an explicit ctor argument. Simplest: a `Vec`-cons whose length is written forced:
```cure
# a match arm that writes the forced length index as a dot, e.g.
#   vcons(.(S(k)), h, r) -> ...   (exact ctor shape depends on where the index sits)
```
If `SameLen`/`Vec` don't expose a natural argument-position dot, construct a small family whose constructor takes the forced index as an explicit argument. `dp06_dot_mismatch_neg.cure`: same, but the dot writes a value that unification does NOT determine (e.g. `.(Z)` where it must be `S(k)`), expected `reject`. `.idr` counterparts use Idris `.`-patterns or the impossible form.
Run `mix cure.oracle dotpat`; `dp02b` `reject` today (elaborator does not yet handle the node), `dp06` `reject`.

- [ ] **Step 2: Verify RED.**
Run: `mix test test/oracle_replay_test.exs` after setting `dp02b` `cure_stricter` — actually first just inspect `mix cure.oracle dotpat` output: `dp02b` `cure=reject`/`idris=accept`.

- [ ] **Step 3: Implement dot-pattern elaboration.**

In the constructor-arm pattern elaboration, when an argument pattern is `{:forced_pattern, _, expr}`: elaborate `expr` to a Core term `t` in the branch context; obtain the value `d` that index unification determined for that position (from the branch subst / the ctor's result-index at that position after applying subst); assert `Conv.conv?` (or the elaborator's convertibility helper) between `t` and `d`. Equal ⇒ accept, bind no variable, record the position as forced. Unequal ⇒ `{:error, {:forced_pattern_mismatch, t, d}}`.

- [ ] **Step 4: Verify GREEN.**
Run: `mix cure.oracle dotpat`
Expected: `dp02b` `cure=accept`/`idris=accept`; `dp06` `cure=reject`/`idris=reject`. Set `dp02b` → `same`, `dp06` → `same` (both agree). No `cure=accept`/`idris=reject`.

- [ ] **Step 5: Replay + scoped elab regression + commit.**
Run: `mix test test/oracle_replay_test.exs test/cure/elab/`
Expected: PASS.
```bash
git add -- lib/cure/elab/elaborator.ex test/oracle/dotpat/
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): elaborate forced (dot) patterns with convertibility check (#5)" -- lib/cure/elab/elaborator.ex test/oracle/dotpat/
```

---

### Task 7: E — forced-argument erasure in `Cure.Elab.Erase`

Extend the erasure pass so a forced constructor-argument position in a match branch is lowered to a wildcard (not bound, not scrutinised). Per-branch, not via the ctor's static `quantities`.

**Files:**
- Modify: `lib/cure/elab/erase.ex` (`erase/2`'s `{:case, s, m, branches}` clause, erase.ex:75-77; the branch triple `{cname, arity, body}` must carry or be joined to the per-branch forced-position set from Task 6)
- Test: `test/cure/elab/forced_erasure_test.exs` (create)

**Interfaces:**
- Consumes: the per-branch forced-position set recorded in Task 6.
- Produces: erased `{:case,…}` whose forced argument positions are wildcards.

- [ ] **Step 1: Write the failing erasure test.**

`test/cure/elab/forced_erasure_test.exs`: elaborate a program with a forced constructor argument to Core, run `Cure.Elab.Erase.erase/2`, and assert the resulting `{:case,…}` branch does NOT bind the forced position (e.g. the branch's pattern arity is reduced, or the forced slot is a wildcard marker — pin the exact representation to whatever Task 6 records). Behavioral assertion: the erased branch body does not reference a variable bound by the forced position, and the branch does not match on it.

- [ ] **Step 2: Verify RED.**
Run: `mix test test/cure/elab/forced_erasure_test.exs`
Expected: FAIL — today `erase/2`'s `{:case,…}` clause (erase.ex:76) preserves every branch's arity/bindings untouched.

- [ ] **Step 3: Implement per-branch forced erasure.**

Thread the forced-position set into the branch triple (extend `{cname, arity, body}` to `{cname, arity, body, forced_positions}` at construction in the elaborator + everywhere the triple is destructured, OR carry a side-table keyed by `{cname, branch_index}` — pin the smaller-diff option). In `erase/2`'s `{:case,…}` clause, for each branch drop/wildcard the forced positions so codegen (`compile_pattern_match`) receives a pattern that ignores them. Keep it **conservative**: only erase positions in the forced set; never touch a non-forced argument. If the triple shape changes, update `has_hole?/1`'s `{:case,…}` clause (erase.ex:100-101) and every other `{c, ar, b}` destructure to match.

- [ ] **Step 4: Verify GREEN.**
Run: `mix test test/cure/elab/forced_erasure_test.exs`
Expected: PASS.

- [ ] **Step 5: End-to-end run-on-unix check (optional but preferred).**

If a forced-argument program can be made executable, build+run it on generic-unix AtomVM (`phase35/run-on-unix.sh` or `phase1/cure-avm run`) and confirm correct output with the arg erased. If not readily executable, note it and rely on the Core-level assertion in Step 1.

- [ ] **Step 6: Scoped regression + commit.**
Run: `mix test test/cure/elab/`
Expected: PASS.
```bash
git add -- lib/cure/elab/erase.ex test/cure/elab/forced_erasure_test.exs
# plus any elaborator.ex change needed to thread forced_positions:
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(erase): erase forced constructor arguments per match branch (#5)" -- lib/cure/elab/erase.ex test/cure/elab/forced_erasure_test.exs
```
> If threading `forced_positions` required an `elaborator.ex` edit, include it in the pathspec.

---

### Task 8: Roadmap update + final full-suite gate

**Files:**
- Modify: `docs/superpowers/specs/2026-07-02-idris-parity-roadmap.md` (§2 row #5)

- [ ] **Step 1: Confirm no unintended TCB spread.**

Run: `git diff --stat cd80b49 HEAD -- lib/cure/core/`
Expected: only `lib/cure/core/kernel.ex` (the Task 2 `unify_indices` change). If any other core file changed, investigate.

- [ ] **Step 2: Update roadmap row #5.**

Mark #5 with a landed banner (mirror #11's style): summarize the K Solution-step fix, the E routing/dot-elaboration/erasure, and the P syntax; record that `dp01`/`dp02` remain **blocked** on the separately-tracked auto-generalization defect (so #5's `Type`-polymorphic-family coverage is partial pending that fix); set the status cell to ✅ (or 🟡 with a note if the blocked probes make you prefer "partial").

- [ ] **Step 3: Final full suite (alone).**

Run: `mix test`
Expected: PASS (2585+ prior tests plus all new ones, 0 failures).

- [ ] **Step 4: Commit.**
```bash
git add -- docs/superpowers/specs/2026-07-02-idris-parity-roadmap.md
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "docs(spec): #5 forced/dot patterns landed — roadmap update" -- docs/superpowers/specs/2026-07-02-idris-parity-roadmap.md
```

---

## Self-review notes (coverage against spec)

- Spec §4.1 (K Solution step) → Task 2 + Task 4 (soundness gate). Termination measures (a)/(b) and multi-key cycle → Task 4 Step 1 antibody obligations.
- Spec §4.2 (P dot syntax) → Task 5, incl. the semantic (not syntactic) guard + `Std.String` non-regression + bare-`.x`-as-expression negative.
- Spec §4.3 (E routing + dot elaboration) → Task 3 (routing, the reach flip) + Task 6 (dot elaboration + mismatch reject).
- Spec §4.4 (E erasure via `Cure.Elab.Erase`, per-branch not `quantities`) → Task 7.
- Spec §5.1 probes: `dp01b`/`dp03` (reach, Task 1→3), `dp04` (guard, Task 1), `dp02b`/`dp06` (dot, Task 6), `dp01`/`dp02` (blocked, Task 1). `dp05` occurs-cycle → Task 2 Step 5 kernel guard test (oracle form pinned only if expressible).
- Spec §6 non-goals respected: no higher-dimensional injectivity engine; auto-generalization defect explicitly NOT fixed here (Task 8 Step 2 records it as blocking dp01/dp02).
- Spec §7 risks: subst-key-overlap regression test → Task 2 Step 5(d)/Task 3; parser scope leak → Task 5 Step 1(c); erasure over-eagerness → Task 7 conservative rule.
```
