# Lean4lean Bridge Removal Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove the Lean export bridge (commit `3d6f739`'s artifact set + the `ae02ba5`/`ccbe2d0` encoder hunks) in one manual deletion commit, collapsing the backend-selection layer so dependent checking calls the elixir-core path directly.

**Architecture:** Pure removal. Nine tracked files/dirs deleted, two live files surgically edited (`lib/cure/elab/program.ex`, `lib/cure/elab/declarations.ex`). No behavior change: the deleted `:lean` path had no live caller; the default path already routed to `check_ast_elixir_core/1`.

**Tech Stack:** Elixir, git. Spec: `docs/superpowers/specs/2026-07-09-lean-bridge-removal-design.md` (hardened `00da9ce`).

## Global Constraints

- Working dir: `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/kernel-parity-batch` (branch `autopilot/kernel-parity-batch`). NEVER read or touch the parent checkout `/Users/ch/Develop/esp32-beam/cure-lang/lib/...`.
- Ghost commits only: `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO Co-Authored-By, NO trailers/signatures.
- Explicit-pathspec staging only: `git add -- <path>` / `git rm -- <path>`; never `-A`/`.`.
- ONE `mix` command at a time, ever (other agents share the machine; a past concurrent run caused a kernel panic).
- Tests immutable: the ONLY test changes permitted are the three whole-file deletions enumerated in Task 1 Step 2. If ANY surviving test needs a change, STOP and report.
- STOP conditions (spec §3.5): a surviving test needs a change; a reference to the backend layer exists outside the enumerated file set; any edit pressures `local_def_names/1` toward private.
- The implementation is ONE code commit (plus nothing else); if you find yourself needing a second code commit, STOP and report.

---

### Task 1: Delete the bridge, collapse the backend layer, verify, commit

**Files:**
- Delete: `lib/cure/lean/module_encoder.ex`, `lib/cure/lean/bridge.ex`, `lib/cure/kernel/backend.ex`, `lib/cure/kernel/backend/elixir_core.ex`, `lib/cure/kernel/backend/lean.ex`, `lean_bridge/CureLeanBridge.lean`, `lean_bridge/README.md`, `lean_bridge/lakefile.lean`, `lean_bridge/lean-toolchain`, `test/cure/lean/module_encoder_test.exs`, `test/cure/lean/bridge_test.exs`, `test/cure/kernel/backend_test.exs`
- Modify: `lib/cure/elab/program.ex`, `lib/cure/elab/declarations.ex`

**Interfaces:**
- Consumes: `Cure.Elab.Program.check_ast_elixir_core/1` (existing public function — the elixir-core entry the backend wrapped).
- Produces: `Cure.Elab.Program.check_ast/2` now calls `check_ast_elixir_core/1` directly; `check_ast/2`'s arity and `{:ok, Env.t()} | {:error, term()}` contract unchanged (types/checker.ex keeps threading opts).

- [ ] **Step 0: Pre-verification (structural red — the deletion's safety evidence)**

Run each; every hit must be inside the file set above, or STOP:

```bash
grep -rn "Cure.Lean\|Cure\.Kernel\.Backend\|lean_bridge\|CURE_KERNEL_BACKEND\|CURE_LEAN_BRIDGE\|CURE_LEAN4LEAN_PATH\|kernel_backend" lib/ test/ mix.exs
grep -rn "_lean\b" lib/cure/elab/program.ex lib/cure/elab/declarations.ex
grep -n "def check_ast_elixir_core" lib/cure/elab/program.ex   # must exist, public
grep -n "local_def_names" lib/cure/elab/program.ex             # expect def + 3 call sites (:268 :512 :575 region)
```

Also confirm the three test files' counts (red baseline for the suite-delta check): `grep -c 'test "' test/cure/lean/module_encoder_test.exs test/cure/lean/bridge_test.exs test/cure/kernel/backend_test.exs` → 5, 7, 8 (total 20). Record how many of the current 6 suite skips live in `bridge_test.exs` (its real-Lean cases skip unless `lean` is on PATH) — you need this for Step 6's arithmetic.

- [ ] **Step 1: Delete the nine tracked paths**

```bash
git rm -r -- lib/cure/lean lean_bridge test/cure/lean
git rm -- lib/cure/kernel/backend.ex lib/cure/kernel/backend/lean.ex lib/cure/kernel/backend/elixir_core.ex test/cure/kernel/backend_test.exs
```

If `lib/cure/kernel/` is now empty, `git rm` has already handled it (git tracks files, not dirs); if other files remain there, leave them.

- [ ] **Step 2: Rewire `check_ast/2` in `lib/cure/elab/program.ex`**

Replace (current body at :34-41):

```elixir
  @spec check_ast(tuple() | list(), keyword()) :: {:ok, Env.t()} | {:error, term()}
  def check_ast(ast, opts) do
    with :ok <- check_no_duplicate_defs(ast),
         :ok <- check_no_duplicate_types(ast),
         :ok <- check_no_duplicate_ctors(ast) do
      Cure.Kernel.Backend.check_ast(ast, opts)
    end
  end
```

with:

```elixir
  @spec check_ast(tuple() | list(), keyword()) :: {:ok, Env.t()} | {:error, term()}
  def check_ast(ast, _opts) do
    with :ok <- check_no_duplicate_defs(ast),
         :ok <- check_no_duplicate_types(ast),
         :ok <- check_no_duplicate_ctors(ast) do
      check_ast_elixir_core(ast)
    end
  end
```

(`opts` only ever selected the backend; the default path was exactly this call — verified in `Backend.ElixirCore.check_ast/2`, which ignores opts. Keep the arity: types/checker.ex threads opts.)

- [ ] **Step 3: Remove the five bridge functions (+ their two nested error rows)**

In `lib/cure/elab/program.ex`: delete whole functions `check_ast_for_lean_backend/1` (def at :143; the `:lean_backend_unsupported_*` row at :150 goes with it), `elaborate_declarations_lean` (:693; row at :708 goes with it), `register_pass_lean` (:699), `body_pass_lean` (:774). Line numbers are pre-edit anchors — locate by name, delete def-to-end.
In `lib/cure/elab/declarations.ex`: delete `elaborate_function_body_lean/2` (:74, `@doc false`).
Do NOT touch `local_def_names/1` (stays public) or `check_ast_elixir_core/1`.

- [ ] **Step 4: Grep gate (spec §3.3)**

```bash
grep -rn "Cure.Lean\|Cure\.Kernel\.Backend\|lean_bridge\|CURE_KERNEL_BACKEND\|CURE_LEAN_BRIDGE\|CURE_LEAN4LEAN_PATH" lib/ test/ mix.exs
grep -rn "_lean\b" lib/
```

Expected: zero hits (prose comments mentioning the Lean LANGUAGE excepted — e.g. "Lean-aligned"; there are no `_lean` identifier survivors).

- [ ] **Step 5: Scoped smoke test (one mix command)**

Run: `mix test test/cure/elab/`
Expected: all green (445+ tests), zero failures — proves the rewire compiles and dependent checking behaves identically.

- [ ] **Step 6: Full suite ONCE**

Run: `mix test`
Expected: **0 failures**. Passed ≈ 3291 − 20 + (number of the 20 that were skipped at baseline); skipped = 6 − (bridge_test skips recorded in Step 0). Antigen (503) and oracle replay (65) run inside this suite — all green. Report exact numbers. Any surviving-test failure = STOP (do not fix tests).

- [ ] **Step 7: Commit (single code commit, ghost, explicit pathspecs)**

```bash
git add -- lib/cure/elab/program.ex lib/cure/elab/declarations.ex
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "refactor!: remove lean4lean bridge and backend-selection layer

Removes the artifact set of 3d6f739 ('Route dependent checking through
Lean backend') plus the ae02ba5/ccbe2d0 encoder hunks: lib/cure/lean/,
lib/cure/kernel/backend*, lean_bridge/, test/cure/lean/, backend_test,
and the five _lean functions (+2 nested error rows) in program.ex/
declarations.ex. check_ast/2 now calls check_ast_elixir_core/1 directly;
no live caller ever selected :lean. Supersedes cleanup-strategy design
decision 6 (second backend as long-term goal) by operator order.
git revert was rejected: 4-file conflict + it would re-privatize
local_def_names/1 and resurrect a file 588bd46 deleted." \
  -- lib/cure/elab/program.ex lib/cure/elab/declarations.ex lib/cure/lean lib/cure/kernel test/cure/lean test/cure/kernel/backend_test.exs lean_bridge
```

Verify: `git status --porcelain` clean; `git log -1 --format='%an %ae %b'` shows ghost author, no trailers.

- [ ] **Step 8: Report**

Report: exact suite numbers (passed/skipped delta vs 3291/6 with the Step-0 skip accounting), the grep outputs (empty), commit hash, and an honest statement that no surviving file beyond the two edited ones changed (`git show --stat`).
