# Identity-Type Phases B/C Implementation Plan (rewrite → case; retire primitives)

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans, composed with the cure-porting skill's loop and constraints. Steps use checkbox syntax.

**Goal:** Retire the primitive `{:rewrite}` transport (Phase B: every producer emits a single-branch inductive `:case` instead, via in-branch re-elaboration) and then strip the dead `{:eq}`/`{:refl}`/`{:veq}`/`{:rewrite}` Core forms (Phase C), flipping the validator to `:reject`, under the full TCB gate.

**Spec:** `docs/superpowers/specs/2026-07-04-identity-type-as-inductive.md` — read the "Current state — REVISED 2026-07-08 (evening)" section FIRST; it is the authoritative re-scope (K6 gate stale; params-on-spine landed `b355753` kernel / `f3b0e73` elaborator; B′ stdlib already done; the real problem is computed-endpoint desugaring, diagnosed in `c635e8c`'s revert message — read that commit message in full with `git show c635e8c --format="%B" -s`).

## Global Constraints (cure-porting discipline — non-negotiable)

- **Two pipelines:** ALL work in `lib/cure/elab/*` (Phase B) and `lib/cure/core/*` (Phase C). `lib/cure/compiler/*` and `lib/cure/types/*` are decoys — never edit them for this.
- **Ghost commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no trailers. **Explicit pathspec staging only** (`git add -- <path>`), never `-A`.
- **One build at a time.** Scoped `mix test <file>` while iterating; `mix cure.oracle <cluster>` for verdicts (never hand-write a verdict); full suite ONCE, alone, at each gate. Oracle replay (`mix test test/oracle_replay_test.exs`) green before every commit.
- **TCB (Phase C) is HARD-STOP-and-review:** red-green + antibody extension + full Antigen + full suite. If any Phase-C removal changes a VERDICT anywhere, stop — that means a primitive was not actually dead.
- **Tests and frozen oracle verdicts are immutable.** The behavioural pin is byte-identical verdicts across: `rewrite/rw01-rw09`, `refl/rf01-rf05`, `frp/*` (sentinel: `frp01_par_assoc` — computed endpoints, the case that killed `d44edb8`), `with/*` + `withmulti/*` (sentinel: `wi05_sibling_refine` — the two producer sites in with-transport machinery), `cycle/*`, `dotpat/*`.
- Worktree: `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/kernel-parity-batch`, branch `autopilot/kernel-parity-batch`.

## Ground truth (hardened-spec-verified; re-verify line numbers before editing)

- **Seven `{:rewrite, …}` producer sites** in `lib/cure/elab/elaborator.ex`: `1083`, `1095`, `1162`, `1166` (bridge_step outer wrap), `1195`, `1856` (`elaborate_with_eq_branch`), `3421` (`elaborate_carried_eq_branch`).
- The kernel `{:rewrite}` rule (`kernel.ex:~117`) infers the proof; after Phase B nothing reaches it. `ensure_eq`/`eq_parts` currently accept both `{:veq}` and `{:vdata, :Equivalent}`.
- `bridge_step` is dormant in the current corpus (traced); its migration must still be correct but has no live oracle coverage — Phase B adds a unit fixture for it.
- `rw_case_build` (the reverted naive attempt) shifted a pre-elaborated body +1 into the branch — WRONG for computed endpoints. The correct construction re-elaborates the body inside the refl branch, routed through `elaborate_match`'s branch machinery (`build_motive` sentinels handle computed indices).
- Validator: `no_eq_node: :warn` / `no_rewrite_node: :warn` default (`validator.ex:45-46`), `:reject` in release_config (`:81` area).
- Antigen antibody exists: `test/antigen/eq_inductive_antibody_test.exs`.

---

### Task B1: The desugar core — `rewrite_to_case` via in-branch re-elaboration

**Files:** `lib/cure/elab/elaborator.ex` (new helper + migrate the `rewrite_plan` family sites 1083/1095/1162/1195); test `test/cure/elab/rewrite_as_case_test.exs` (new).

**Contract produced:** a helper (suggested name `elaborate_rewrite_as_case`) that, given the proof expr, motive info, and the UNELABORATED body AST + expected type, produces `{:case, proof_core, motive, [refl_branch]}` where the refl branch's body is elaborated INSIDE the branch context (indices refined by the unifier), reusing `elaborate_match`'s machinery rather than reimplementing it. Discovery is part of this task: read `elaborate_match/6`, `build_motive/6`, and how surface `match p ... reflexive() -> body` elaborates today — the target construction is semantically `match p reflexive() -> body` with the motive `rewrite_plan` computed. STRONGLY PREFERRED: desugar at the SURFACE level (rewrite → synthesized single-arm match AST) so `elaborate_match` does all the work; only if the motive cannot be injected that way, build the `:case` node through the same internal functions `elaborate_match` uses. STOP and report if neither route can carry `rewrite_plan`'s occurrence-abstraction motive.

- [ ] **Step 1 (red):** `test/cure/elab/rewrite_as_case_test.exs` with two fixtures asserted via `Program.check_ast/1`: (a) a variable-endpoint rewrite (rw01 shape) whose emitted Core (walk `env.defs[...].body`) contains NO `{:rewrite, ...}` node; (b) a computed-endpoint rewrite (miniature `frp01_par_assoc` shape — endpoints are applications, not variables) that must ACCEPT with no `{:rewrite}` node. Both red today (bodies contain `{:rewrite}`).
- [ ] **Step 2:** Implement the helper; migrate sites 1083/1095/1195 (the main `rewrite_plan` outputs), then 1162 (symmetry path). Iterate against the red file ONLY.
- [ ] **Step 3 (pin):** `mix cure.oracle rewrite && mix cure.oracle refl && mix cure.oracle frp` — byte-identical verdicts (esp. `frp01_par_assoc` stays accept). Then `mix test test/oracle_replay_test.exs`.
- [ ] **Step 4:** Commit (ghost, pathspec): `feat(elab): rewrite desugars to single-branch inductive case (variable+computed endpoints)`.

### Task B2: bridge_step + with-transport sites (the last three producers)

**Files:** `lib/cure/elab/elaborator.ex` (sites 1166, 1856, 3421); extend `test/cure/elab/rewrite_as_case_test.exs`.

- [ ] **Step 1 (red):** add a unit fixture that FORCES `bridge_step` (a reducible-inner-occurrence rewrite that the `contains_a`/`contains_b` syntactic paths cannot take — derive from the rw07 commit history if needed; if genuinely unreachable, document why and delete `bridge_step` instead of migrating it — dead code migration is worse than removal, but ONLY with the tracing evidence written into the test file as a comment). Add with-transport fixtures mirroring `wi05_sibling_refine`'s shape asserting no `{:rewrite}` in emitted Core.
- [ ] **Step 2:** Migrate/remove per Step 1's finding. After this, `grep -n "{:rewrite," lib/cure/elab/elaborator.ex` shows ZERO producers (traversal clauses may remain until C).
- [ ] **Step 3 (pin):** `mix cure.oracle with && mix cure.oracle withmulti && mix cure.oracle rewrite && mix cure.oracle frp`; replay green. Scoped `mix test test/cure/elab/` green.
- [ ] **Step 4:** Commit: `feat(elab): all rewrite producers retired (bridge + with-transport)`.

### Task B-Gate: intermediate full gate

- [ ] Full `mix test` once (0 failures), `mix cure.check.examples` (44), full oracle replay. Commit any strictly-necessary fix with its own red test. Commit: `test(elab): Phase B gate — no rewrite producers, full pins green`.

### Task C1: strip dead Core forms (TCB — HARD-STOP discipline)

**Files:** `lib/cure/core/term.ex`, `eval.ex`, `kernel.ex`, `quote.ex`, `certificate.ex`, `serialize.ex`, plus elab traversal clauses (`subst`, `erase.ex`, `relevance.ex`, `resolution.ex`, `unify.ex`, `generalize`/`walk` helpers — grep `:rewrite`, `{:eq,`, `{:refl,`, `:veq` and enumerate in the report).

- [ ] **Step 1 (red):** kernel test asserting a `{:rewrite, …}` (and `{:eq}`/`{:refl}`) term no longer round-trips: `infer` returns an unknown-form error, `Term.to_external` raises/errors, serializer rejects. Red today (they succeed).
- [ ] **Step 2:** Remove clauses file-by-file, ONE commit per coherent group, scoped `mix test test/cure/core test/cure/elab` between groups. `ensure_eq`/`eq_parts` collapse to the `{:vdata, :Equivalent}`-only forms.
- [ ] **Step 3:** Flip `no_rewrite_node` AND default `no_eq_node` to `:reject` in `validator.ex`; red test first asserting the validator rejects a smuggled primitive node.
- [ ] **Step 4:** Commits per group: `refactor(core): retire {:rewrite} clauses`, `refactor(core): retire {:eq}/{:refl}/{:veq} clauses`, `feat(validator): primitive identity nodes reject by default`.

### Task C-Gate: full TCB gate

- [ ] Extend `test/antigen/eq_inductive_antibody_test.exs` per spec Gate C: (i) refl-matching discharges/refines exactly as the index unifier dictates and equates NO distinct normal forms (defeq non-collapse obligation — generate distinct-normal-form pairs and assert conversion still rejects); (ii) termination unaffected; (iii) retired nodes unreachable (reuse Task C1's red test forms). Red-first where the obligation is new.
- [ ] Sequential gate: full Antigen suite → full `mix test` → `mix cure.check.examples` → full oracle replay (`mix test test/oracle_replay_test.exs`) → `mix cure.oracle rewrite/refl/frp/with/withmulti/cycle/dotpat` live re-run, byte-identical.
- [ ] Update the parity ledger (§2 of `docs/superpowers/specs/2026-07-02-idris-parity-roadmap.md`): the Eq/rewrite rows graduate; note K/UIP stance unchanged.
- [ ] Commit: `feat(kernel): identity type fully inductive — primitives retired (Phase B/C complete)`.

## STOP conditions (report, don't improvise)

- The in-branch re-elaboration cannot carry `rewrite_plan`'s motive (B1).
- Any oracle verdict drifts at any pin (esp. `frp01_par_assoc`, `wi05_sibling_refine`).
- A Phase-C removal turns out to be load-bearing (verdict change / suite failure not explained by the red tests).
- Anything requires touching `lib/cure/compiler/*` or `lib/cure/types/*`.
