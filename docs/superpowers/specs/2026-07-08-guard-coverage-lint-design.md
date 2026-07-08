# Z3 Guard-Coverage Lint + bool_elim Vocabulary Retirement — Design

**Status:** approved design (operator standing batch authorization; feature itself pre-authorized by the builtin-inductive foundation spec's "committed next" bullet and the locked SMT trust-boundary decision).
**Layer:** E (untrusted elaborator) + docs/comments. **Zero changes under `lib/cure/core/`.**
**Batch:** parity queue item C-2 (task #12), worktree `kernel-parity-batch`, branch `autopilot/kernel-parity-batch`.

## §0 Rescope: what "match-embedded constructor guards" still means

The roadmap item this initiative descends from — "match-embedded `when` (general), re-expressed on inductive-Bool `:case`" (builtin-inductive foundation spec, `docs/superpowers/specs/2026-07-03-builtin-inductive-foundation-design.md`, "Deferred / committed next" bullet, lines 306–313; roadmap row 4 of `2026-07-02-idris-parity-roadmap.md:49`) — is **mostly landed already**. Verified against the tree (dependent pipeline only):

- Variable/catch-all guard subset: `92d11d5`, `try_guard_match` at `lib/cure/elab/elaborator.ex:2396-2497`.
- Single-level constructor-pattern guards: `desugar_ctor_guards`/`fold_ctor_guard_groups`/`build_guard_chain`, `elaborator.ex:2664-2781`.
- Nested constructor-pattern guards: matrix rows carry `{patterns, guard, body}` (`elaborator.ex:2929`), leaves fold via `fold_leaf_rows` (`elaborator.ex:2981-2987`).
- Non-variable guarded scrutinee: `bind_once_guard` β-redex binder (`6122340`, `elaborator.ex:2421-2434`).
- All of it lowers through the single primitive `bool_case/5` (`elaborator.ex:2542-2546`), which emits `{:case, scrut, motive, [{:True,0,tt},{:False,0,ff}]}` over the **registry** Bool (`Inductive.builtin(sig, :bool)`; seeded at `lib/cure/core/builtins.ex:57`, resolved at `lib/cure/core/kernel.ex:1087`). `bool_elim` was retired wholesale in `9fb19ad`; no live `{:bool_elim}` clause survives in `lib/cure/core/` or `lib/cure/elab/`.

So the "re-express on inductive-Bool `:case`" half of the roadmap prose describes work that has already happened. The genuinely unbuilt remainder of the committed item is:

1. **The Z3 untrusted guard-coverage lint** — the foundation bullet's own words: "Z3 as an untrusted coverage lint (trichotomy drops the catch-all; non-exhaustive errors; shadowed warns)". No trace of it exists in `lib/cure/elab/` today; the only SMT consumer is the non-dependent refinement-types pipeline (`lib/cure/types/refinement.ex` → `lib/cure/smt/solver.ex`), which is a decoy for this purpose.
2. **Stale `bool_elim` vocabulary retirement** — comment/doc/name references to the dead eliminator that survived `9fb19ad`, plus one adjacent stale moduledoc (§5).

This spec covers exactly those two, nothing else.

## §1 Goal

When a guarded match group is structurally non-exhaustive (no unguarded catch-all), today the elaborator hard-rejects with `{:unsupported_guard, :non_exhaustive}` at three sites (`elaborator.ex:2441`, `2748`, `2987`). After this change:

- If Z3 **proves** the guards cover all cases (e.g. the `x < y | x == y | x > y` trichotomy over machine Ints), the match is **accepted**: the final guarded arm becomes the direct fall-through (its guard test, provably true when reached, is elided from the emitted Core). The kernel checks the emitted term exactly as it checks every term.
- If Z3 refutes, times out, answers `:unknown`, or the guards are untranslatable, behavior is **unchanged**: the same `{:unsupported_guard, :non_exhaustive}` error, same shape.
- Independently, if Z3 proves a guard is **shadowed** (implied by the disjunction of the guards before it — its arm is dead code), the elaborator records a warning; elaboration proceeds unchanged.

## §2 Lint design

### §2.1 Trigger points

- **Exhaustiveness recovery** runs only where the structural check is about to reject `:non_exhaustive` — the three sites above. It is a recovery path, not a new always-on pass: structurally exhaustive matches (unguarded catch-all present) never touch Z3.
- **Shadow detection** runs once per guarded group at guard-chain construction, for each guard `g_i` with `i ≥ 2`: if `g_i ∧ ¬(g_1 ∨ … ∨ g_{i-1})` is UNSAT, arm `i` is unreachable → warn. Untranslatable or non-UNSAT (including `:unknown`) → no warning. Because every query failure degrades to "no warning", this pass can run unconditionally without correctness risk; if plan-time measurement shows compile-time cost, it may be restricted to groups with ≥ 2 guards (which is anyway the only case it can fire on).

### §2.2 Translation fragment

New module `lib/cure/elab/guard_lint.ex` translates **elaborated Core guard terms** (the guards are already elaborated at `Bool` — `elaborator.ex:2460` checks them against `bool_type_term/1`) into SMT-LIB:

- `{:prim, op, args}` for `op ∈ {lt, le, gt, ge, eq, ne}` over Int-typed operands → the corresponding linear-arithmetic atom; `{:prim, op, args}` for `op ∈ {add, sub, mul}` (mul only by a literal, keeping the fragment linear) → arithmetic terms; Int literals → numerals; guard-scope variables of machine-Int type → declared SMT Int constants.
- Bool constructors `True`/`False` → `true`/`false`.
- **Anything else** — user function calls, non-Int-typed subterms, `Nat` (an inductive, not a machine Int), nonlinear arithmetic — makes the containing query **untranslatable**.
- **Untranslatable ⇒ not proven.** This adopts the K13 rule already stated for the refinement lint (`lib/cure/smt/solver.ex:79-80`): an obligation the untrusted lint cannot fully translate must never be reported as proven. Rendering unknown subterms as `true` and proving the weakened formula is forbidden. Structural identity is the one sound weakening: two syntactically identical untranslatable guards may be mapped to the same fresh uninterpreted Boolean constant (this lets shadow detection catch a literally repeated guard); distinct untranslatable guards get distinct constants, so an exhaustiveness proof can never lean on them.

### §2.3 Accept semantics and why soundness never depends on Z3

On a proven-exhaustive group, the emitted Core changes in exactly one way: the last guarded arm's `bool_case` wrapper is dropped — the previous guard's false-branch becomes that arm's body directly. The result is a closed, total, kernel-checked term; the kernel neither sees nor trusts the Z3 verdict (locked decision: Z3 is OUT of the dependent-kernel TCB, untrusted lint only — see the SMT trust-boundary memory, reconfirmed here as normative).

Failure analysis for a wrong Z3 "proof" (solver bug): the elided final guard means inputs in the (actually uncovered) region evaluate the final arm's body instead of being rejected at compile time. That is a **semantic deviation confined to programs the surface language previously rejected as ill-formed** — no type-unsoundness, no kernel judgement influenced, no stuck term, totality intact. This is the precise sense in which the lint is "untrusted": it gates surface acceptance at the E-layer (which is untrusted by definition), never a kernel judgement.

Z3 is always present as part of the language (locked decision — no feature-gating on availability). If the binary is nonetheless missing at runtime, the query layer reports failure and both lint passes degrade to the conservative pre-lint behavior; nothing else may change.

### §2.4 Solver plumbing reuse

Reuse `Cure.SMT.Process` (the low-level Z3 process/query runner) **only**. Do NOT reuse `Cure.SMT.Translator` or `Cure.SMT.Solver`'s refinement-predicate semantics — those translate the non-dependent refinement-AST, not Core terms. `guard_lint.ex` owns its own Core→SMT-LIB rendering per §2.2 and issues queries with a fixed conservative timeout (default 3000 ms, matching `solver.ex`'s `:default` budget); timeout ⇒ `:unknown` ⇒ conservative.

### §2.5 Warnings channel

`Cure.Elab.Program.elaborate/1` returns `{:ok, env}`; that shape is pinned by hundreds of tests and does not change. Shadow warnings accumulate on the elaboration environment: a `warnings` list field (append `{:guard_shadowed, fn_name, arm_index}`) with a public accessor (e.g. `Env.warnings/1` or equivalent — exact placement decided at plan time against the real `Env` struct). Tests assert warnings through the accessor. Wiring warnings into CLI output is out of scope (non-goal §7); the Validator's separate Core-layer `{:ok, _warnings}` channel (`program.ex:364`) is untouched and unrelated.

## §3 Trust boundary (normative restatement)

- All new code lives in `lib/cure/elab/` (+ tests). **Nothing under `lib/cure/core/` changes.** This initiative does not qualify for the Agda/Lean-alignment TCB blanket approval and must not need it.
- The lint can only ever: (a) flip a would-be `:non_exhaustive` **rejection** into an acceptance whose emitted Core the kernel fully checks, and (b) add warnings. It must have no other observable effect. In particular a Z3 `:sat`/`:unknown`/crash/timeout/absence must leave behavior byte-identical to today.
- Antigen V6 (per the locked SMT memory) tests **lint-soundness**: the lint must never prove exhaustive a guard set that isn't (§6).

## §4 Idris divergence — deliberate and documented

Idris2 has no SMT coverage lint; the trichotomy example without a catch-all is rejected by Idris (`%default total` coverage) and accepted by post-lint Cure. This is a **deliberate, operator-authorized Cure extension** (the foundation spec bullet is explicit), not an oracle finding:

- **No oracle probes for lint-accept cases.** A `.cure`/`.idr` pair there would produce cure-accepts/idris-rejects, which the oracle contract reserves for soundness surprises; manufacturing such rows for a deliberate extension would poison the contract's signal. The divergence is documented in ledger row 4 prose instead (one sentence added to the roadmap's row-4 status, marked "deliberate extension, foundation-spec-authorized").
- Existing guard oracle clusters (`guard/guard01–06`, `guardscrut/gs01–03`, all relation `same`) must remain `same`: every one either has a catch-all or is rejected for reasons the lint does not touch. The gate re-verifies via replay, not `mix cure.oracle` (which is destructive and unneeded here).

## §5 Stale-vocabulary cleanup (comment/doc-only, zero behavior)

Retire the dead `bool_elim` vocabulary that survived `9fb19ad`, and one adjacent stale moduledoc:

- `lib/cure/elab/elaborator.ex` — comment references at ~2387-2394, 2447, 2501-2502, 2662, 2952 and the stale kernel-side comment at `lib/cure/core/kernel.ex:1116` (comment text only — this is not a code change under `core/`; if touching even a comment there proves contentious at review, drop that one edit rather than argue): reword to describe the `:case`-on-Bool lowering that actually exists.
- `lib/cure/elab/declarations.ex:375` — same treatment.
- `lib/std/bool.cure:7` — stale doc comment.
- `lib/antigen/generators/totality.ex` — `bool_elim`-flavored *naming/comments* only; do not rename public functions if any test references them (plan-time grep decides rename vs. comment-only).
- `lib/antigen/assays/dot_forcing.ex` moduledoc — corrects the claim that oracle fixtures ni03/ni07 exercise the carried-eq dispatch "end-to-end": they landed as the simplified directly-invertible family (Idris cannot express the carried differential without `with`); real carried coverage lives in `test/cure/elab/named_implicit_tail_test.exs` and the `Antigen.Generators.ElabDotForcing` catalog (landed this batch).

Exact line numbers are anchors, not gospel — the plan re-greps `bool_elim` across `lib/` and updates every stale mention it finds, and the diff for this section must contain no executable-code changes (comments, docstrings, string literals in docs only).

## §6 Testing

Strict red-green throughout; tests behavioral and immutable once green.

- **Unit (new `test/cure/elab/guard_lint_test.exs`):**
  - Trichotomy accept: `x < y | x == y | x > y` over machine Ints, no catch-all → `{:ok, _}` (red first: today `{:error, {:unsupported_guard, :non_exhaustive}}`).
  - Two-guard complement accept: `x < y | x >= y` → `{:ok, _}`.
  - Genuinely non-exhaustive translatable set (`x < y | x > y`, missing equality) → error unchanged, exact shape `{:error, {:unsupported_guard, :non_exhaustive}}`.
  - Untranslatable guards (user Bool function, e.g. `isZ(k)`) with no catch-all → error unchanged (K13 rule observable).
  - Shadowed guard (`x < y` then `x < y` again, catch-all present) → `{:ok, env}` + one `{:guard_shadowed, _, _}` via the accessor; unshadowed group → no warnings.
- **Pinned-fixture audit (plan-time, mandatory):** verify the existing pinned non-exhaustive rejects (`test/cure/elab/guard_test.exs:66-74`, `test/cure/elab/ctor_guard_test.exs:105-106`) use guard sets that are NOT provably exhaustive in the §2.2 fragment, so their pins survive untouched. If one turns out provably exhaustive, STOP and report (tests-immutable vs. spec'd behavior-change conflict is an operator call, not an executor improvisation).
- **Antigen V6 lint-soundness assay:** a new fixed-catalog generator + assay pair mirroring the just-landed `ElabDotForcing` structure (`elab/guard_lint` label; runner registry line; challenge round-trip): catalog cells = translatable guard sets with hand-verified exhaustive/non-exhaustive labels, two-sided; metamorphic `:flip` = drop one guard from an exhaustive set (must flip accept→reject); `:same` = alpha-rename a guard variable. Modest cell count (≈6) — this is a soundness pin, not a fuzzer; the StreamData-backed corpus expansion stays a non-goal.
- **Gate:** scoped suites per task; then, once, alone: `mix test test/antigen/` and full `mix test` (including `oracle_replay_test.exs`, which re-verifies §4's "existing clusters stay `same`" claim). Zero failures required.

## §7 Non-goals

- SMTCoq/certificate reconstruction of Z3 proofs (locked: someday, not now).
- Counterexample-enriched error messages (would change the pinned error shape).
- CLI/stderr presentation of warnings (channel lands; presentation is a separate surface concern).
- Join-point sharing of duplicated default bodies; nested named-default over non-variable scrutinee (`resolve_default_body` residual) — both remain roadmap row-4 residuals.
- Any change to guard *elaboration* semantics outside the single elision of §2.3.
- **#15 interplay:** the translator keys on `{:prim, op, args}`. Task #15 (prim→delta-globals) will retarget those to delta-global applications; #15's spec must include a one-clause update to `guard_lint.ex`'s recognizer. Record this as a note on task #15 — do not pre-build dual recognition here (YAGNI).

## §8 Acceptance criteria

1. Trichotomy-without-catch-all elaborates `{:ok, _}`; its emitted Core kernel-checks; erasure/runtime behavior of the accepted program is correct on all three regions.
2. Every Z3-failure mode (refuted / unknown / timeout / untranslatable / binary absent) leaves behavior byte-identical to pre-lint on both trigger paths.
3. Shadow warning observable via the Env accessor; `Program.elaborate/1` return shape unchanged.
4. `git diff` of the landed work contains zero executable-code changes under `lib/cure/core/` (comment-only edits permitted per §5) and zero changes to `lib/cure/types/*`, `lib/cure/compiler/*` (two-pipeline discipline).
5. Full gate green: all existing guard pins unchanged, oracle replay green, new Antigen assay green (flip flips, same holds).
6. `grep -rn bool_elim lib/ --include='*.ex' --include='*.cure'` returns only historically-accurate mentions (e.g. "retired in 9fb19ad") or nothing.
