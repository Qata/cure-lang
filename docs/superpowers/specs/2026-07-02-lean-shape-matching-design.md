# Lean-Shape Dependent Pattern Matching (for Safe FRP Types) — Design

**Date:** 2026-07-02
**Status:** Approved design (Lean shape; replace A/B/C; kernel work authorized).
**Governing memories:** `dependent-types-frp-initiative`, `reactive-runtime-design-bible`, `transliteration-program-p0`, `elaborator-hard-stop-principle`.
**Domain skill:** `cure-porting` (differential-oracle TDD loop, K/E/P/A/C layer map, TCB HARD-STOP discipline).

## 1. Goal

Give Cure **real Lean-style dependent pattern matching** — one unification-driven,
context-generalizing `match`/`with` mechanism that **subsumes today's three
fragmented paths** (A = value-abstraction `with`, B = eq-transport `with` proof,
C = index-inversion LHS-rematch) — so that Cure can express and *statically check*
the type system of Sculthorpe & Nilsson, **"Safe Functional Reactive Programming
through Dependent Types" (ICFP'09)**, and run the resulting programs on BEAM/AtomVM.

This is the enabling capability for the dependent-types-FRP initiative: replacing
Cure's faked dependent types with machinery strong enough for indexed signal-function
families.

## 2. Why this shape (paper-grounded)

The paper's type system rests on **one heavily-indexed inductive family**
`SF : SVDesc → SVDesc → Dec → Set` whose constructors carry **computed indices**:

- `_≫_  : … → SF as cs (d₁ ∧ d₂)`
- `_∗∗_ : … → SF (as ++ bs) (cs ++ ds) (d₁ ∧ d₂)`
- `loop : … → SF (as ++ cs) (bs ++ ds) → SF ds cs dec → SF as bs d`

Indices are **`++` on type-level lists** and **`∧`/`∨` on `Dec`** — *functions*, not
constructors. The operational semantics (paper Fig. 4) and every combinator are
defined by **dependent pattern matching on this family, refining computed indices
per branch**. §8 records that the authors abandoned Haskell for Agda specifically
because of **"problems encoding associativity of vector concatenation."**

That is the crux and the acceptance driver: matching/composing on `SF (as ++ bs) …`
leaves the index a **stuck application** (`++` with an unknown split), so unification
does **not** reduce to a substitution — the equation must be **carried** and
discharged by an **associativity/identity `rewrite`**. Cure's current
substitution-only rematch (path C) *cannot* do this. The Lean shape handles it by
carrying the equation into the motive as an explicit `Eq` — exactly what this
type system needs.

### Why Lean shape over Agda shape (for Cure specifically)

Both mature systems solve this; the tie-break is architectural fit:

1. **Reuses Cure's just-verified trusted core.** Rematch already routes through
   `{:case}` + `unify_indices` + `specialize_branch_context` + a re-checking
   `Kernel.check`. Generalizing *that* engine is a continuation, not a new subsystem.
2. **Handles the ++-associativity crux natively** via carried equalities in the motive.
3. **Composes with Cure's existing `rewrite`** (rw07, bridge lemmas) instead of
   redefining `rewrite` as with-sugar (the Agda model would disrupt shipped machinery).
4. **Matches Cure's "elaborator proposes, kernel disposes" model** — which *is* Lean's
   equation-compiler model (frontend → eliminator applications the kernel re-checks).

(Agda-shape with-function generation would be the more literal transliteration of the
paper's *source*, but a worse fit for Cure's architecture and shipped `rewrite`.)

## 3. Layer map & the trusted-kernel discipline

- **K (TCB, `lib/cure/core/*`):** the changes in Phases 1, 2, 5. Each is
  **HARD-STOP-and-review**: red-green + a new Antigen antibody proving the change
  terminates and **equates no distinct normal forms** + full Antigen suite + full test
  suite + an **independent adversarial-verification subagent** pass (fresh context, tries
  to break soundness, re-derives from code) BEFORE the task is done.
- **E (`lib/cure/elab/*`):** Phase 3 (the equation-compiler front-end) and the A/B/C
  retirement. Emits only kernel-checkable Core; the kernel re-check is the soundness
  backstop.
- **P/C:** minimal (surface already supports `match`/`with`/`rewrite`).
- **A (Antigen):** grows an antibody per TCB change.

**No auto-merge.** The full human review of all TCB changes is at merge time (consistent
with "authorize kernel work" + autopilot). Per-change the automated soundness gate above
must be green.

## 4. Architecture — one generalizing, unification-driven match

A single elaborator path (an equation compiler) that, for a `match`/`with` on scrutinee(s):

1. **Generalizes the dependent context into the motive** — every context entry whose
   type mentions a scrutinee (or a scrutinee's indices) is reverted into the motive, so
   per-branch refinement reaches siblings (Lean `generalizing := true`).
2. **Runs the full first-order unifier per branch** (Phase 1): the five rules —
   **solution** (`x := t`), **injectivity** (`c ū = c v̄` → unify `ū,v̄`), **conflict**
   (`c … = d …`, c≠d → `:impossible`, discharge `{:absurd}`), **cycle** (occurs-check →
   `:impossible`), **deletion** (definitionally-equal sides → drop).
3. **Carries stuck equations** (Phase 2): when neither solution nor injectivity applies
   (e.g. `as ++ bs` vs a variable/other stuck term), inject an explicit `Eq` hypothesis
   into the branch (motive-carried), rather than failing — the FRP crux.
4. **Emits nested case trees** (`{:case, …}`, possibly nested) the kernel re-checks.
5. **Discharges carried equalities** via Cure's existing `rewrite` + a stock of
   type-level lemmas (Phase 4): `++` assoc/right-identity, `∧`/`∨`/`<:` laws.

Capabilities A/B/C become special cases of this path and are retired once each is
provably subsumed (their existing tests stay green as the subsumption proof).

## 5. Phased plan (each phase = independently testable; TCB phases gated)

- **Phase 0 — Acceptance oracle (E/none; non-TCB).** A minimal faithful transliteration
  of the paper's `SF as bs d` family with `++`/`∧` indices + one combinator whose result
  index is `as ++ bs`, as paired `.cure`/`.idr` oracle probes (cluster `frp`). Currently
  **red in Cure** (the stuck-`++`-index case), green in Idris — this anchors "done" and
  proves the gap. Also a red unit test at the elaborator level.
- **Phase 1 — Full unifier (TCB; gated).** Extend `unify_indices` from solution-only to
  the five-rule first-order unifier. Antibody: unifier terminates + never equates distinct
  normal forms + conflict/cycle ⇒ `:impossible` soundly.
- **Phase 2 — Carried equalities (TCB + E; gated).** Stuck unification carries an `Eq`
  into the motive instead of failing; kernel case rule + motive-wf accept the carried
  hypothesis; elaborator threads it into the branch context. Antibody: a carried-eq branch
  is sound iff the kernel can independently re-derive the equation's use-site well-typedness.
- **Phase 3 — Generalizing match front-end (E).** The equation compiler (context
  generalization + per-branch unifier + carried eqs + nested case-tree emission).
  Subsume + retire A, then B, then C (each: prove its suite still green under the unified
  path, then delete the special-case code). Differential oracle: `match`/`with` clusters
  stay `same`.
- **Phase 4 — Type-level lemma stock + `rewrite` composition (E/C).** `++` assoc/identity,
  `∧`/`∨`/`<:` as total type-level functions + refl-bridge lemmas; make `rewrite` discharge
  carried stuck-index equalities. **Phase-0 probes flip to accept here** (oracle `frp` → `same`).
- **Phase 5 — Signature-aware `Quote.reify` (TCB; gated).** The reach-pinned repair (recover
  the params/indices split from the signature, Agda/Lean-style) — closes the residual
  Eq-endpoint incompleteness (`reify_split_gap_reach_test` migrates red→green-forcing).
- **Phase 6 — FRP capstone (E + probes).** Port the real `SF` + `≫`/`∗∗`/`loop`/`switch`
  + decoupledness (`Dec`) + initialisation (`Init`) indices. Oracle confirms: well-formed
  nets **accept**; instantaneous (undecoupled) cycles and uninitialised-signal escapes
  **reject** — the paper's safety property, checked by Cure.

## 6. Acceptance criteria

- **Differential oracle** `frp` cluster: well-formed signal-function nets `accept`
  (Cure = Idris), the paper's two bad-program classes (instantaneous cycle; uninitialised
  escape) `reject` in both; every entry `same` (or a written, sound `cure_stricter`).
- The ++-associativity composition (`_∗∗_`, `loop`) type-checks in Cure — the crux the
  authors switched languages for.
- **A/B/C retired**: the unified path subsumes them; `with_abstraction`, `with_rematch_*`,
  and dependent-`match` suites remain green with the special-case code deleted.
- Every TCB phase: its Antigen antibody green + full Antigen + full suite + independent
  adversarial verification, TCB diff reviewed at merge.
- 0 regressions vs the branch baseline at each phase gate; full suite green at Stage 5.

## 7. Skeptical-review directive (operator-mandated)

**At the top of EVERY skeptical-review pass (spec review and plan review), the reviewer
must first re-check how Lean implements the relevant mechanism** by reading the actual
`~/Develop/lean4` source (`src/Lean/Elab/Match.lean` for the equation compiler / motive
generalization / `withEqs`; `src/kernel/` for the checked eliminator; the unifier in
`src/Lean/Meta/`), and ground each finding against that reference rather than against
memory or assumption. A finding that contradicts Lean's actual behavior is itself suspect.

## 8. Non-negotiable constraints

- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`,
  no `Co-Authored-By`, no Claude signature.
- **Explicit-pathspec staging only** (`git add -- <path>`); a concurrent agent may share
  the origin worktree. This build runs on an isolated `autopilot/<topic>` worktree.
- **One build at a time.** Never run two `mix` suites concurrently (a past concurrent
  full-suite run panicked the kernel). Scoped `mix test <file>`; full suite once, alone, at gates.
- **Tests immutable once green**; behavioral, not implementation-coupled.
- **Reference-grounded:** verify against vendored Idris2/Agda AND `~/Develop/lean4` source,
  never memory.

## 9. Deferred (out of scope for this run)

- Forced/dot patterns as a first-class surface feature (`f (k+k)`) beyond what carried
  equalities already give (ledger #5) — revisit if Phase 6 needs it.
- Multiple/nested `with` beyond what the equation compiler yields for free.
- Universe polymorphism (the paper works around its absence in Agda; Cure mirrors the
  workaround, not the feature).
- Codegen/runtime of the FRP combinators on-device (Phase 6 is type-checking; the runtime
  is the reactive-runtime-design-bible's separate staged roadmap).
