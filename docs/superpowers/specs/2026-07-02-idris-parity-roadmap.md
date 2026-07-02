# Idris-parity roadmap — quality parity for the features Cure already supports

**Status:** planning reference (not an implementation spec). Enumerates every
remaining work item to call Cure's dependent-type implementation "Idris parity"
— **scoped to the quality of the capabilities we already support**, not to
Idris' full feature set. New capability *domains* Cure deliberately does not
have (linear/quantitative types, interfaces at Idris depth, elaborator
reflection, `with`-abstraction as a language feature, named/auto implicits) are
listed once under §4 and then excluded.

This document is the source of truth for "what is left." It is grounded in the
current kernel/elaborator/Antigen code (all line references verified against the
tree at authoring time) and supersedes ad-hoc gap discussions. Individual rows
graduate into their own design specs + autopilot runs; this ledger tracks them.

Related specs:
[`2026-07-02-dependent-match-surface-design.md`](2026-07-02-dependent-match-surface-design.md)
(sub-project ④, in flight — rows 2/8/16),
[`2026-07-02-antigen-eq-rewrite-design.md`](2026-07-02-antigen-eq-rewrite-design.md)
(the `rewrite/eq` vertical),
[`2026-07-01-case-index-unification-design.md`](2026-07-01-case-index-unification-design.md)
(the kernel unifier, row 1),
[`2026-07-01-antigen-tier-a-design.md`](2026-07-01-antigen-tier-a-design.md)
(the Antigen apparatus).

## 1. Scope and framing

"Parity" here means: **for a feature Cure already implements, does it match
Idris in soundness, completeness, and ergonomics?** A gap is either
- *soundness* — the checker can accept an ill-typed / non-total program;
- *reach* — a program Idris accepts (within this feature) that Cure rejects;
- *ergonomics* — Cure demands manual annotation Idris infers;
- *assurance* — how strongly we can *demonstrate* the property holds.

Layers referenced throughout: **K** = trusted kernel / TCB
(`lib/cure/core/*`), **E** = untrusted elaborator (`lib/cure/elab/*`), **P** =
parser/lexer (`lib/cure/compiler/*`), **A** = Antigen
(`lib/antigen/*`, `test/antigen/*`), **C** = eval / codegen / erase.

Status legend: ✅ at parity · 🔵 in flight (sub-project ④) · ⬜ not started · 🔴 live soundness hole.

## 2. Parity ledger — the features we support

| # | Capability | Work item to reach parity | Layer | Kind | Status |
|---|---|---|---|---|---|
| 1 | Dependent case unifier | First-order unification: solution, deletion, injectivity, occurs-check, no-confusion, impossible-branch discharge | K | — | ✅ |
| 2 | Dependent case surface | Impossible clauses (omit + verified `-> impossible`) + constructor-headed motive completeness (verbatim-reuse case) | E, P, C | additive | ✅ |
| 3 | Pattern matching depth | Nested/deep patterns → decision-tree compiler (M8.4). Kernel case already nests, so this is a lowering pass, not a kernel change | E | additive (refactors match path) | ⬜ |
| 4 | Pattern forms | Non-constructor patterns in dependent position (`_`, literal, as-patterns) handled, not merely rejected | E | additive | ⬜ |
| 5 | Pattern matching | Forced/dot patterns + forced-argument erasure | E, C | additive | ⬜ |
| 6 | Dependent matching | `with`-abstraction (match on an intermediate, refine the goal) — *borderline; core to Idris matching quality*. **Capability A landed** (`58037d6`): block/inline `with <single-expr>` over a **non-indexed** scrutinee, refining the GOAL by the scrutinee's *value* via a value-abstracting motive `{:lam, ty, abstract_term(goal, e, 0)}` (the `motive_for` pattern, not index-refinement) elaborated in place as `{:case,…}`; kernel accepted the value-abstracting motive unchanged (no TCB). Strictly beyond `match` (oracle wi01: plain `match` on the same goal is rejected). *Reach*: `proof` clause (B), sibling/other-argument refinement (M), multiple with-exprs, LHS re-matching of parent patterns, views (C), and codegen/runtime lowering (type-checks only today); indexed scrutinee is explicitly rejected (`{:with_indexed_scrutinee_unsupported,_}`) — that is `match`'s domain | E, P | additive | 🟡 (capability A; reach: proof/sibling/views/codegen) |
| 7 | Propositional equality | Automatic `rewrite` motive inference (abstract LHS occurrences in the goal, à la Idris `rewrite … in`) — implemented in `rewrite_plan/6`, audited to parity with `elabRewrite` (P0); motive-under-`:case`-binder capture bug fixed. Conversion-occurrence rewriting (oracle probe rw07) now **parity** (`same`) via an elaborator bridge-lemma step (`2ac4add`): a refl-bodied bridge checked at the asymmetric endpoint through a constant motive, so the kernel only ever decides a top-level conversion. Underlying **K-layer reach** tracked in the TCB note below (multi-occurrence / deep up-to-conversion still uncovered by the single-occurrence bridge) | E | additive | ✅ |
| 8 | Equality / absurdity | `Void`/absurd elimination at the surface (`{:absurd}`) | K (leaf), E | additive | ✅ |
| 9 | Inference unification | First-order metavariable engine: alloc, occurs-checked solve, zonk (`lib/cure/elab/unify.ex`) | E | — | ✅ |
| 10 | Inference unification | Pattern (Miller) unification — solve `?m x y = t` | E | additive | ⬜ |
| 11 | Inference unification | Postponed/suspended constraints (real flex-flex: constraint queue + retry-on-progress) | E | additive | ⬜ |
| 12 | Totality — termination | Single-argument structural descent | E | — | ✅ |
| 13 | Totality — termination | **Mutual recursion**: soundness hole closed (`d13d718`; `diverging_mutual_pair` replays `:ok`, antibody banked as a permanent regression guard). Remaining is *reach* — well-founded mutual / lexicographic descent is conservatively rejected, not unsoundly accepted (P1/#14) | K, E | reach | ⬜ |
| 14 | Totality — termination | Multi-argument / lexicographic (size-change) descent | E | additive | ⬜ |
| 15 | Totality — coverage | Kernel exhaustiveness (`declared ⊆ covered`) | K | — | ✅ |
| 16 | Totality — coverage | Surface exhaustiveness diagnostics accounting for discharged/impossible branches | E | additive | ✅ |
| 17 | Totality — coverage | Coverage over nested patterns | E | additive | ⬜ (needs #3) |
| 18 | Positivity | Strict positivity checker + vertical | K/E, A | — | ✅ |
| 19 | Positivity | Confirm + bank nested / through-constructor / negative-position (arrow-left) positivity | K/E, A | verify + additive | ✅ (W4: audited, holes fixed, antibodies banked) |
| 20 | Universes | Cumulative universes, no `Type:Type`, two-universe constructor-field rule | K | — | ✅ |
| 21 | Assurance (meta) | Known-label regression net across all verticals | A | — | ✅ |
| 22 | Assurance (meta) | **Term-generator metatheory engine** (StreamData-backed corpus, known-label totality) — turns the net into soundness *evidence* | A | additive | ⬜ (designed) |
| 23 | Assurance (meta) | Missing per-rule antibodies: occurs-check/cycle and deletion rule | A | additive | ✅ (W3: deletion antibody + occurs pin) |
| 24 | Assurance (meta) | Wire a forced/dot-pattern (`forcing`) Antigen vertical once #5 exists | A | additive | ⬜ (needs #5) |
| 25 | Assurance (meta) | Surface-level `.cure` regression corpus for the ④ features | A | additive | ⬜ (post-④) |
| 26 | Dependent matching | Expression-level / inline `match` (Idris `Elab/Case.idr`). **Checking mode landed** (`fcdf5ce`): a `match` in nested expression position — as a `rewrite … in` body and as an arm body of another `match`, non-dependent and with a dependent goal that mentions the matched variable (motive refines per level); non-exhaustive nested matches now give the real `{:missing_branch,_}` coverage error. *Reach*: inference-position inline match (no expected type → needs Idris's auxiliary case-function lift) and let-blocks (`:block`/`:assignment`) in the dependent elaborator, so a `let r = match … in r` tail is still rejected (oracle probe mt05, `cure_stricter`) | E | additive | 🟡 (checked mode; reach: inference-pos + let-blocks) |

### Already at parity — no work (bounds the scope)
Rows **1, 9, 12, 15, 18, 20**: the kernel type checker, first-order index
unifier, universes, structural termination, coverage, and positivity are at
Idris quality for what they cover. **The TCB is essentially done** — with #8's
`{:absurd}` leaf landed, #13's mutual-recursion hole closed, and #19's
nested-positivity gaps audited + banked, every remaining row lives in the
untrusted elaborator / Antigen layers.

**One known K-layer *reach* (soundness-safe incompleteness), scheduled as its
own reviewed TCB run.** The normalizer preserves stuck eliminators without
δ-reducing their targets: a stuck `case` never re-reduces its scrutinee
(`normalise.ex` `nf_neutral`), and `spine/2` only unwraps `napp`, so `nfst`/
`nsnd` frames over a certified-global spine freeze the same way — e.g.
`nf(plus(plus(Z,n),Z))` and `fst(g(x))` stay stuck even at top level. This is
*incompleteness, not unsoundness* (it rejects/leaves-stuck; it never equates
distinct normal forms), and rw07 (#7) is currently dodged in the elaborator by
the bridge lemma. The prescribed fix is **one clause at the `unfold_head`
seam** — whnf the `ncase` scrutinee and the `nfst`/`nsnd` targets, resume ι if a
constructor emerges — repairing whnf+nf+conv at a single trusted point rather
than patching `nf_neutral` and `conv_neutral?` separately. **Gate for that
run (HARD-STOP review):** red-green, a new Antigen antibody proving the clause
terminates and equates no distinct normal forms, the full Antigen suite, and
the full test suite. Until it lands, the bridge lemma is the sanctioned
workaround and this row is the must-eventually-accept reach-pin.

### The honest headline
Of 26 rows: **13 at parity, 13 remain, 0 live soundness holes** — the
transliteration-P0 audit landed ④'s rows 2/8/16 and #7's audited-complete
`rewrite` motive inference (rw07 now closed via the elaborator bridge lemma),
the pre-port banking run closed #13's mutual-recursion hole (now a reach item),
#19's nested positivity, and #23's missing antibodies, and the post-merge port
run landed checked-mode expression-level `match` (#26, `fcdf5ce`) and
`with`-abstraction capability A (#6, `58037d6`). The remaining 13 are reach
(#3–#6, #13, #14, #17, #26 — several now *partially* landed: #6 capability A,
#26 checked mode), ergonomics/inference (#10, #11), or assurance strength (#22,
#24, #25).
Highest-leverage single item: **#22** — without a term generator, Antigen
proves "these specific holes stay closed," not "the kernel is sound."

## 3. Antigen — coverage and capability expansion

### 3.1 Current coverage (verified against `lib/antigen/` + `test/antigen/`)

| Vertical | Soundness property it proves | Challenges banked (well/ill) | Strength |
|---|---|---|---|
| `stub` | harness self-test (planted `{:global,:boom}`) | 1 planted infection | meta only |
| `totality/terminating` | structural-recursive defs accepted | `structural_terminating` + W2 reach pins (reach.sexp, P1 targets) | partial |
| `totality/diverging` | non-terminating defs rejected | `diverging_mutual_pair` + W1 adversarial set | solid (hole fixed `d13d718`; antibodies = permanent regression guards) |
| `positivity` | strict positivity of datatypes | positivity gen challenges + W4 escape hatches (arrow-left, double-negation, sigma-hidden, through-constructor) | strong (deep walk; double-negation already rejected; sigma-hidden + through-constructor were live holes, found and fixed D4 red-green in `6148aff`) |
| `reflexivity` (+`forcing` gen) | conversion/normalization halts (refl ≡ deep-norm; `Conv.conv_within?`, fixed 500-unfold fuel) | `forcing_pair` | solid |
| `indexed/case` | dependent-case soundness | `branch_family`, `coverage`, `refinement`, `motive_wf`, `discharge`, `injectivity` | strong |
| `rewrite/eq` | propositional equality | `eq_formation`, `refl_typing`, `rewrite_premise`, `transport_type` | strong |
| `universes` | fixed hierarchy: no Type-in-Type, ceiling, cumulativity, two-universe ctor-field rule | `type_in_type`, `ceiling`, `cumulativity`, `stratification`, `ctor_field` | strong |

Note: the `forcing` generator is **not** an unwired dot-pattern stub — it feeds
the `reflexivity`-as-normalization assay. Row 24 (a *forced/dot-pattern*
vertical) is separate future work that reuses the name only loosely.

### 3.2 Expansion ledger

| # | Expansion | Type | What it closes | Layer | Priority |
|---|---|---|---|---|---|
| A1 | Fix mutual-recursion termination so `diverging_mutual_pair` replays `:ok` | turn hole green | the one live soundness infection (ledger #13) | E + A | ✅ done (`d13d718`; antibody replays `:ok`) |
| A2 | Bank occurs-check/cycle + deletion-rule antibodies in `indexed/case` | coverage fill | kernel has both rules, neither has a named antibody (ledger #23) | A | ✅ done (deletion antibody + occurs pin banked; TCB gap in `Term` fixed en route, `360402b`) |
| A3 | Bank nested / through-constructor / negative-position positivity antibodies | coverage fill | classic positivity escape hatches (ledger #19) | A | ✅ done (three escape hatches banked; sigma-hidden + through-constructor holes found+fixed per W4 audit, `6148aff`) |
| A4 | New `universes` vertical: reject `Type:Type`, prove cumulativity sound, reject two-universe ctor-field violation | new vertical | kernel enforces universes but nothing tests them (ledger #20 has zero Antigen coverage) | A | ✅ done (universes vertical banked) |
| A5 | New `conversion`/def-eq vertical: distinct normal forms never judged equal (β/η soundness), complementing `reflexivity`'s halting check | new vertical | NbE `Conv` soundness only half-covered | A | medium |
| A6 | New `ctor-formation` vertical (or extend `indexed`): result-index shape, param uniformity, telescope well-formedness in `check_ctor` | new vertical | datatype *formation* rules under-tested | A | medium |
| A7 | New surface `.cure` vertical: elaborate through `Cure.Elab.Program` to prove ④'s `missing_branch`/`reachable_impossible`/impossible-clause behavior | new vertical | ④ currently slated for a plain regression corpus, not Antigen (ledger #25) | A + E | medium (post-④) |
| A8 | **Term-generator metatheory engine** — StreamData-backed generated corpus w/ known-label totality, swappable backend | architectural | turns every vertical from regression net into soundness *evidence* (ledger #22) | A | 🔵 biggest leverage (designed) |
| A9 | Broaden mutual-recursion challenges beyond one pair (longer cycles, indirect, guarded vs unguarded) | coverage fill | depth behind A1 | A | ✅ done (subsumed by W1 adversarial set) |
| A10 | Wire per-vertical generators into A8's generated stream once the engine lands | integration | makes A8 actually cover the verticals | A | follows A8 |

### 3.3 Shape of the Antigen work
- **A1 is closed** (`d13d718`): the checker conservatively rejects every mutual cycle and the banked antibody replays `:ok`. What remains of mutual recursion is *reach* (accepting well-founded groups — transliteration program P1), not soundness.
- **A2–A4 are cheap, high-value** — the kernel already enforces these rules; we
  bank antibodies that prove they stay enforced. A4 tests an entire kernel
  subsystem (universes) with *zero* current Antigen coverage.
- **A8 is the capability jump** — everything today is hand-built known-label
  challenges. The term generator lets Antigen claim "sound over a generated
  space" rather than "these specific cases stay fixed." A10 is its follow-on.

## 4. Explicitly out of scope (new capabilities, not parity)

These are not "quality gaps in things we support" — they are features Cure does
not have, and are excluded from this roadmap by construction:

- Linear / quantitative types (Idris 2 QTT).
- Interfaces / typeclasses at Idris depth (Cure has protocols; not the same reach).
- `%default total`/`covering`/`partial` totality modes as a language surface.
- Elaborator reflection / `%macro`.
- Named and auto-bound implicit arguments as a first-class feature.
- Nested/deep pattern compilation to a case tree **as a capability** appears as
  ledger #3 only because the kernel already nests — it is a reach item for our
  existing single-level matching, not a new domain.

## 5. Suggested sequencing (dependency-ordered, post-④)

1. **④ merges** (rows 2, 8, 16 land; unblocks A7/#25).
2. **A1 / #13** — close the one live soundness hole (mutual-recursion termination).
3. **A2, A3, A4** — cheap antibody/vertical fills; A4 covers an untested kernel subsystem.
4. **#7** — automatic `rewrite` motive inference (largest ergonomic gap in equality).
5. **A8 / #22** — the term-generator metatheory engine (assurance jump), then A10.
6. **#3 → #17, #4, #5 → A24** — pattern-matching reach (compiler pass, then forms, then forcing + its vertical).
7. **#10, #11** — inference-unification depth (Miller patterns, postponed constraints).
8. **#14, #6, A5, A6, A9** — remaining depth/ergonomics as capacity allows.
