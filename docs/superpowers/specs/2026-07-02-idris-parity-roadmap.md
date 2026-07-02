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
| 3 | Pattern matching depth | Nested/deep patterns → decision-tree compiler (M8.4). Kernel case already nests, so this is a lowering pass, not a kernel change. **Boundary hardened**: a nested constructor sub-pattern (`S(S(m))`, `C(Z(),y)`) now returns a clean `{:unsupported_pattern, :nested_constructor_arg}` instead of crashing `constructor_pattern` with a raw no-clause exception — the lowering pass itself is still the remaining work | E | additive (refactors match path) | ⬜ (clean boundary; compiler pending) |
| 4 | Pattern forms | Non-constructor patterns in dependent position (`_`, literal, as-patterns) handled, not merely rejected. **Variable/wildcard catch-all landed** (oracle `match/mt06_var_catchall`, accept/accept): a bare-variable (`x -> …`) or wildcard (`_ -> …`) arm covers every constructor not explicitly matched, binding the scrutinee (Idris/Lean variable-pattern coverage). Implemented in `elaborate_default_branch` (E) — each un-matched constructor is reconstructed `cname(fresh…)` (present-arg count from ctor `quantities`), the catch-all name is substituted by that reconstruction, and the branch routes through the ordinary matched-branch path, so index inversion + goal refinement still apply and an unsound catch-all body is kernel-rejected (soundness test: catch-all covering a reachable ctor at a wrong index rejects). Runs on the BEAM (multi-ctor coverage verified). No TCB. *Reach*: integer/atom **literal** patterns (distinct mechanism — equality dispatch, not coverage) and as-patterns binding subterms; catch-all whose var is rebound in its own body is conservatively rejected (`:shadowed_default`) | E | additive | 🟡 (var/wildcard catch-all; reach: literals, as-patterns) |
| 5 | Pattern matching | Forced/dot patterns + forced-argument erasure | E, C | additive | ⬜ |
| 6 | Dependent matching | `with`-abstraction (match on an intermediate, refine the goal) — *borderline; core to Idris matching quality*. **Capabilities A + B + sibling refinement landed** (`58037d6`, `8487c51`, `dbf874e`): block/inline `with <single-expr> [proof <name>]` over a **non-indexed** scrutinee. **A** refines the GOAL by the scrutinee's *value* via a value-abstracting motive `{:lam, ty, abstract_term(goal, e, 0)}` (the `motive_for` pattern, not index-refinement), in place as `{:case,…}`; strictly beyond `match` (oracle wi01: plain `match` on the same goal is rejected). **B** (`proof`) binds `<name> : Eq(T,e,pat)` per branch via an **Eq-arrow motive** `λw. Eq(T,e,w) → G[e↦w]`, branch `λ(pf).body`, `:case` discharged by `refl(e)` (oracle wi04, load-bearing). **Sibling refinement** (oracle wi05/wi06): in-scope params whose type mentions `e` are refined per branch by **proof-carrying transport** `{:rewrite, prf, λx.H_j[e↦x], h_j} : H_j[e↦pat]` (reuses the `:rewrite` primitive, whose checking is `Eval.apply`, not `reify`) and re-bound under the original name — composes with `proof`. Independent-sibling set only (`{:with_sibling_dependency_unsupported,_}` otherwise). Kernel accepted all three unchanged (no TCB). **Runs on BEAM** (`d5fc309`): value-level `with` lowers to a runtime `case` (refinement + proof erase; `proof` binds an erased placeholder), verified end-to-end (compiles, loads, runs identical to `match`). **LHS re-matching over an indexed view landed** (`bb17c88` P, `4f686fc`+`e96fff8` E): a with-clause may restate the parent LHS refined — `<parent-pat…> \| <with-pat> -> body` (parser `{:with_rematch_arm}`) — and `elaborate_with_rematch` routes it like an indexed `match`: `build_motive` generalizes the goal over the scrutinee's index vars, and the kernel's index inversion (`branch_unify` `{:solved, n:=S m}`) refines the branch goal AND every index-mentioning sibling (`w:SNat(n)` ↦ `SNat(S m)`) via `specialize_branch_context_subst`. `match_parent_lhs` (ports Idris `getMatch`) validates each restated LHS is constructor-refined (rejecting forced/`k+k` patterns). This is the **convoy**, and it is **sound with NO TCB change**: the index equation comes from the case eliminator (not index injectivity); the kernel validates every `{:data}` slot-split against the signature (`check_spine`), the split is not part of value identity (flat `{:vdata}`), and `conv?` is value-directed so the `reify` collapse equates no distinct normal forms (all three positively established + banked as Antigen antibodies `data_split_validation`/`reify_collapse_distinct`). Oracle wi07 (faithful indexed Nat-view) is now accept/accept. *Reach*: multiple with-exprs, named/dependent ctor args (P-layer — the singleton `SNat`-carrying workaround is used meanwhile), forced/arithmetic restated patterns (#5), nested/multiple `with`, guards in rematch arms, runtime use of a proof *term*. A residual `Quote.reify` split-collapse false-rejection remains on the **Eq-endpoint** path of `infer_type_value_sort` (`defc6cb` approach-b fixed only the Π/Σ domain + Eq-carrier); the principled repair is signature-aware `reify` (TCB), reach-pinned `reach_reify_split.sexp` (must-eventually-accept) | E, P | additive | 🟡 (A + B + sibling + indexed LHS-rematch; reach: multi/named-args/#5/codegen) |
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
| 22 | Assurance (meta) | **Term-generator metatheory engine** (StreamData-backed corpus, known-label totality) — turns the net into soundness *evidence*. **Tier B landed** (`2026-07-02-antigen-tier-b-term-generator` spec+plan): mode-directed dependent `gen_term(Γ,T)` over a versioned signature menu + dependent context generator, three differential self-consistency assays (`term/infer_check`, `term/subject_reduction`, `term/normalization`), and a binder-usage/reduction-activity health gate. Acceptance run: 0 infections over the generated stream, `→ healthy`. *Reach still open*: `conversion_termination`/`erasure_preservation` assays, ill-typed mutation corpus, `ChoiceSeq` backend, and a richer menu (Pi/Sigma goals, type parameters) — all deferred to a follow-up spec | A | additive | ✅ |
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

**Two known K-layer *reaches* (soundness-safe incompleteness): BOTH now CLOSED
via reviewed TCB runs.**

*(1) Stuck-eliminator normalization — ✅ CLOSED (`d37721f`, reviewed TCB run).*
The normalizer used to preserve stuck eliminators without δ-reducing their
targets: a stuck `case` never re-reduced its scrutinee, and `spine/2` only
unwrapped `napp`, so `nfst`/`nsnd` frames over a certified-global spine froze —
`nf(plus(plus(Z,n),Z))` and `fst(g(x))` stayed stuck even at top level. Fixed by
a single seam clause in `unfold_certified_head` (`normalise.ex`): when the spine
head is a stuck `ncase`/`nfst`/`nsnd`, whnf its target (threading `opts`, so
`delta: :none`/fuel honored) and, if a ctor/pair emerges, apply the same ι-rule
`eval` trusts, then re-apply the spine args. Conversion inherited the fix via
`conv_val?`'s existing `whnf_value` routing (`conv.ex` untouched). Gate met:
red-green kernel tests, the new `StuckElimDelta` Antigen antibody (termination +
soundness, with a banked negative control that must stay distinct), full Antigen
suite (106), full test suite (2256, 0 regressions). **Correction to the earlier
plan:** this does NOT retire rw07's bridge lemma. The seam reduces
`plus(plus(Z,n),Z)` to `plus(n,Z)` (inner stuck `plus(Z,n)→n`), but `plus(n,Z) ≡
n` is *genuinely not definitional* (needs induction / `plus_n_Z`), so
`conv?(plus(plus(Z,n),Z), n)` is correctly still `false` and the bridge remains
necessary for that rewrite. What the seam fixes is the real reduction gap
(stuck-δ-scrutinee `case` + `fst`/`snd` over certified-global spines), not any
equality requiring induction.

*(2) `check_motive_wf` reify-collapse — ✅ CLOSED (`defc6cb`, reviewed TCB run).*
`Quote.reify` collapses `{:vdata, name, args}` → `{:data, name, args, []}` (no
inductive sig to recover the param/index split). This was invisible except in
`infer_type_value_sort`, which inferred a Π/Σ/Eq motive body's sort by reifying +
re-inferring — so an **indexed family as a Π domain** (the *convoy* encoding of
`with` sibling refinement, `λw. Π(SNat(w)). …`) re-inferred with `:arg_arity` and
was wrongly rejected `:bad_motive`. **Fixed without touching `reify`** (approach
b, the smaller/safer of the two — `reify` feeds 11+ callers): the `{:vpi}`/
`{:vsigma}`/`{:veq}` clauses of `infer_type_value_sort` now recurse on the
sub-*values* directly, mirroring `infer/2`'s type-formation rules and bottoming
out in the existing direct `{:vdata,…}` clause — so acceptance equals a non-lossy
reify+infer, and a non-type domain still falls to `:not_a_type_value` (rejected;
proven by a banked negative control). `reify`/`conv`/`normalise`/elaborator
untouched. Gate met: red-green kernel test (positive accepted + negative control
rejected), Antigen `indexed/case` antibodies (both banked), full Antigen (106),
full suite (2258, 0 regressions). This unblocks the clean **convoy** encoding and
is a prerequisite for indexed-scrutinee `with` / views. The elaborator's
`resplit_data` workaround is now redundant-but-harmless (leave for a follow-up).
**Residual (approach-b did NOT cover):** the `{:veq}` clause value-recurses on
the Eq *carrier* but still **reifies the Eq endpoints** — so an `Eq` whose
endpoints are themselves indexed-family TYPE values (e.g. `Eq(Type, SNat(x),
SNat(x))` as a motive body) is false-rejected `:bad_motive` via the same
collapse. This is a live must-eventually-accept, reach-pinned in
`test/antigen/reach_reify_split.sexp` (`reify_split_gap_reach_test`); the
principled fix is **signature-aware `Quote.reify`** (a TCB change, Agda/Lean
prior art). The indexed with-rematch convoy (`elaborate_with_rematch`) is a sound
non-TCB *workaround* that never routes through this path, not the repair.

### The honest headline
Of 26 rows: **14 at parity, 12 remain, 0 live soundness holes** — the
transliteration-P0 audit landed ④'s rows 2/8/16 and #7's audited-complete
`rewrite` motive inference (rw07 now closed via the elaborator bridge lemma),
the pre-port banking run closed #13's mutual-recursion hole (now a reach item),
#19's nested positivity, and #23's missing antibodies, the post-merge port
run landed checked-mode expression-level `match` (#26, `fcdf5ce`) and
`with`-abstraction capabilities A + B + sibling refinement (#6, `58037d6`,
`8487c51`, `dbf874e`), and the Antigen Tier-B run landed **#22 / A8** — the
dependent term generator plus the three differential self-consistency assays and
the health gate (acceptance run: 0 infections over the generated stream, `→
healthy`). The remaining 12 are reach (#3–#6, #13, #14, #17, #26 — several now
*partially* landed: #4 var/wildcard catch-all, #6 capabilities A + B + sibling,
#26 checked mode),
ergonomics/inference (#10, #11), or assurance strength (#24, #25, plus A10's
still-open wiring of the *existing* verticals onto the generated stream).
With #22 landed, the next-highest-leverage items are the inference-unification
depth (#10 Miller patterns, #11 postponed constraints) and the pattern-matching
reach chain (#3 → #17, #4, #5).

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
| A8 | **Term-generator metatheory engine** — StreamData-backed generated corpus w/ known-label totality, swappable backend | architectural | turns every vertical from regression net into soundness *evidence* (ledger #22) | A | ✅ done (Tier B: `gen_term` + 3 differential assays + health gate; `2026-07-02-antigen-tier-b-term-generator` plan) |
| A9 | Broaden mutual-recursion challenges beyond one pair (longer cycles, indirect, guarded vs unguarded) | coverage fill | depth behind A1 | A | ✅ done (subsumed by W1 adversarial set) |
| A10 | Wire per-vertical generators into A8's generated stream once the engine lands | integration | makes A8 actually cover the verticals | A | 🟡 partial — the `:typed_term` stream feeds the three Tier-B differential assays (`term/*`); feeding the *existing* known-label verticals (totality/positivity/universes) from a generated stream remains open |

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
