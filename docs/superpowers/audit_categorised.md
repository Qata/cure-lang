# Raw Audit — Categorised

Source: `docs/superpowers/raw_audit.txt` (~640 findings). This index groups the
findings, flags the heavy cross-document duplication, and separates the
**Tier 1** kernel cleanup (the "stuff only we have" — the near-term focus) from
the **Tier 2** broad compiler/stdlib/tooling hygiene sweep.

## Document structure

The file is **two documents concatenated**:

- **Doc 1 — "Cure Issues" (items 1–18)** — a curated, pre-deduplicated cleanup
  plan for the dependent kernel; each item has Goal / Change / Main files.
  Item 18 = recommended implementation order.
- **Doc 2 — items 1–640** (prefixed "0. Correction from earlier diffs") — a raw
  full-system sweep. Internal runs:
  - **1–520**: broad compiler / stdlib / codegen / tooling / security audit.
  - **521–569**: "Cure vs Lean/Agda/Idris references" — kernel divergences.
  - **570**: "immediate priority vs references" note.
  - **571–639**: granular kernel/elab code-level findings.
  - **640**: "most urgent kernel-surrounding cleanup" note.

**Key dedup fact:** Doc 1 (18 items) is a distilled view of Doc 2's kernel
portion (521–640). Doc 1's own items 1–17 also re-appear inside Doc 2's 1–520
run (e.g. legacy Pi/Sigma, Nat==Int). Below, each Tier-1 category lists the
Doc 1 items and the Doc 2 items that restate them, so we plan once per concept.

The audit names its own priorities: **Doc 1 item 18**, **Doc 2 item 570**, and
**Doc 2 item 640** are the three "do this first" notes — cross-check any plan
ordering against them.

---

# TIER 1 — Dependent kernel / Core soundness ("only we have")

These are the divergences from real dependent languages. This is the focus.

## K1 — Primitive equality, the `refl` atom, and the rewrite node
Retire primitive `{:eq}/{:refl}/{:rewrite}` + `:veq/:vrefl/:cure_refl`; use the
builtin inductive `Eq`/`refl` end-to-end; lower surface `rewrite` to an Eq
eliminator/transport. **This is the single most-duplicated theme.**
- Doc 1: **2** (remove primitive eq/refl/rewrite), **3** (rewrite → Eq
  eliminator), **4** (proof-token equality).
- Doc 2: **521** (primitive prop-equality layer), **522** (rewrite emits
  primitive nodes), **523** (ad-hoc rewrite "bridge step"), **552** (elaborator
  hardcodes `"Eq"`/`"refl"`), **560** (three competing equalities), **567**
  (erasure = evaluating rewrite away), **568** (`Eq` not fully inductive),
  **577** (kernel accepts both prim + inductive Eq), **578** (Eq recognition
  hardcoded to `:Eq`), **589** (termination still knows prim eq/rewrite), **590**
  (positivity still knows prim rewrite), **260** (legacy equality = blind
  structural subst), **261** (`:cure_refl` still exposed), **37** (runtime `Eq`
  protocol not segregated from propositional Eq), **442** (examples depend on
  `:cure_refl`).

## K2 — Primitive operations in Core; type them properly
`{:prim, op, args}` should not be the operation model; ops need real typed
signatures before entering Core. Includes Bool-as-hardcoded-atoms.
- Doc 1: **13** (remove `{:prim,op,args}` as op model), **14** (proof-producing
  comparison APIs).
- Doc 2: **527** (prim ops = separate node vs typed constants), **528** (partial
  arithmetic folded into defeq too loosely), **607** (`infer_prim` types div as
  total), **608** (`infer_prim` still accepts numeric `:eq`/`:ne`), **609** (prim
  op fallback stuck in evaluator), **33** (prim ops spread across layers), **34**
  (div/rem weakly typed), **35** (float prim reduction policy).
- Bool-as-prim sub-cluster: **546** (Bool split: hardcoded atoms vs registry),
  **579** (`:True`/`:False` hardcoded in kernel), **627** (CoreBridge → bare
  `:True`/`:False`), **631** (Reduce folds bool ops at surface), **55** (constant
  folding uses Erlang booleans vs inductive Bool), **559** (runtime/protocol Bool
  mismatch).

## K3 — Holes in final Core
Allowed during elaboration; must never survive into final/trusted Core.
- Doc 1: **1** (final-Core holes).
- Doc 2: **524** (kernel accepts holes as terms), **102** (emit hole-check erases
  before checking), **292** (`_` in value position treated as hole), **293**
  (hole numbering only walks 3-tuples), **20** (`Types.Holes` → new policy),
  **323** (`Holes.render` uses legacy display).

## K4 — The `absurd` marker lives in Core syntax
Should be elaborator-only unreachable marker, not a Core term.
- Doc 2: **566**, **571**.

## K5 — Index unification / branch-skipping / coverage (soundness-critical)
The heart of dependent `match`; conservative and known-incomplete.
- Doc 1: **15** (keep practical indexed matching, don't chase full Agda).
- Doc 2: **532** (skips "impossible" branch bodies), **533** (arity mismatch
  ignored), **534** (defeq ignored except syntactic), **572** (`check_case_branches`
  skips bodies), **573** (`unify_indices` no length check), **574** (`unify_spine`
  mismatch → success), **575** (drops `:undecided`), **576** (`branch_unify`
  `:impossible` on unknown ctor/family), **635** (coverage: no duplicate-branch
  check), **636** (impossible vs missing ctor not distinguished), **543**
  (`check_coverage` = set inclusion only), **563** (no principled
  coverage+unification report), **601–606** (branch-subst internals:
  `replace_branch_vars` catch-all success, `specialize_branch_context` reify/eval,
  `bind_index` binds outer vars, 100 000-depth bound, `occurs_index?`
  over-approx, `strongly_rigid_occurs?` only ctor/data spines), **254–256**
  (exhaustiveness treats pin/unknown-ctor as wildcard; redundancy calc broken),
  **257** (pattern checker hardcodes Option/Result/List/Bool).

## K6 — Flat data values / lost constructor identity
Values flatten params++indices; ctors carry no family/param identity → forces
checking mode and repeated re-splitting.
- Doc 2: **531** (quoted data lossy without signature), **544** (flatten
  params/indices in values), **545** (parameterized ctors can't infer), **597**
  (case repeatedly splits flattened data), **598** (ctor values lack
  family/param identity), **599** (kernel rejects parameterized-ctor inference),
  **600** (result params/indices computed by eval, opaque rep).

## K7 — Universes / levels
- Doc 1: **9** (remove fixed `Type 0..2` ceiling), **10** (universe-polymorphic
  globals + level params).
- Doc 2: **525** (universe machinery far short of Lean/Agda/Idris), **563** (no
  level-metavar/universe-constraint integration in unification), **592**
  (field-level universe check too simple), **593** (`infer_sort` only exact
  `{:vtype}`), **611** (type formation doesn't reduce aliases before
  `infer_sort`), **612** (no cumulative coercion).

## K8 — Normalizer / conversion / defeq discipline
- Doc 2: **529** (frozen stuck-case expansion is bespoke), **530**/**583**/**409**
  (fuel in process dictionary, not nest-safe), **582** (`:fuel_exhausted`
  returned as term-like), **410** (option validation raises), **550**
  (`Types.Reduce` parallel normalizer), **557** (reify WHNF/NF without
  signature-aware quote in public paths), **558** (η for functions but not
  records/Σ), **584** (same-neutral-before-δ shortcut), **585** (no principled
  transparency mode), **547** (norm/quote can produce terms kernel rejects),
  **610** (`{:global}` eval always opaque; δ only in norm/conv), **630** (Reduce:
  CoreBridge then structural surface recursion).

## K9 — Metavariables / unification / elaborator internals
- Doc 2: **535** (metas not contextual enough), **536** (Miller solver emits
  unchecked solutions), **537** (final-Core meta rejection not centralized),
  **538** (multiple non-reference fallback elaboration strategies), **614**
  (`MetaCtx` stores type but not local context), **615** (WHNF pre-reduction
  disabled under binders), **616** (WHNF lambda-from-non-lambda), **617** (Miller
  detection lacks explicit spines), **618** (Miller peels Pi syntactically),
  **619** (Miller solutions not type-checked against meta type), **620/621**
  (`has_meta?` catch-all false; ignores motives/branches), **622**
  (`finish_global_app` swallows expected-type unify failure), **623**
  (`elaborate_free_name` → global fallback for any unknown), **624**
  (`elaborate_type` unknown var → data family), **625** (`elaborate_named_call`
  spine of unknown globals), **626** (a second elaborator subset at file bottom),
  **554** (`System.get_env` inside elaboration).

## K10 — Legacy parallel dependent systems (Pi/Sigma/Reduce/CoreBridge/legacy SMT)
Second dependent calculus that shadows the real Core; mostly off the main path
already, but still referenced (esp. by Antigen oracles).
- Doc 1: **11** (legacy SMT-backed dependent system).
- Doc 2: **548** (legacy dep system not comparable to Agda/Lean/Idris), **549**
  (Pi/Sigma = second calculus), **550** (`Types.Reduce` parallel), **551**
  (CoreBridge surface vars → globals), **12** (legacy routing misses constructs),
  **13** (legacy `Nat == Int`) + **508** (`Std.Nat` and `Nat==Int` coexist),
  **14** (Pi/Sigma parallel), **15** (Pi erasure/subst too weak), **16** (Sigma
  admits `Any`), **17** (type-level reducer parallel), **288–291** (legacy
  compat: missing constraints "compatible", no implication proof, VC truncation,
  no value-param subst), **69/70** (CoreBridge vars→globals, interns atoms),
  **89** (CoreBridge + SMT parallel type-level semantics), **318** (still creates
  globals for unresolved names), **629** (function calls → globals via
  `String.to_atom`), **632/633** (legacy Pi zip; Sigma `:any` fallback).

## K11 — Trusted boundary: certification, final-Core invariant, subject reduction
- Doc 1: **12** (Core totality certificates authoritative), **17** (final-Core
  invariant enforced globally).
- Doc 2: **555** (`check_def` runs before final-readiness), **556** (certify /
  certificate pipeline too weak for trusted reduction), **562** ("kernel
  re-checks it" used as substitute for elaborator invariants), **586**
  (`check_def` doesn't enforce final-Core invariants), **587**
  (`validate_certificate` insufficient while `Env.certify` public), **588**
  (termination call graph walks proof/type positions), **411** (totality counts
  globals in non-computational positions), **637** (no final-Core grammar
  boundary), **638** (no subject-reduction regression harness), **639** (no
  progress-style final-Core gate), **140** (`Env.certify/2` public, proves
  nothing), **49** (Antigen needs final-Core invariant assays), **48** (artifact
  format should encode final-Core invariants).

## K12 — Bare-atom globals/constructors & missing symbol table (kernel-relevant)
- Doc 2: **526** (globals are bare atoms), **634** (kernel/elab depend on
  bare-atom ctor/family collisions), **578** (`:Eq` hardcoded — see K1), **97**
  (Core env silently overwrites defs/families/ctors), **98** (ctor namespace
  global + unqualified), **99** (nullary ctor collides with atoms), **100**
  (imported dependent globals emit as local calls), **129** (source-name→atom is
  pervasive; needs a compiler symbol table), **70** (CoreBridge interns names).
  *(The broad `String.to_atom` sweep is Tier-2 §T10; only the kernel-facing
  subset is here.)*

## K13 — Refinements / SMT trusted only as lint, not proof (dependent/final mode)
- Doc 1: **7** (refinements + SMT are warning-only in final/static/dependent).
- Doc 2: **262/263** (refinement base types via legacy resolver; result can't
  represent unknown), **30** (guard refinement/exhaustiveness advisory when
  solver absent), **87/88** (Path/PatternRefinement ignore unsupported guards),
  **192** (`Std.Refine` predicates are runtime Bool, not proofs), **502**
  (`Std.Refine.PositiveFloat`/`Probability` use Float predicates).
  *(Aligns with the locked "Z3 out of the TCB" decision — keep as untrusted lint.)*

## K14 — `Any` removed from the sound modes
- Doc 1: **8** (remove gradual `Any` from static/dependent/final mode). The
  pervasive `Any` escapes elsewhere are Tier-2 §T2; this item is the kernel-mode
  policy that governs them.

---

# TIER 2 — Broad compiler / stdlib / tooling / security sweep (Doc 2, ~1–520)

Not the current focus, but catalogued so nothing is lost. Grouped by theme with
representative Doc 2 item numbers/ranges.

- **T2 — `Any` gradual-typing escapes (non-dependent checker):** 18, 19, 22–29,
  38–41, 178–181, 349, 353–355, 402–407, 448–462, 484–487.
- **T3 — Effects & totality/partiality typing (functions typed pure/total that
  aren't):** 4–11, 71–80, 85–86, 234, 356/490, 460, 463–476, 491–498; extern
  effect/arity 6–8, 82.
- **T4 — Stdlib type-fidelity (signatures lie about shapes):** 36, 182–198,
  230–233, 240–242, 264–265, 473–520 (large `Std.*` cluster), 519–520 (map/set
  ordering).
- **T5 — Codegen / lowering soundness (unknown → `:undefined`/`:ok`/`inspect`):**
  45, 60–66, 114–116, 146–152, 199–202, 210, 350–352, 408, 412–419, 199, 60.
- **T6 — Optimizer / PGO not rechecked after type-checking:** 51–54, 84,
  106–110, 51.
- **T7 — Protocols / sessions / FSM / temporal semantics:** 46, 56–59, 153–172,
  211–222, 281–283, 313–317.
- **T8 — Trace / replay / runtime instrumentation (unsafe deser, global dbg,
  public ETS):** 203–204, 223–229, 375–378.
- **T9 — Packaging / registry / release / signing / transparency / MCP
  (supply-chain trust):** 42–44, 90, 119–129, 245–253, 266–270, 306–308,
  327–346, 388–393, 431–437, 359–360.
- **T10 — Untrusted `String.to_atom` interning (DoS / atom-table exhaustion):**
  70–72, 115, 121, 127–129, 141, 168–171, 173, 196, 243–244, 304, 309, 333, 339,
  342, 445 — audit's own remedy note at **129** (compiler symbol table).
- **T11 — LSP / MCP / docs / CLI tooling (parse-only, not checked; crashes):**
  41, 266–280, 299–305, 321–325, 361–372, 379–387, 394–401, 420–430.
- **T12 — Build-mode / trust configuration (checking off by default):** Doc 2
  **1** (release defaults to no type checking), **2** (opt-out must be
  mode-gated), **3** (stdlib preload ignores compile failures), 21 (`unsafe`
  keyword needed), 47–50, 91–94, 477–487, 513–517.
- **T13 — Antigen harness updates:** 49, 205, 309–312, 442; plus embedded
  "update Antigen" clauses in Doc 1 items 1 & 2.
- **T14 — SMT tooling (parser/solver plumbing, distinct from K13 policy):**
  67–68, 206–207, 284–287, 322, 144.

---

# Cross-cutting duplicate clusters (plan once, touch many)

1. **Equality/refl/rewrite** (K1) — the biggest: ~19 findings across Doc 1
   {2,3,4} and Doc 2 {37,260,261,442,521,522,523,552,560,567,568,577,578,589,590}.
2. **Primitive ops + Bool-as-atom** (K2) — Doc 1 {13,14} + Doc 2
   {33,34,35,55,527,528,546,559,579,607,608,609,627,631}.
3. **Holes** (K3) — Doc 1 {1} + Doc 2 {20,102,292,293,323,524}.
4. **Index unification / coverage** (K5) — Doc 2 {254–257, 532–534, 543, 563,
   572–576, 601–606, 635, 636}.
5. **Legacy parallel dependent systems** (K10) — Doc 1 {11} + Doc 2 {12–17,
   69,70,89,288–291,318,508,548–551,629,632,633}.
6. **Fuel-in-process-dictionary** — Doc 2 {409, 530, 583} are the same defect
   reported three times.
7. **`String.to_atom` interning** — K12 (kernel) + T10 (broad) are one root
   cause; a compiler symbol table (Doc 2 #129) closes both.
8. **Trusted boundary / final-Core invariant** (K11) — Doc 1 {12,17} + Doc 2
   {48,49,140,411,555,556,562,586,587,588,637,638,639}.

# The audit's own priority notes
- **Doc 1 §18** — recommended implementation order for the kernel cleanup.
- **Doc 2 §570** — "immediate priority versus references."
- **Doc 2 §640** — "most urgent kernel-surrounding cleanup from this pass."
Reconcile any plan ordering against these three before locking sequence.

---

# Tackle order (Tier 1), reconciled across §18 / §570 / §640

The three priority notes agree strongly. The key consensus: **all three lead with
a final-Core grammar + validator, not a removal** (§570 #1, §640 #1) — "remove
primitive X from final Core" only has teeth once a validator rejects X everywhere
(eval/normalise/certify/emit/serialize/release/publish). That validator is the
ratchet that makes every later removal enforceable and regression-proof, so it is
Wave 0.

Two deliberate deviations from the raw notes:
- Pull the validator to **Wave 0** (stronger than §18, which buries the grammar
  mid-list) because it de-risks everything after it.
- Split **K1** and **K5** into "acute now / deep later" so cheap soundness wins
  land early without waiting on canonical transport and the coverage report.

## Wave 0 — Enabler (before any removal)
1. **K11a — Final-Core grammar + validator scaffold** (grammar #637, validator run
   everywhere, subject-reduction #638 + progress #639 harness). *Consensus #1 in
   §570 and §640.*

## Wave 1 — Cheap, high-consensus trust-boundary removals (localized)
2. **K3 — Holes out of final Core.** *§18 Phase 1 #1; one kernel clause + emit check.*
3. **K1a — Kill primitive `{:eq}/{:refl}/{:veq}/{:vrefl}`; temporarily reject
   surface `rewrite`.** *#2 in both §570/§640. Inductive `Eq` already exists
   (task #90). §18's temp-reject device (Phase 1 #3) resolves the
   rewrite→primitive back-bridge; canonical transport is Wave 5.*
4. **K5a — Acute index-unifier soundness fixes** (`unify_spine` mismatch→success
   #574, stop dropping `:undecided` #575, length-check #573). *§640 #3/#4.*
5. **K13 — Reject unknown SMT/refinement obligations in final mode.** *§18 Phase 1
   #7; matches the locked "Z3 out of the TCB, lint-only" decision.*
6. **K14 — Ban `Any` in static/dependent/final mode.** *§18 Phase 2 #8; mostly
   enforced for free by the Wave-0 validator.*

## Wave 2 — Bounded representation cleanups the kernel leans on
7. **K4 — `absurd`: encode as checked empty-elimination / elaborator-only marker.**
   *§640 #5. Shallow.*
8. **K6 — Flat data values → params/indices stored separately + constructor family
   identity.** *§640 #7.*
9. **K12 — Bare atoms → qualified symbol IDs (+ compiler symbol table).** *§570 #5,
   §640 #6. The one heavy structural lift early; also removes K1's `:Eq`
   hardcoding; prerequisite for universes (globals carry level args).*

## Wave 3 — The primitive model
10. **K2 — Typed primitive globals** (registry: type/effects/totality/reducer/
    lowering; classify logic-total / runtime-total / partial / effectful / unsafe;
    rework emit/eval/Antigen; finalize Bool-as-inductive). *§18 Phase 4, §570 #3,
    §640 #9.*

## Wave 4 — Universes
11. **K7 — Universe polymorphism** (level exprs/metas/constraints, cumulativity,
    level params on globals, universe-poly `Eq`). *§18 Phase 3, §570 #4. Gated on
    K12.*

## Wave 5 — Collapse legacy + practical dependent payoff
12. **K10 — Collapse legacy Pi/Sigma/Reduce/CoreBridge/legacy-SMT dependent out of
    the trusted path.** *§640 #10. Mostly dead-code deletion once the Antigen
    oracle is repointed at real Core.*
13. **K1b + K5b — Canonical `Eq.rec`/transport; rewrite→transport (undo Wave-1
    temp reject); deep indexed-pattern/impossible-branch strengthening;
    proof-producing comparisons.** *§18 Phase 5 — the phase that pays off the
    FRP-paper goal.*

## Continuous hygiene (fold in, do not gate on)
- **K8** normalizer/conversion (fuel-out-of-process-dictionary is trivial;
  principled transparency-mode is bigger).
- **K9** meta/elaborator internals (type-check Miller solutions, complete
  `has_meta?`).
- **K11b** authoritative certification + relevance/erasure integrated into binders
  (§570 #9).
