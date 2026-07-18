# Elaborator gaps — verified status (2026-07-18)

**Status:** investigation complete. Six independent Sonnet agents, each in isolation,
re-verified the six OPEN items from the handoff
(`2026-07-18-open-elaborator-gaps-handoff.md`) — E9, E6-residual, E8, E2-residual, E10,
E11-Stage-2 — **empirically** against the live elaborator on branch `elaborator-gaps`
(HEAD `235d20d1`), with a differential Idris2 cross-check where the "Idris accepts" claim
was load-bearing. This spec records what is actually true as of this commit, separates the
**kernel-layer** bugs (Antigen targets) from the **elaborator/parser** gaps, and captures
the findings that overturn the catalog's own framing.

Method per gap: build a faithful `.cure` repro, get Cure's real verdict via
`Cure.Elab.Program.elaborate/1`, root-cause in the **dependent** pipeline
(`lib/cure/elab/*` + `lib/cure/core/*`) only — the `lib/cure/compiler/*` and
`lib/cure/types/*` same-named symbols are decoys and were explicitly excluded — and, where
relevant, run `idris2 --check` on the byte-equivalent program. No `lib/**` was modified.

## 1. Summary

| Gap | Verdict | Layer | Fix shape | Reach gap? |
|---|---|---|---|---|
| **E9** — stuck-index eqn on GADT match | OPEN; **premise falsified** | K (+E) | headline: architectural & beyond-Idris; sub-bug: trivial kernel fix | **NO** for the headline (Idris rejects too) |
| **E6-residual** — shared metacontext | OPEN | E | **architectural** (thread one metacontext; ~6 entry points) | YES |
| **E8** — sequential-match refinement | OPEN; **narrower than catalog** | E | **bounded-for-repro** (carried-eq detour) | YES |
| **E2-residual** — name relevant ctor index | OPEN; **design-gated, not bounded** | E | new surface grade syntax + quantity policy | YES |
| **E10** — HO-fn arg not reduced in index | OPEN; **root cause overturned** | (a) P + K, (b)/(c) K | (a)-parser trivial; kernel part HARD-STOP | YES (all three, Idris-verified) |
| **E11-Stage-2** — type-directed overload | OPEN; **not landed here** | E | **bounded** (wire overload into index path) | partial |

**Net:** none were already fixed; none is trivial-and-done. Two carry a **kernel** bug
(E9 sub-bug, E10 (b)/(c)); two were **mis-framed** by the catalog (E9 premise, E10 root
cause); two are **more bounded than feared** (E8, E11-Stage-2); two are **bigger than the
handoff's ordering implied** (E2-residual, E6-residual). Two **new** bugs surfaced that the
catalog did not list (E11 elaborator crash, E10a parser misparse).

## 2. Kernel-layer bugs — the Antigen targets

These are the items the Antigen expansion must trip on **before** any kernel change. Both are
**completeness** gaps (Cure is conservative — it rejects/undecides a term Idris accepts), not
soundness gaps; the trusted kernel never accepts anything ill-typed. So the antibodies are
**must-eventually-decide / must-certify** reach pins, not "never-equate-distinct-NF" pins.

### K-bug 1 — order-dependent constructor-injectivity in `unify_one`/`bind_index`
- **File:** `lib/cure/core/kernel.ex`, `unify_one/4` (~1330–1428), `bind_index/4` (~1465–1503).
- **Symptom (differential, order-flip):** `Equivalent(Nat, S(a), S(Z()))` (var first) →
  `:conversion_failure`; `Equivalent(Nat, S(Z()), S(a))` (ground first) → **ACCEPT**. The
  decidable equation is silently dropped in one argument order only.
- **Cause:** the top-level r/s var-side asymmetry ("r-side vars `< arity`, s-side vars
  `>= arity`") is violated in the resolve-before-bind re-unify path (`bind_index` ~1498 calls
  `unify_one(old, rterm, ...)` on arbitrary previously-bound terms). There is a clause for an
  outer var on the **right** (`unify_one(r, {:var,j}, ...) when j >= arity`, ~1336) but **none
  for it on the left**, so that pair falls through to `:undecided` and is dropped.
- **Antibody shape:** a symmetric-decidability pin — for a ground/var constructor-injectivity
  pair, both argument orders must reach the same verdict. Currently red for the var-first order.
- **Fix (HARD-STOP, TCB-approved):** add the missing symmetric `unify_one` clause (or
  canonicalize argument order before the re-unify). Aligned with Idris/Agda/Lean (symmetric
  constructor injectivity is standard).
- **Caveat:** this does **not** unblock the E9 headline (`msadd(m1,m2)` stays correctly
  `:undecided` — it is a non-injective stuck app, not a var/ctor pair).

### K-bug 2 — size-change checker rejects guarded-lambda recursion (`certificate.ex`)
- **File:** `lib/cure/core/certificate.ex`, `size_change_total?/2`, `walk_node/4` for
  `{:lam,...}` (~197–198), `arg_relation/2` (~320–334).
- **Symptom:** a continuation-style `bind` whose recursive self-call sits **inside an
  unapplied lambda** (`Bind(e,g) -> Bind(e, fn(y) -> bind(g(y), f))`) fails certification, so
  `Cure.Core.Conv` (δ-unfolding gated on `Env.certified?`, `conv.ex:10–15`) treats `bind` as
  **opaque and never δ-unfolds it**. Every `bind(...)` in a type/index position is therefore
  stuck (`:conversion_failure`), independent of the continuation's shape.
- **Cause:** `walk_node` descends into the unapplied-lambda body and evaluates the call
  argument `g(y)` (an application of a bound field, not a bare var/ctor), so `arg_relation`
  returns `:unknown`, no diagonal `:smaller`, certification fails. A genuine incompleteness of
  the Lee–Jones–Ben-Amram port vs Idris's real `Core/Termination/SizeChange.idr`.
- **Differential:** byte-equivalent `bind` + all three `Refl` goals **type-check in Idris2**
  under `%default total` (harness sanity-checked against a real non-terminating loop, which
  Idris rejects). So this is a true reach gap.
- **Antibody shape:** a must-certify pin — a guarded/deferred self-call under an unapplied
  lambda that is genuinely size-change-terminating must certify (and thus δ-unfold in
  conversion). Currently red.
- **Fix (HARD-STOP, TCB-approved):** extend the size-change criterion to recognize
  guarded/deferred self-calls under an unapplied lambda as not owing the decrease at that
  syntactic point (mirror Idris's checker). **No elaborator-only route exists** — the blocker
  is that `bind` never certifies at all.

## 3. Elaborator / parser gaps (fix after the kernel bugs are green)

### E11-Stage-2 — type-directed overload in type/index position — **OPEN, bounded**
- **Not landed here** despite `autopilot/type-directed-overload-resolution` (`d30c72a8`) being
  an ancestor: that branch shipped Ph1 overload for **term position only**
  (`elaborator.ex:elaborate_named_call_resolved`, ~335–344). The type/index-lowering path
  (`declarations.ex:lower_applied_type_head/7` ~2190, `applied_def_key/3` ~2243) still runs the
  pre-Ph1 Stage-1 logic and was never wired to `Overload.resolve/5` /
  `Resolution.overload_candidates/2`.
- **Evidence:** bare `plus(...)` in an `Equivalent` index → `{:ambiguous_name, :plus, [...]}`;
  qualified spelling accepts; term-position overload works.
- **Fix:** in `lower_applied_type_head`'s catch-all, check `overload_candidates`; if ≥2, infer
  each already-lowered index arg's type (new plumbing in `idx_to_core`/`map_idx_to_core`
  ~2584) and call `Overload.resolve/5`, mirroring term position. Bounded E edit.

### NEW — E11 elaborator crash on same-module-overload vs ambient provider
- When a bare name has a **same-module overload set** (discriminated keys, no bare local key)
  **and** an ambient/prelude same-name provider (e.g. `Std.Nat#plus`),
  `Resolution.resolve_bare`'s `prefer_direct` silently drops the local overloads and returns the
  ambient candidate as if unambiguous. The mis-resolved global is applied to the wrong ctor args
  and the elaborator **crashes with an uncaught `RuntimeError`** (`ι: no branch for constructor …`)
  out of `Cure.Elab.Program.elaborate/1` instead of a clean `{:error,_}`. **No workaround** for
  the same-module case (no qualified escape). The E11-Stage-2 fix (`overload_candidates` prefers
  local via `prefer_local`) also fixes this. Should at minimum fail closed, not crash.

### E8 — sequential-match refinement across scrutinees — **OPEN, narrower than catalog**
- Repro reproduced (`:rewrite_no_match`, `m` unrefined; helper-delegation control accepts).
  Traced (via `Cure.Dev.Trace`) to the **carried-index-equality mechanism**
  (`elaborate_carried_eq_branch`, landed `c6c98e93`), **not** to a missing simultaneous-matching
  architecture:
  1. `collect_index_siblings/5` (`elaborator.ex:3669`) **over-fires** — it treats an outer,
     already-consumed scrutinee as a transport sibling because it only excludes the *current*
     scrutinee var (fires 1/44 in the failing case, 0/46 in the control).
  2. When it fires, `cod_expected` (`elaborator.ex:5572–5575`) substitutes only the single
     carried index position and **drops the full `subst`** (which contains `m ↦ msadd(m1,m2)`)
     that the plain `refine_branch_goal` path threads correctly.
- **Fix (bounded, two candidates):** (a) tighten `collect_index_siblings` to exclude
  already-consumed enclosing scrutinees; and/or (b) thread the ctor's full `subst` through the
  carried-eq path. Tens of lines in `elaborator.ex`, red-green-able.
- **Caveat:** verified for the documented repro shape only; broader E1-family shapes that never
  trip the carried-eq detour were not tested and may still be larger.

### E6-residual — shared metacontext through the app tree — **OPEN, architectural**
- Repro reproduced (`{:unsolved_metavariables, AStar0}`; typed-helper workaround elaborates).
  Root cause confirmed: `finish_ctor_app/6` (`elaborator.ex` ~7315) finalizes eagerly, and it is
  **systemic** — 6+ entry points each mint a fresh `MetaCtx.new()`
  (`elaborator.ex:7216/7378/7899/8069/8126`, `proof_search.ex:236`), so no solution crosses
  nesting levels. The E6 **core** (direct sibling) is already fixed (`check_ctor_args`
  postponement, `fb4c240e`); this is the enclosing-application residual.
- **Fix:** ARCHITECTURAL — one `MetaCtx` created per top-level elaboration and threaded through
  the recursive descent, with per-ctor finalization postponed to the top-level solve. Multi-day
  refactor across most of `elaborator.ex`'s ctor/app paths. Typed-helper workaround stands.
- **Out of scope (do not "fix"):** the floating-OUTPUT-index `PStep` variant — rejected by
  Idris too; reformulate the index family instead.

### E2-residual — name a relevant ctor index existential — **OPEN, design-gated**
- The naming/binding machinery already works (a bound-but-unused named implicit elaborates).
  The wall is downstream: `declarations.ex:1556–1562` hardcodes ctor-index quantity purely by
  **surface position** (auto-implicit ⇒ erased/quantity-0), and `erase.ex` genuinely drops those
  fields from the runtime tuple — so the `{:erased_used_relevantly}` rejection is a **sound
  erasure gate**, not a patchable false-positive. Commit `4cf73e9d` (2026-07-18) *hardened* this
  same wall, confirming it is treated as correct behavior.
- **Fix:** needs a **design decision + new surface syntax** for per-slot grades on constructor
  fields (the deferred QTT-grades item), a quantity-policy change in `declarations.ex`, and a
  third pattern-slot category (implicit-at-application / relevant-at-runtime) in
  `constructor_pattern`/`branch_scope`/`split_named_implicits`. Not a bounded edit.
- Explicit-field + congruence-helper workaround still required (live in
  `lib/std/otp_conversation.cure`).

### E9 headline — stuck-index equation — **OPEN, but NOT a reach gap**
- The catalog's headline "Idris accepts via `with`-style abstraction" is **empirically false**
  for this repro. Three genuine Idris idioms (clause split, `case`, real `with … proof p`) all
  **reject** with `Can't solve constraint between msadd ?m1 ?m2 and MkMS 0 0 0`. Idris needs the
  same index-generalization helper Cure already has; the committed oracle pair is `rel=same`.
- The stuck `msadd(m1,m2)` index is a non-injective `{:app}` — `unify_one` correctly returns
  `:undecided` (kernel, correctly conservative; not a bug). Closing the stated "definition of
  done" would require **inventing** auto-synthesis of an `Equivalent(I, ctorIdx, scrutIdx)`
  hypothesis on stuck index pairs — machinery **beyond Idris parity**, architectural, lower
  payoff than advertised. The index-generalization workaround stays (used by both sides of the
  oracle). The only actionable kernel item from E9 is **K-bug 1** above.

### NEW — E10a parser misparse — **trivial, P-layer**
- `maybe_parse_function_type/2` (`parser.ex:7534–7552`) mis-parses a `fn(y) -> …` lambda literal
  in **type/index** position as a parenthesized arrow-type, emitting a bogus `Function(y,…)` node
  → `:unknown_global` (the doc's claimed `Eval.apply` crash was **not** reproduced at HEAD). Term
  position parses the lambda fine. Small bounded parser fix; independent of the kernel work, but
  fixing it alone changes E10a's symptom to the same `:conversion_failure` as E10 (b)/(c) — it
  does not reach acceptance without K-bug 2.

## 4. Execution order (this thread)

1. **This spec** (done).
2. **Antigen red** — antibodies for K-bug 1 and K-bug 2; verify each is red at HEAD.
3. **Kernel fixes (HARD-STOP, TCB-approved)** — green K-bug 1 then K-bug 2; each with red-green +
   new antibody + full Antigen + full suite as its own reviewed step. Note K-bug 1 does not close
   the E9 headline; K-bug 2 is the sole unblock for E10 (b)/(c).
4. **Elaborator/parser gaps**, tractability order: E11-Stage-2 + E11 crash (bounded) → E10a parser
   (trivial) → E8 carried-eq (bounded-for-repro) → E6-residual (architectural) → E2-residual
   (design-gated). Each: paired `.cure`/`.idr` oracle probe red-green, plus a negative antibody
   proving the widening admits nothing unsound. Remove the workaround it replaces from ≥1 real
   module and confirm `rel=same`.

Discipline throughout: ghost-writer commits, explicit pathspec, one build at the gate,
`cure_stricter` reproduced before fixing, tests immutable once green.
