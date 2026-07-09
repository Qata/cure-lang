# Canonical-Spelling Kernel Batch — Design (task #22)

**Date:** 2026-07-09. Two sibling below-the-judgement spelling fixes, one TCB-gated batch. Operator approval: fields-only conditional on "we lose nothing" — condition PROVEN by the 2026-07-09 kernel audit (verdict FIELDS-ONLY SAFE); nf readback fix per the reclassified `nf_ill_typed` finding. TCB blanket approval applies: both align Cure's kernel with Agda (params dropped at elimination; type-directed conversion; normalization preserves well-typedness).

## 0. Non-negotiables

- Diff confined to: `lib/cure/core/{eval,normalise,conv}.ex` (+ `quote.ex` ONLY if the B2 consumer audit requires a helper), `lib/antigen/generators/equality.ex`, new antibody test files. `lib/cure/elab/` and `lib/cure/compiler/` untouched. Elaborator already emits fields-only ctors — no surface change.
- Ghost commits, explicit pathspecs, ONE mix at a time, strict red-green per antibody.
- Tests immutable EXCEPT the enumerated flip class in §3.4 (each flip ledgered with per-item justification). Any other surviving-test edit = STOP.
- Baseline recorded at Step 0 (expected 3142/0/0 = post-firewall; do not assume).

## 1. Part A — fields-only constructor values (ledger #28)

**Audit facts this rests on (verified 2026-07-09, do not re-derive):** the kernel is ALREADY fields-only at every load-bearing site — ι binds `reverse(args) ++ env` with branch arity == field count enforced at type-check time (eval.ex:56-62, kernel.ex:708, reference value kernel.ex:729 is fields-only); erase drops grade-0 params (erase.ex:24-28); emit's BEAM tuples are tag+fields (emit.ex:179). Conversion's vctor comparisons (conv.ex:88-89 via length-strict conv_spine? :109-112; same_value_no_delta? :172-180) are safe under the **shared-type conversion invariant**: Conv is entered only on same-type pairs (kernel.ex:215, :261, :1070; meta_check.ex:20; elaborator.ex:3391, :3473; elab/unify.ex:321 — closed, meta-free), and a vctor comparison is reached only after the enclosing `{:vdata, family, params++indices}` already converted (conv.ex:85-86). Mixed spelling can only false-REJECT (length gates conv.ex:110, elab/unify.ex:341), never false-accept. The ONLY params-on-spine producer is the K6 ctor TERM form (kernel.ex:153-160 infer, :274-275 check→check_via_infer; added for Eq bridge_step, kernel.ex:144-151 comment), which yields a `{:vdata}` TYPE in inference — but nothing structurally prevents such a term from being evaluated and eliminated.

**Canonical spelling: fields-only.** Changes:

1. **A1 — ι-rule coercion (closes the K6 hazard).** At every ι site — eval.ex:56-62, normalise.ex:235-246, normalise.ex:269-288 — the branch tuple carries its declared `arity`; when `length(args) > arity`, bind only the LAST `arity` args (`Enum.drop(args, length(args) - arity)`): params precede fields on a K6 spine, so dropping the leading extras coerces to fields-only exactly. `length(args) == arity` binds as today (zero-cost on the canonical path). `length(args) < arity` is impossible for kernel-checked terms — leave behavior as today (no new error path; the kernel's type-check-time guard kernel.ex:708 owns that invariant).
2. **A2 — conversion mixed-spelling completeness.** In `conv_spine?`'s callers for vctor pairs (conv.ex:88-89) and `same_spine_no_delta?` (conv.ex:177-180): when lengths differ AND the signature resolves the ctor's field count F, coerce each side longer than F to its last F elements before the pairwise walk; if the signature cannot resolve the ctor, keep today's strict-reject. Sound by the shared-type invariant (dropped positions are type-determined); turns the false-reject into agreement, changes NO accept into reject.
3. **A3 — K6 term form UNCHANGED as a typing rule.** Inference of params-on-spine ctor terms stays (kernel.ex:153-160, :274-275); its values are now coerced at elimination (A1) and tolerated at conversion (A2). No elaborator change.
4. **A4 — antibodies** (new `test/antigen/ctor_spelling_antibody_test.exs`): (i) a case-elimination of a params-on-spine ctor term evaluates to the SAME result as its fields-only spelling (the de Bruijn misalignment repro — must FAIL red before A1); (ii) `Conv` equates the two spellings of one ctor value under a shared type (red before A2); (iii) nf/eval never bind more args than branch arity (property over the Antigen ctor generators, or a directed test if the generator hookup is disproportionate — executor judgment, ledgered).

## 2. Part B — signature-aware nf readback (nf_ill_typed class)

**Facts:** `Normalise.nf`/`whnf` read back via 2-arg signature-less `Quote.reify` (normalise.ex:31, :42), collapsing an indexed family's param/index split — `Equivalent` (1 param + 2 indices) reads back `{:data, :Equivalent, [Nat, Z, Z], []}`, which fails re-inference `:arg_arity`. The kernel already reifies WITH `Context.signature(ctx)` where it matters internally (kernel.ex:626-627) and documents the collapse (kernel.ex:647-650). Two real Antigen campaigns: every `Equivalent` infection is `nf_ill_typed` (389/389, 202/202), zero `not_idempotent`.

Changes:

1. **B1** — normalise.ex:31 and :42: reify with the context's signature (same form kernel.ex:626-627 uses), so `{:vdata}` readback splits params/indices per the family record.
2. **B2 — consumer audit (BEFORE B1 lands).** Enumerate every 2-arg `Quote.reify` call site and every consumer of nf/whnf OUTPUT that assumes the flat shape — including the kernel.ex:828-831 flat-spine comparison ("Quote.reify always…" comment) and `unify_indices`' term diet. For each: unaffected (values, not reified terms), reconciled by B1 itself, or REQUIRES a semantic change → STOP and report. B1 lands only after this table is written into the execution report.
3. **B3** — `lib/antigen/generators/equality.ex:80-83, :130-133`: the deliberately-flat claimed type shapes ("reify has no signature to split it") update to the split shape in the same commit as B1.
4. **B4 — antibodies** (new `test/antigen/nf_welltyped_antibody_test.exs`): (i) for an indexed-family term (the `Equivalent(Dec, Causal, Causal)` shape from the banked seeds), `check(nf(t), inferred_type)` succeeds — RED before B1 with `:arg_arity`; (ii) `nf(nf(t)) == nf(t)` on the same shapes (idempotence retained).
5. **B5** — do NOT run open-ended `mix antigen` campaigns as a gate (they append banked seeds to committed corpus files); the antibodies + existing suite are the gate. If a spot campaign is run for evidence, `git checkout -- test/antigen/*.sexp` afterward and say so.

## 3. Verification gates

1. Red→green evidence per antibody (A4.i, A4.ii, B4.i must each be demonstrated RED first).
2. Scoped: `mix test test/cure/core/ test/antigen/` green. Full suite ONCE: 0 failures, arithmetic = baseline + new antibody tests − ledgered flips (expected 0 deletions; flips don't change counts).
3. Oracle replay 65/65 inside the suite; ANY replay flip = STOP (readback must not change elaboration verdicts).
4. Diff-scope: `git diff` touches ONLY the §0 file list. `lib/cure/elab/` EMPTY, `lib/cure/compiler/` EMPTY.
5. **§3.4 permitted flip class:** a surviving test whose assertion pins the FLAT readback of an INDEXED family (params+indices merged in the params slot with `[]` indices) may be flipped to the split shape — that is the wrong convention being corrected. Each flip ledgered (file:line, old→new, why it pinned the collapse). A test pinning anything else = STOP. Expected flip surface: normalizer/quote/core tests asserting `{:data, _, _, []}` shapes for indexed families, if any exist (executor enumerates by grep before starting).

## 4. STOP conditions

A B2 consumer requiring flat readback that can't be reconciled without semantic change; any accept→reject behavior change out of A2 (it must only ADD acceptances); any oracle replay flip; any test edit outside §3.4; the A4.i red test NOT failing on baseline (would mean the K6 hazard is unreachable in a way that makes A1 untestable — report, don't fake the red).

## 5. Out of scope

Removing the K6 term form (stays, Lean-aligned inference rule); flat-vs-split at kernel.ex:828-831 index unification beyond what B2 proves necessary; any elaborator ctor-spelling change (already fields-only); #23 value-surface work.
