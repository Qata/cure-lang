# Autopilot completion report — Antigen rewrite/eq vertical (sub-project ③)

**Branch:** `autopilot/case-index-unification` (worktree; **not merged** — review + merge is yours)
**Result:** full suite **2165 passed, 0 failures** (baseline 2158 + 7 new tests).

## What shipped

A new **known-label soundness vertical** for Antigen, `rewrite/eq`, covering the
kernel's propositional-equality surface (`{:eq}` / `{:refl}` / `{:rewrite}`). It
is the regression **net** that must stay green while sub-project ② (the
case-refinement pattern-fragment unifier) is built — if the unifier ever
weakens the transport/`refl` conversion discipline, this battery goes red.

Mirrors the indexed-case vertical exactly: `Antigen.Generators.Rewrite`
hand-builds raw Core defs (Challenge kind `:rewrite_eq`, payload
`%{families, def_name, def_type, def_body}`) whose `:well_typed`/`:ill_typed`
label is correct **by construction**; `Antigen.Assays.Rewrite` runs each through
`Cure.Core.Kernel.check_def/2` and reports an infection iff acceptance ≠ label.
No term generator, no external oracle. **Zero TCB change** — no kernel edit was
needed (no soundness hole surfaced).

### The four obligations (12 variants)

| § | Builder | Variants | Probes |
|---|---------|----------|--------|
| 4.1 | `eq_formation/1` | well_typed, ill_typed | `infer({:eq,…})` endpoint typing (`MkFoo : Foo ≠ Dec` rejected) |
| 4.2 | `refl_typing/1` | base, redex, conjunct1_violation, conjunct2_violation | `check({:refl},{:veq,…})` two-conjunct guard: `conv(a,b)` **and** `conv(eval subj, a)`, up-to-normalization |
| 4.3 | `rewrite_premise/1` | well_typed, proof_not_eq, body_mismatch | `ensure_eq` on the proof; body checks at `M a`; mismatch → `:rewrite_premise` |
| 4.4 | `transport_type/1` | transport_correct, refl_coherence, left_at_source | result type is `M b` not `M a`; `left_at_source` (declared codomain left at the source type) is correctly **rejected** — the load-bearing soundness probe |

## Stage log

| Stage | Outcome |
|-------|---------|
| 0 Brainstorm | Design approved earlier; spec written + hardened (`24db3a1`, `adf9617`). |
| 1 Spec review | Sonnet recursive-skeptical-review → hardened spec committed. |
| 2 Plan | 5-task TDD plan (`d1fab89`). |
| 3 Plan review | Sonnet review (9 passes) → hardened plan (`0d6fa06`); fixed the T5 `Corpus.append_seeds`/`Runner.replay` API mismatches before execution. |
| 4 Execute (Opus, TDD) | 5 tasks, per-task red→green→commit (below). |
| 5 Verify | Full suite once: **2165 passed, 0 failures**. |

## Commits (Stage 4)

- `f1d67cf` scaffolding + wiring (`:rewrite_eq` kind, `@known_atoms`, `to_pieces`/`from_pieces`, Coverage, Runner, corpus-replay registry) + Eq-formation obligation
- `0aa81a2` refl-typing obligation (both conjuncts)
- `34db33f` premise-discipline obligation
- `42ea8ad` transport-result-type obligation
- `5ec51a4` bank + statically replay rewrite/eq seeds

## Notes for review

1. **No antibodies, seeds only.** Every one of the 12 variants is handled
   correctly by the kernel — the `:left_at_source` probe (the one that would
   expose a lost transport) is properly rejected. So the vertical banks
   known-good **seeds** into `test/antigen/seeds.sexp` (append-only) and adds
   **no** antibody to `corpus.sexp`. The seed test guarantees every banked
   record replays `:ok`.
2. **9 seeds from 12 variants — intended coverage collapse.** Seed
   `dedup_key` is the coverage abstraction `{ctors, depth-bucket, flags, label}`
   (identical to indexed/case). Variants equal under that metric collapse (e.g.
   `rewrite_premise(:well_typed)` and `transport_type(:transport_correct)` share
   a Core term). This is by design; coverage is non-empty and every seed
   replays `:ok`.
3. **No `gen/0`, not in `default_gen/0`.** Like `Generators.Indexed`, this is a
   fixed, exhaustively-enumerable battery banked via its own seed test, not a
   population wired into the `mix antigen` explorer sweep.

## Not done (intentionally deferred — next autopilot run)

- **Sub-project ② — case-refinement pattern-fragment unifier** (constructor
  injectivity + no-confusion + occurs-check), keeping `rewrite` as the
  propositional escape hatch (the locked Idris/Agda architecture). This
  vertical is the net that guards it. Own spec → Sonnet review → plan → Sonnet
  review → Opus TDD execute → verify.
