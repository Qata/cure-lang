# Gap-Design Gate — Core cleanup complete, awaiting operator sign-off

**Status (2026-07-08):** The dependent-kernel Core-cleanup grind has reached its
terminal state. The Core is clean to **Idris-2 parity minus linear types on the
soundness dimension** — see spec §J.1 and the audit FINAL-STATE banner. The
unattended cron's next phase is the deferred feature **gaps**, and per its own
instruction those require **operator design sign-off** before any implementation.
This file is the durable hand-off: it frames the gaps so a brainstorming session can
start the moment the operator returns. **No gap work has been started.**

## Why we paused here

The cron authorized unattended *Core cleanup* (soundness/boundary tightening) but
explicitly gated *features* behind design approval. Everything remaining is a
feature or a faithfulness-only representation change — none is an open soundness
hole — so the autonomous mandate is exhausted. Brainstorming is interactive (it asks
one question at a time and needs your answers), so it cannot run unattended.

## What's done (so you can trust the "Core clean" claim)

- **All K1–K14 resolved.** Soundness LANDED or kernel-enforced (K1a, K2 §G.1, K3,
  K4, K5a, K6 545/599, K11a, K12 slices 1–2, K13, K14). Faithfulness-only items
  declined-with-recorded-proof (K1b `{:rewrite}` Phase B, K2 `{:prim}` migration).
- **Eight E-layer hygiene holes closed** beyond the audit (duplicate def/type/ctor
  per module, param, field, family index, GADT-ctor named domain, non-linear
  pattern) + a self-audit fix scoping those checks per module.
- **Six dependent-soundness axes probed sound:** telescope linearity, strict
  positivity, match coverage, termination (partial-by-default; δ never unfolds a
  non-terminating global), erasure relevance, universe consistency (predicative,
  `Type₀ : Type₁`, no `Type:Type`).
- Suite green at **3107** (HEAD `238b90f`).

## The deferred gaps — pick one to design first

### Group A — the cron's named feature gaps
1. **Unsafe-hole taxonomy** *(grade-wave-coupled — NOT the quick win it first looks)*.
   The 3 position-kinds (type / proof / body) + an `unsafe` keyword, with a per-hole
   safety flag `{:hole, name, safety}`. The DECISION is locked (memory
   `holes-unsafe-taxonomy-decision`) and Wave-1 K3 shipped the firewall
   (`no_hole: :reject` at release, commits f7cfa6e→a2409a8). BUT the full taxonomy's
   proof-vs-body split *is* erased-vs-relevant, so the locked note explicitly
   sequences it **with the grade wave** and calls it "its OWN brainstorm/spec". So
   this gap first needs a decision on grade-wave sequencing — a real design
   conversation, not a rubber-stamp. (Note: the `{0,ω}` erasure *soundness* is
   already enforced via the relevance check; what the grade wave adds is the
   per-binder grade *field* — a representation/faithfulness change, so this gap is a
   feature, not a soundness fix.)
2. **Bucket B / C stdlib-dependent extensions** *(lowest-risk standalone start —
   recommended first)*. `Bounded` (native-int `Fin`), flesh out `Vector`
   (lookup/head/map/…), `Ordering`-as-inductive (memory `stdlib-dependent-expansion`).
   Concrete, incremental, no kernel/grade-wave coupling — the cleanest way to
   re-establish the design→plan→implement rhythm.
3. **Safe FRP Types (ICFP'09).** Derive the Dec/Init index algebra + `switch` from
   the paper PDF (Agda source is gone — memory `frp-source-unavailable-derive-from-paper`,
   `reactive-runtime-design-bible`). Largest / most research-y; the Lean-shape
   pattern-matching work was building toward enabling it.

### Group B — declined/deferred K-features (optional, faithfulness/parity)
4. **Canonical `Eq` transport (K1b / K5b).** Retire the `{:rewrite}` node → genuine
   J-eliminator / `Eq.rec`. Declined twice as Phase B (empirical parity regressions);
   would need a kernel-conversion improvement that removes the `bridge_step`
   workaround first. No soundness gain — pure faithfulness.
5. **Universe-level polymorphism (K7).** Level variables, `Type ℓ`, globals carrying
   level args. Soundness already met (predicative); this is ergonomics/parity.
6. **Qualified `Sym` (K12).** Module-path-qualified globals/ctors replacing bare
   atoms; enables principled cross-module disambiguation (subsumes the fn-vs-ctor
   name-collision decline) and robust serialization. Large representation change.

## Recommended next step

Start a `superpowers:brainstorming` session on **gap #2 (Bucket B/C stdlib
extensions)** — it has no kernel or grade-wave coupling, so it converges fast and
re-establishes the design→plan→implement rhythm on the lowest risk. Gap #1
(unsafe-hole taxonomy) is better done once its grade-wave sequencing is decided; gap
#3 (FRP) is the largest. Group B items are opt-in parity work with no soundness
urgency.

**To proceed:** reply with which gap to design first (default #2), and I'll run
brainstorming to a design you approve before any code is written.
