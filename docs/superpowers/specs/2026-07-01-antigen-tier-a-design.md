# Antigen Tier A — harness + schema-directed assays (design)

**Status:** Draft (ready for review)
**Date:** 2026-07-01
**Author:** brainstormed with the operator.
**Umbrella:** `docs/superpowers/specs/2026-07-01-antigen-design.md` (vocabulary,
architecture, the totality vertical). **Research basis:**
`docs/research/pbt-dependent-types/synthesis.md` (11-paper synthesis).

This spec is the **first buildable slice** of Antigen. It inherits the umbrella's
vocabulary (antigen / assay / antibody / infection) and its swappable-backend
architecture, and pins down exactly what we build first and how.

---

## 1. Scope — what Tier A is and is not

The 11-paper research synthesis surfaced a hard fault line in Antigen. It has:

- a **schema-directed half** that rests on solid, published ground — the pipeline
  plus generators whose objects are built *by construction* with a known
  ground-truth label (totality/positivity), which is the "proven-good class" of
  the QuickChick derivation literature; and
- a **frontier half** — a general well-typed *dependent* term generator, which is
  genuinely open research (no turnkey solution exists in the corpus).

**Tier A builds the schema-directed half in full.** It delivers a working,
end-to-end engine that catches the *confirmed* mutual-recursion hole two
independent ways, with **zero dependence on the frontier generator**.

**In scope (Tier A):**
- The corpus subsystem — two committed, never-pruned, C2-serialized,
  generator-independent stores (antibodies + valid/seed bank).
- The `Antigen.Gen` DSL (reified, inspectable) + the StreamData backend.
- Known-label generators built directly as `Core`+`Env` (bypassing the elaborator).
- Four assays: `totality/terminating`, `totality/diverging`, `positivity`,
  `reflexivity-as-normalization`.
- Three run modes — explorer, generate, replayer — with the budget model of §8.
- Health-gate plumbing (discard-rate + coverage tracking).
- Reporting (`tmp/antigen/` + stdout breadcrumb).

**Deferred to Tier B (its own spec):** the hybrid bidirectional-inversion
dependent term generator and the differential assays it unlocks
(`subject_reduction`, `infer_check_agreement`, `normalization_stability`,
`conversion_termination`, `erasure_preservation`). Tier B's expensive-to-generate
terms will accrue into the *same* committed seed bank Tier A builds.

**Not in scope at all (separate specs):** *fixing* anything. Antigen **detects**.
The mutual-recursion checker fix, the `Vector`→`Std.Array` rename, and the emit
unused-var cleanup are their own specs that consume Antigen's findings.

## 2. Success criteria

Tier A is done when:

1. `mix antigen` (explorer) generates mutual-recursion definition groups, the
   kernel certifier wrongly certifies them (`totality/diverging` infection), the
   result is shrunk to a minimal cycle, written to `tmp/antigen/`, and appended
   to the antibody corpus — all in one self-terminating run.
2. `reflexivity-as-normalization` independently flags the *downstream* consequence
   of the same hole: a wrongly-certified diverging global, forced inside a term,
   makes `conv(t,t)` exceed its fuel budget.
3. `totality/terminating` and `positivity` pass on known-good inputs and would
   fail on injected known-bad ones (both directions exercised).
4. `mix test` statically replays both corpora, reports **every** failing entry,
   and never mutates the corpus (git-clean for CI).
5. `mix antigen generate` harvests valid terms into the seed bank until killed,
   losing nothing on SIGINT.
6. The architecture test passes: nothing under `Antigen.Generators.*` /
   `Antigen.Assays.*` references `StreamData`.

## 3. Component architecture

Modules, and which plan-phase builds them. (The spec is one document; the
*implementation plan* runs in two phases — see §11.)

```
Phase 1 — harness skeleton
  Antigen.Gen              # reified, inspectable generator AST (§6)
  Antigen.Backend          # behaviour: explore / replay
    └─ Backend.StreamData     # interprets Gen → StreamData; integrated shrinking
  Antigen.Corpus           # two stores: antibodies + seeds; decode/dedup/replay (§7)
  Antigen.Coverage         # the coverage key: dedup + health signal (§7.2, §9)
  Antigen.Report           # tmp/antigen/ + stdout breadcrumb (§10)
  Antigen.Runner           # explore / generate / replay orchestration (§8)
  Mix.Tasks.Antigen        # `mix antigen [generate]`

Phase 2 — schema-directed assays + generators
  Antigen.Generators.Totality   # known-label terminating/diverging defs (§5.1)
  Antigen.Generators.Positivity # ±strictly-positive families (§5.2)
  Antigen.Generators.Forcing    # schematic terms that force a global (§5.3)
  Antigen.Assays.Totality       # totality/{terminating,diverging} (§4.1)
  Antigen.Assays.Positivity     # positivity (§4.2)
  Antigen.Assays.Reflexivity    # reflexivity-as-normalization (§4.3)
```

Phase 1 is a runnable engine with a trivial stub assay; Phase 2 replaces the stub
with the real four and their generators. The harness is untestable without at
least one real assay, which is why they share a spec.

## 4. The four assays

Every assay is a pure function `antigen -> :ok | {:violation, detail}` (umbrella
§7). Tier A's four, in full:

### 4.1 `totality/terminating` and `totality/diverging`

The umbrella §6 details the totality vertical; this is its Tier-A realization.

- **Generator:** §5.1 (known-label defs built directly into `Core`+`Env`).
- **Oracle:** the **known label**. No fuel, no timeout — the certifier
  (`Kernel.validate_certificate` / `Certificate.terminating?`) is a *static
  structural analysis* that terminates on its own.
- **`totality/diverging` asserts:** the certifier **must NOT certify** a
  by-construction non-terminating def. Violation = a soundness infection. **This
  is the direct, cheap detector of the confirmed hole** — a mutual group
  `f→g→f` that the certifier wrongly accepts.
- **`totality/terminating` asserts:** the certifier **must certify** a
  by-construction total def (including well-founded mutual groups). Violation =
  an incompleteness bug (rejecting a genuinely-total function), and guards the
  eventual fix against over-correction.

### 4.2 `positivity`

- **Generator:** §5.2 (inductive families, labeled ±strictly-positive).
- **Oracle:** the **known label**. Static — run the positivity checker, compare.
- **Asserts:** the kernel accepts a family **iff** it is strictly positive. A
  labeled-negative family that is accepted, or a labeled-positive family that is
  rejected, is an infection. Guards the second classic unsoundness route (a
  negative occurrence lets you build a non-terminating loop and inhabit ⊥).

### 4.3 `reflexivity-as-normalization`

The independent, downstream probe for the hole. From *Certify a Conversion
Checker* (FSCD'25): **reflexivity of conversion is equivalent to deep
normalization** — `conv(t,t)` terminates iff `t` deeply normalizes. So a
budget-bounded `conv(t,t)` is a non-normalization detector that does **not** rely
on trusting the checker's verdict (it relies only on whether it *halts*).

- **Generator:** §5.3 — a known-label **diverging** def registered in `Env`, plus
  a small **schematic term** `t` that forces the global (built directly in `Core`,
  not the general term generator).
- **Oracle:** **fuel** (§8). Assert `conv(t,t)` halts within the fixed fuel
  budget. Fuel exhaustion = a (suspected non-termination) infection.
- **Why it complements §4.1:** δ-reduction only unfolds *certified-total*
  globals. So `conv(t,t)` can only loop here *because* the certifier already
  wrongly certified the diverging def (§4.1's hole). `totality/diverging` catches
  the hole at the certifier; `reflexivity-as-normalization` catches its
  conversion-level consequence — and remains a general non-normalization probe for
  any future source, not just this hole.

## 5. Known-label generators

All three build `Core` terms and the `Env` **directly**, bypassing the
elaborator. This is essential and load-bearing: the surface elaborator cannot even
express mutual recursion (the forward-reference gap that *masks* the hole), so
Antigen constructs the mutually-recursive `Env` itself and calls the certifier —
the exact move that confirmed the hole, now fuzzed. **These generators ARE the
oracle**, so their correctness is the depth of the vertical (umbrella §6).

### 5.1 Totality generator (`Antigen.Generators.Totality`)

Emits `(def_group, label)` where `label ∈ {:terminating, :diverging}` is
ground-truth by construction:

- **`:terminating`** — non-recursive defs; single defs where every self-call is on
  a strict structural subterm (guarded by destructors); **and well-founded mutual
  groups** (even/odd style, where the group's calls structurally decrease).
- **`:diverging`** — genuine non-termination: direct self-loops with
  non-decreasing arguments; **mutual groups `f→g→f` that are not structurally
  decreasing** (the confirmed hole); and non-structural / deep recursion.

Generation parameters (fed by `Antigen.Gen`): arity, number of mutual
participants, recursion-argument shape (decreasing vs. constant vs. increasing),
guard pattern. Shrinking respects the label — a `:diverging` counterexample cannot
shrink away its back-edge (umbrella §6).

### 5.2 Positivity generator (`Antigen.Generators.Positivity`)

Emits `(family, label)` where `label ∈ {:positive, :negative}`:

- **`:positive`** — every recursive occurrence in every constructor argument is
  strictly positive by construction.
- **`:negative`** — one injected negative occurrence (a recursive occurrence to
  the left of an arrow in a constructor argument type).

### 5.3 Forcing generator (`Antigen.Generators.Forcing`)

For `reflexivity-as-normalization`: takes a `:diverging` def group from §5.1,
registers it in `Env`, and builds a minimal schematic `Core` term `t` that applies
/ forces the diverging global so that (once wrongly certified) its δ-unfolding
drives conversion. This is a fixed schematic construction, **not** the general
term generator — it stays schema-directed and Tier-A.

## 6. `Antigen.Gen` DSL + backend

Refines the umbrella §4.1. Two decisions from the research (synthesis §3.4, from
*Foundational PBT* ITP'15):

**Reified, inspectable AST — not opaque closures.** `Antigen.Gen` values are data
(`{:return, x}`, `{:one_of, gs}`, `{:frequency, weighted}`, `{:bind, g, f}`,
`{:member_of, list}`, `{:sized, f}`, `{:resize, n, g}`), so a static pass can
compute/over-approximate a generator's **support set** by structural recursion
(`support(bind g f) = ⋃_{a∈support g} support(f a)`) — which is what makes "what
can this assay generator actually produce?" answerable rather than assumed.
(`bind`'s continuation is a function, so its support is only *over-approximable* —
an accepted limit.)

**Size-hygiene tags.** Each generator is tagged `:unsized` (size-independent
support) or `:size_monotonic` (bigger size ⇒ superset). These license the clean
compositional support reasoning and prevent false-completeness claims across
sizes (ITP'15 §3.5: `bind` threads one size to both sides).

**No `filter` as a first-class primitive** — the generate-then-filter
anti-pattern every paper warns against. Available only as a marked escape hatch.

**Backend.** `Backend.StreamData` interprets one clause per primitive; because
`bind → bind`, integrated (Hedgehog-style) shrinking is inherited and stays valid.
Architecture rule (umbrella §4, enforced by test §11 there): only
`Backend.StreamData` may reference `StreamData`.

## 7. Corpus subsystem

Two committed stores, both **C2-serialized** (`Cure.Core.Serialize`),
**never-pruned**, and **generator-independent** — replay decodes a stored object
and runs the assay *through the kernel*; the generator is never on the read path.
This is why a full generator rewrite cannot cost us the accumulated library.

### 7.1 The two stores

- **`test/antigen/corpus.sexp` — antibodies** (counterexamples). Admission rule:
  **admit any** infection. One C2 record per line (umbrella §8.2 grammar). Static
  replay asserts each still violates → a live infection turns `mix test` **red**
  and stays red until fixed. Pure verdicts, no `open`/xfail.
- **`test/antigen/seeds.sexp` — the valid/seed bank.** Admission rule: **admit iff
  coverage-novel** (§7.2). Holds well-typed / well-formed generated antigens
  regardless of assay outcome. Serves three jobs at once: static regression
  replay, the coverage record, and (Tier B) generation seeding. An
  infection-triggering antigen is a *valid object that also violates an assay* — it
  is banked in **both** stores (valid here, counterexample in the antibody store);
  no contradiction.

Record grammar is shared; a `kind` distinguishes them where a reader needs it.
Dedup on append is idempotent, keyed on the canonical C2 serialization of the
`(assay, term)` for antibodies and on the **coverage key** for seeds.

### 7.2 The coverage key

A **feature vector**, not a full-shape hash (a full hash makes every distinct term
"novel" and defeats the plateau — the store would grow without bound). The key:

```
{ set of Core constructors used
· depth bucket ∈ {0–2, 3–5, 6–9, 10+}
· binder-shape flags: has_shadowing, has_mutual_group, per-eliminator-kind present
· label kind (:terminating | :diverging | :positive | :negative | :none) }
```

**Admit a seed iff its key is new.** So "keep all valid terms" means "keep all
*coverage-novel* terms" — which plateaus (the feature-vector space is finite once
common shapes are covered) and stays committable and diff-friendly. Changing the
key later only affects whether *new* terms are judged novel; it never evicts an
already-committed term (never-pruned). The same key drives the health gate (§9).

## 8. Run modes and the budget model

Three modes on the runner. The budget model separates a **deterministic verdict**
from **wall-clock safety**, so the committed corpus replays identically everywhere.

- **Per-conversion fuel — the verdict, FIXED and committed.** The fuel bounding
  `reflexivity-as-normalization`'s `conv(t,t)` is a **fixed constant baked into the
  assay**, a count of reduction/normalization steps. It must not vary by run mode
  or machine: otherwise the same term could read diverging on one box and
  terminating on another, and a committed antibody could flip green↔red. Fuel
  exhaustion is the deterministic, replayable verdict.
- **Per-conversion killswitch — safety, a fixed decent constant.** A wall-clock
  cap on a single conversion so one pathological term can't wedge the runner.
  Reported as a distinct "killswitch tripped" event, **never** an assay verdict.
  Not configurable (a fixed sensible value).
- **Explorer — `mix antigen`** (generate + assay + bank). **Self-terminating** on
  a default number of generation rounds; optional `--count N` / `--budget Nm`
  override. **No** named fast/regular/thorough tiers. On each infection: shrink,
  write the tmp report, append to the antibody store (dedup), and **keep going**
  (harvests many infections per run). Every generated valid antigen is offered to
  the seed store (coverage-dedup). Owns corpus mutation; the operator commits the
  diff.
- **Generate — `mix antigen generate`** (harvest-only). Produces well-typed /
  well-formed antigens, coverage-dedups, appends to the seed store, and **skips
  the assays entirely** (no verdicts, no infection-hunting). **Runs until killed**
  (SIGINT), flushing to the store periodically so a kill loses nothing. This is
  the "leave it running for hours to stack up expensive terms" tool; those terms
  are assayed later by the replayer. (High-value mainly for Tier B's expensive
  terms; the machinery is built here so Tier B inherits it.)
- **Replayer — in `mix test`** (read-only, static). Decodes both stores and runs
  the assays over them, reporting **every** failing entry (non-fail-fast). Never
  generates, never mutates — `mix test` stays git-clean for CI. Bounded by corpus
  size, so no run budget.

## 9. Health gate

Coverage bounded by the generator is the field's dominant false-confidence trap
(synthesis §3.2, §3.4): a green assay from a generator that can't reach the
interesting shape is vacuous. Tier A builds the plumbing:

- **Discard rate** — fraction of generation attempts that fail to produce a
  bankable object. For known-label generators this should be ≈0; a rising rate is
  a red flag.
- **Coverage** — which coverage-key buckets (§7.2) the run hit. Reported per run;
  a batch that never hits `has_mutual_group`, for instance, cannot have tested the
  hole.

Tier A **reports** these (per-run summary + into `tmp/antigen/`); it does not hard-
fail on them. Term-specific health metrics (binder-usage rate, reduction activity)
are added in Tier B, where terms with binders exist — the `Antigen.Coverage`
module is structured to receive them without rework.

## 10. Reporting

Per umbrella §8.1, unchanged: on **every** infection or unexpected error, a full
report is written to `tmp/antigen/failure-<seed>-<assay>-<n>.txt` and flushed
**before** anything reaches stdout (a killed process or a `grep`-filtered pipe
cannot lose it), plus a stable `tmp/antigen/latest.txt`. One grep-surviving stdout
breadcrumb per infection. Reports also carry the run's health-gate summary (§9).

## 11. Plan phasing

One spec, two plan-phases (each an independently testable deliverable):

- **Phase 1 — harness skeleton.** `Antigen.Gen` + `Backend.StreamData`,
  `Antigen.Corpus` (both stores, decode/dedup/replay), `Antigen.Coverage`,
  `Antigen.Report`, `Antigen.Runner` (all three modes), `Mix.Tasks.Antigen`.
  Driven by a **trivial stub assay + stub generator** so the whole
  explore/generate/replay/report/corpus data flow is exercised end-to-end before
  any real assay exists.
- **Phase 2 — schema-directed assays + generators.** The three generators (§5)
  and the four assays (§4). Replaces the stub. Phase 2's completion is
  success-criterion #1–#3 (§2): the engine catches the confirmed hole two ways.

## 12. Testing Antigen itself

Per umbrella §11, plus Tier-A specifics:

- **Architecture test** — no `Antigen.Generators.*` / `Antigen.Assays.*` module
  references `StreamData`.
- **Generator self-tests** — the totality generator's `:terminating` / `:diverging`
  outputs are validated against a fixed known-good/known-bad set, *including* the
  confirmed mutual cycle Antigen must flag; the positivity generator likewise.
- **Support-set characterization** — for each generator, a runnable soundness
  meta-test (`check all x <- gen: assert well_formed?(x)`) and a documented note on
  what its support set can/can't produce (synthesis §3.4). Soundness is tested;
  completeness is the coverage/corpus argument, not a proof.
- **Corpus round-trip** — every record encodes → decodes → re-checks identically
  (C2 stability), for both stores.
- **Replay determinism** — replaying any stored term yields the same verdict every
  run (this is what the fixed fuel of §8 guarantees).
- **Fuel determinism** — `reflexivity-as-normalization` returns the same verdict
  regardless of machine speed (fuel, not wall-clock, decides).

## 13. Deferred to Tier B (for continuity, not built here)

The hybrid dependent term generator: bidirectional-rule inversion + INDIR
(head-first saturated elimination) + a retained plain-elimination rule (so redexes
remain reachable) + interleaved generation-and-checking + direct normal-form
generation + deliberate shadowing contexts; conversion and index constraints
discharged via the kernel conv-checker under the same fuel budget. It unlocks the
differential assays and feeds the seed bank built here. Its yield and coverage are
engineering unknowns to be *measured against this harness* — which is the reason
Tier A is built first.
