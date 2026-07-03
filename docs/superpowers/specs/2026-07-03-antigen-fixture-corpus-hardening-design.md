# Antigen fixture & corpus robustness hardening — design

**Status:** approved (design gate). Autopilot run on `autopilot/antigen-tier-b` (stays on this worktree per operator preference). Written after merging `autopilot/lean-shape-matching` (112 commits) into `antigen-tier-b`.

## 1. Motivation

Three robustness gaps, bundled because they all harden the Antigen generator/corpus fixtures against non-determinism and latent decode failure:

1. **A flaky mutation-generator test** (`test/antigen/generators/mutation_test.exs`) that fails only intermittently in the full suite. Investigation (below) shows the *described* mechanism does not match the code, so the fix is **defensive**: make every generator invariant hold **by construction** and rewrite the probabilistic / kernel-sampling assertions to be **draw-independent**, killing any latent seed-flake in the file regardless of which assertion it was.
2. **`@known_atoms` is incomplete** (`lib/antigen/challenge.ex`) — a latent decode-safety gap surfaced while making the corpus human-readable. Missing at least `:boom`, `:reify_distinct`, `:stuck_elim_delta`. Masked in the full suite (generator modules intern their literal atoms at load), but a bare-process decode of a record whose Base64 `scaffold` (`binary_to_term/2` with `[:safe]`) references an un-interned atom **raises**.
3. **Two corpus-format coverage facts** the readable-corpus work surfaced — the fault value-grammar is wider than flat atoms (`scope` int-pair; `:universe` term-valued heads), and there are three committed corpora — both worth **locking with regression guards** so a future change can't silently regress them.

### 1.1 Investigation findings (grounding — not hypothetical)

- The handoff points at `mutation_test.exs:36` (the `:index` arm asserting `f.expected_head != f.injected_head`). That reads a **static** fault-map constant — `index_mismatch` is hard-coded `expected_head: :Z, injected_head: :S` (`mutation.ex:58`); `:Z != :S` is always true and that test **never samples StreamData**, so it cannot seed-flake.
- Every `build/2` operator uses a **fixed structural mismatch**, not a drawn constructor. A 600-draw-per-operator probe found **0 kernel-accepted (no-op) terms**. A 15-seed sweep of `mutation_test.exs` in isolation is **all green**. The banked corpus is clean (all fault heads distinct; 13/13 distinct mutant terms).
- The one genuinely draw-and-kernel-dependent assertion is the **uncontaminated-control** test (`mutation_test.exs:82-85`): it samples 15 random wrapper stacks around a well-typed `Nat` inner and asserts the kernel **accepts** each. Contamination can only arise if a wrapper's **filler** (`gnat(ctx) = Term.gen_term(ctx, Nat)`) is ever *not* a well-typed `Nat` — which would make the stack ill-typed independent of the inner, failing the assertion. This is the plausible flake surface **and** a latent generator-soundness defect (a "rejected" mutant rejected for the wrong reason).

## 2. Part 1 — Mutation generator: construction guarantees + deterministic tests

### 2.1 Construction guarantees (generator side)

- **Rejection is filler-independent.** For every operator in `Mutation.operators()`, the mutant `infer`-rejects *regardless* of any drawn well-typed filler — the wrongness lives in the fixed structural mismatch, never in a draw. Audit `build/2`; today this holds (fixed heads). Document it as an invariant; if any operator is found where a draw could make the term well-typed, restructure it (fix the mismatch site, or reject-sample) so rejection is guaranteed.
- **Wrappers are non-contaminating.** For every wrapper in `Mutation.wrappers()`, a **well-typed `Nat` inner** yields a **well-typed** stack. Each wrapper is Nat→Nat with a `Nat` filler, so this reduces to: **`gnat(ctx)` / `Term.gen_term(ctx, Nat)` must only ever produce well-typed `Nat` terms.** Verify this is a construction guarantee of the lazy `Term` generator. If it can produce an ill-typed / stuck filler (the flake root), fix it — either constrain the filler to a provably-well-typed subset, or reject-sample fillers that fail a cheap well-typedness check — so contamination is impossible by construction.

### 2.2 Deterministic tests (test side)

Rewrite the flaky / probabilistic assertions in `mutation_test.exs` to be **draw-independent**:

- **Uncontaminated control** (`:82-85`): replace 15 random `deepen` samples with **deterministic per-wrapper enumeration** — for each wrapper kind, build the stack once with `inner = {:ctor,:Z,[]}` (well-typed `Nat`) and a **fixed** filler, assert the kernel **accepts**. A companion deterministic check: each wrapper around an intrinsically-ill-typed inner (`{:fst,{:ctor,:Z,[]}}`) **rejects**. No sampling, no kernel-on-random-draw.
- **Every operator rejects** (`:9-21`): keep the kernel-rejection check but make it deterministic — one representative construction-guaranteed draw per operator (a fixed filler / pinned generator), not 20 random samples whose acceptance the kernel decides.
- **Diversity asserts** (`≥5 fault kinds`, `≥4 wrapper kinds`): replace "sample N and hope the count is high enough" with **deterministic reachability** — assert each operator/wrapper is *individually* reachable (enumerate `operators()`/`wrappers()` and show each is produced), rather than a probabilistic count over a random sample.

> The witness-invariant test (`:23-46`) is already deterministic (reads static fault fields); keep it, and it doubles as the check that §2.1's fixed-mismatch invariant holds.

**Where sampling is inherent** (e.g. a test that genuinely must exercise the random generator), pin a fixed seed and document why, rather than relying on the ambient suite seed.

## 3. Part 2 — `@known_atoms` completeness + bare-process decode guard

### 3.1 Audit + add

Audit **every** module under `lib/antigen/generators/` and `lib/antigen/assays/` for atom literals reachable inside a banked record — i.e. in a Term **piece** (`{:global, n}` / `{:ctor, n, …}` / `{:data, n, …}` / `{:prim, op, …}`), in the Base64 **scaffold** (def-names, family/ctor names, quantities), or in a mutant **fault** (kinds, witnesses, heads, `wrap_path`, `carrier`, …). Add every missing name to `Challenge.@known_atoms`. Known-missing today: `:boom` (`Generators.Stub`), `:reify_distinct` and `:stuck_elim_delta` (lean-match's reify/stuck-elim verticals). The audit must be exhaustive, not just these three.

### 3.2 Bare-process decode regression test

Add a test that, in a context where **only** `Challenge.__known_atoms__()` is forced (generator/assay modules **not** relied on to intern their literals), decodes **every** record of **every** committed corpus (`seeds.sexp`, `corpus.sexp`, `reach.sexp`) and asserts all succeed (no `decode_error`, no raised `ArgumentError` from `[:safe]`). This permanently catches the missing-atom class.

> Implementation note: the test cannot truly unload already-loaded modules within one BEAM, but it **can** assert the decode contract holds after forcing only `__known_atoms__()`, and — more strongly — assert that every atom name appearing in each committed record's scaffold/fault/pieces is a member of `@known_atoms` (a static membership check over the corpus), which is what actually guarantees bare-process safety. The plan picks the concrete assertion; the membership check is preferred as it is deterministic and independent of load order.

## 4. Part 3 — fault-schema + corpora consistency guards

- **(a) Fault value-grammar lock.** Strengthen the fault-codec coverage: assert `decode_fault(encode_fault(f)) == f` for a fault of **every value shape the generators actually emit** — enumerated by calling `Mutation.build/2` for each operator (+ a deep `deepen` fault with `depth`/`wrap_path`, + a `Conversion.conv_reject` carrier fault), not hand-written maps. Locks the atom / int / `nil` / int-pair / list / Core-term grammar the readable-corpus work introduced.
- **(c) Corpora-readable guard.** A test asserting every committed corpus (`seeds.sexp`, `corpus.sexp`, `reach.sexp`) is fully in the readable format — every piece body starts with `(` (no Base64 pieces), and every record decodes — so a future un-migrated record fails CI instead of silently regressing readability.

## 5. Testing (TDD, per Stage 4)

Each item below is a red test first.

1. **(Part 1)** Deterministic uncontaminated test — every wrapper accepts a well-typed inner with a fixed filler; every wrapper rejects an intrinsic-fault inner. Draw-independent.
2. **(Part 1)** Deterministic per-operator rejection + per-operator/per-wrapper reachability (replacing the probabilistic diversity asserts).
3. **(Part 1)** If §2.1 finds `gnat`/`gen_term(Nat)` can produce a non-well-typed filler: a red test exhibiting a contaminated stack, green after the generator fix.
4. **(Part 2)** Static membership: every atom name in every committed corpus record ∈ `@known_atoms` — RED for `:boom`/`:reify_distinct`/`:stuck_elim_delta`, green after §3.1.
5. **(Part 3a)** Fault codec round-trips every generator-emitted fault shape.
6. **(Part 3c)** All three corpora are readable + decode.
7. **Full suite once** (Stage 5) — all green; run `mutation_test.exs` across several seeds to confirm determinism.

## 6. Files

- **Modify:** `lib/antigen/challenge.ex` (`@known_atoms` additions only — no other change), `test/antigen/generators/mutation_test.exs` (deterministic rewrites), possibly `lib/antigen/generators/mutation.ex` and/or the `Term` generator (only if §2.1 finds a real contamination/soundness bug — otherwise generator code is unchanged and the hardening is test-side + `@known_atoms`).
- **Create:** a test for the corpus atom-membership + corpora-readable guards (may live in `test/antigen/corpus_test.exs` or a new `test/antigen/corpus_atoms_test.exs` — plan decides).
- **Untouched:** `lib/antigen/corpus.ex` (readable-corpus work already shipped), the migration task, all `.sexp` corpora (already migrated).

## 7. Non-goals (YAGNI)

- Changing the corpus on-disk format further (done).
- A `to_existing_atom` corpus decoder (separate, deferred item).
- Reproducing the exact original flake (falsified against the code; the fix is construction-by-design, which subsumes it).
- Broad generator redesign — only the minimal change needed to make the audited invariants hold by construction.
- Re-banking / regenerating corpora (the guards validate the existing migrated files).

## 8. Risks

- **§2.1 finds nothing to fix** (the generator is already sound): then Part 1 is purely a test-determinism rewrite — still valuable (kills the seed-flake), and the risk is only that the "flake" recurs from a source outside this file. Mitigation: the deterministic rewrites remove *this file* as a flake source; if it recurs elsewhere the failure will point there.
- **Atom audit misses one**: mitigated by the static membership test (§3.2) which scans the actual committed records, so any name a real record carries is checked — the test fails if the audit was incomplete.
- **Determinism rewrite weakens coverage**: enumerate-each-reachable is *stronger* than probabilistic-count (it proves each case, not just the aggregate), so coverage is preserved or improved.
