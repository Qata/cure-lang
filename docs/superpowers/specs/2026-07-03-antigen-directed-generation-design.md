# Antigen directed generation — design (Run A)

**Status:** approved (design gate — operator batch-approved A/B/C/D). Autopilot on `autopilot/antigen-tier-b`. Pure-Antigen: **no `Cure.Core.*` (TCB) edits.**

## 1. Motivation

A `--count 50000` explorer run found **0 infections** while banking a large seed set — evidence that undirected StreamData generation *plateaus*: dedup collapses to a coarse feature vector (`Coverage.key = {ctors, bucket(depth), flags, label}`), so past a few thousand rounds most draws re-cover buckets already seen. The fix is to make generation reach **deeper and more diverse** shapes without touching the kernel. Three independent, pure-Antigen levers:

1. **Coverage-vector enrichment** — the dedup/health key is too coarse; refine it so distinct-but-similar terms stop colliding and the health gate sees real diversity.
2. **Corpus-backed fillers (crossover)** — reuse real banked terms as well-typed fillers, reaching term shapes fresh random generation rarely hits.
3. **Health-adaptive biasing** — close the existing health loop so generation steers toward the weakest vertical instead of drawing uniformly.

## 2. Part 1 — Coverage-vector enrichment

`Coverage.key/1` currently returns `{ctors, bucket(depth), flags, label}` where `ctors` is the *set* of constructor names and `bucket(depth)` is a coarse depth band. Two distinct terms with the same constructor *set*, depth band, flags and label are treated as covered-equivalent — collapsing genuinely different structures.

**Change:** enrich the feature vector with two cheap, plateauing structural signals (both bounded, so the key space stays finite and dedup still converges):

- a **former histogram bucket** — for each Core former class present (`:lam`/`:pi`/`:app`/`:case`/`:ctor`/`:data`/`:eq`/`:rewrite`/`:prim`/leaf), a *presence* bit or small count bucket (0 / 1 / many), capturing *shape mix* not just constructor identity;
- a **binder-depth bucket** — max nesting depth of binders (`:lam`/`:pi`/`:sigma`/`:case`-branch), bucketed, distinct from the existing overall term-depth bucket.

The key stays a small tuple of bounded-cardinality features (spec §7.2's "plateauing feature vector" property is preserved — it must still saturate, not grow unboundedly). `key_string/1` extends to render the new fields. `Coverage.terms_of/1` is unchanged. **Backward-compat:** banked seed dedup keys are recomputed on read (they are not stored as `Coverage` keys — the corpus stores its own `key=` field), so enrichment does not invalidate committed corpora; verify no seed-replay test asserts an exact `Coverage.key_string` value (if one does, update it — the enrichment is the intended behavior change).

## 3. Part 2 — Corpus-backed fillers (type-safe crossover)

The mutation/typed-term generators build terms with **typed holes** filled by fresh `Term.gen_term(ctx, goal)` draws. Crossover reuses *real banked terms* as those fillers.

**Mechanism:** a new `Antigen.Generators.SeedPool` that, at generation time, loads a corpus file once (default `test/antigen/seeds.sexp`), extracts every **closed** (empty-context, de-Bruijn-closed) `typed_term` sub-corpus term indexed by its **recorded type** (the seed's `payload.type`), and exposes `pool_term(goal) :: Gen.t() | :none` returning one banked term whose type is syntactically equal to `goal` (or `:none` if the pool has none).

`Term.gen_term(ctx, goal)` (and/or the mutation fillers `gnat`/`gvec0`/`gvec_sz`) gain a **low-frequency** branch: with small weight, if `SeedPool.pool_term(goal)` is available, draw a banked closed term instead of generating fresh. Closedness guarantees the spliced term is valid in any context (no shift needed); type-equality guarantees well-typedness at the hole.

**Determinism/safety:**
- The pool is built from **closed** seeds only (drop any with a non-empty ctx or a free de-Bruijn index — reuse `Shrink.closed?`-style checking). This is what makes context-free splicing sound.
- Type match is **syntactic equality** of the goal type-term against the seed's stored `type` (no kernel call). Conservative but sound.
- If the pool file is absent/empty, the branch is inert (`:none`) — generation falls back to fresh, so the feature degrades gracefully and tests don't depend on a populated pool.
- **Quarantine:** `SeedPool` lives under `lib/antigen/generators/` and must contain **no** literal `StreamData` (grep-enforced by `architecture_test.exs`) — it uses `Antigen.Corpus` + the `Antigen.Gen` DSL only.

## 4. Part 3 — Health-adaptive biasing

`Runner.explore/1` today draws **all** `count` challenges up front (`draw(opts[:gen], count)`), then reduces and computes health post-hoc — so health can't feed back into generation.

**Change:** restructure `explore/1` to run in **rounds** (a fixed round size, e.g. 200 challenges), computing per-vertical health after each round and **re-weighting** the generator mix for the next round toward the vertical with the lowest health stamp (e.g. a vertical stamped `:vacuous` or with the lowest reduction_activity/diversity gets a higher draw weight). The mix is a weighting over the existing `default_gen` sub-generators; biasing only changes weights, never removes a vertical (every vertical keeps a floor weight so coverage never starves).

**Constraints:**
- **Behavior-preserving default:** with adaptivity disabled (a `bias: false` opt, default for the existing static tests) `explore/1` produces the *same* outcome as today (one batch, uniform mix). Adaptivity is opt-in via `bias: true` (the `mix antigen` CLI enables it).
- The round loop reuses the existing per-challenge reduce body (assay → bank/report) unchanged — only the *draw* is re-batched and re-weighted.
- Total challenge count and the final health/infection reporting are unchanged in shape.

## 5. Testing (TDD, per Stage 4)

1. **(Part 1)** `Coverage.key/1` distinguishes two terms that today collide — e.g. `λ.λ.x` vs `λ.(f x)` at equal depth/ctors/label produce **different** keys after enrichment (RED against current coarse key); the key remains bounded (a property test: N random terms yield ≤ K distinct keys for small K, proving it still plateaus). `key_string/1` round-trips the new fields.
2. **(Part 2)** `SeedPool.pool_term(goal)` returns a closed banked term of exactly `goal`'s type for a populated pool, `:none` for an absent/empty file; every returned term passes `Term.term?` and is closed. A generator test: with the seed pool wired, some fraction of drawn fillers are banked terms (reachability), and every produced challenge still satisfies its construction guarantee (mutants still infer-reject; typed_terms still infer-accept).
3. **(Part 2)** Quarantine: `architecture_test.exs` stays green (no `StreamData` literal in `SeedPool`).
4. **(Part 3)** `explore(bias: false)` (default) is outcome-identical to today on a fixed challenge set; `explore(bias: true)` runs the round loop, and a test shows the next round's weight vector shifts toward a vertical made artificially low-health (inject a stub gen whose vertical is vacuous, assert its weight rises). Floor weights hold (no vertical drops to 0).
5. **Full suite once** (Stage 5) + a sanity `mix antigen --count 800 --bias` to a tmp corpus: health lines should show **improved** diversity/reduction_activity vs the pre-change baseline (record both).

## 6. Files

- **Modify:** `lib/antigen/coverage.ex` (enriched key + `key_string`), `lib/antigen/runner.ex` (round loop + biasing, opt-gated), `lib/antigen/generators/term.ex` (+ mutation fillers) for the corpus-backed branch, `lib/mix/tasks/antigen.ex` (`--bias` flag).
- **Create:** `lib/antigen/generators/seed_pool.ex`, tests under `test/antigen/`.
- **Untouched:** `Cure.Core.*` (TCB), the corpus format/migration, `Challenge`.

## 7. Non-goals (YAGNI)

- **Grey-box kernel-branch instrumentation** — true execution-trace coverage requires editing `Cure.Core.*` (TCB, HARD-STOP-review); explicitly deferred as a separate operator-reviewed run.
- Cross-context splicing of open terms (only closed banked terms are pooled — sound without a shift/typing engine in the generator).
- Kernel-call-based type matching for the pool (syntactic equality only).
- Changing the corpus on-disk format or re-banking committed corpora.

## 8. Risks

- **Enriched key stops plateauing** (unbounded key space → dedup never converges, health gate breaks). Mitigation: every new feature is bucketed to a small fixed cardinality; §5 item 1's plateau property test guards it.
- **Adaptive loop changes existing test outcomes.** Mitigation: `bias: false` default is behavior-preserving; only `mix antigen`/opt-in paths use rounds.
- **Corpus-backed filler contaminates a mutant** (a banked term isn't actually the claimed type). Mitigation: syntactic type-equality + closed-only + the construction-guarantee assertions in §5 item 2 (mutants must still infer-reject); if a banked term ever breaks that, it's caught red.
