# Antigen deep cut: indexed-family `case` soundness — design spec

**Status:** approved design, spec drafted for self-review.
**Branch:** `autopilot/cure-dependent-types-frp` (worktree `.claude/worktrees/cure-dependent-types-frp`).
**Depends on:** [[antigen-metatheory-engine]] Tier A (totality + positivity + reflexivity), already implemented and merged into this branch. Reuses its harness wholesale.
**Vertical name:** `indexed`. Assay key: `indexed/case`.

## 1. Why

Antigen's Tier A went deep on **totality** (the confirmed mutual-recursion hole, now fixed) and touched **positivity**. A manual read of `Cure.Core.Kernel`'s dependent-`case` typing (`infer/2` on `{:case,...}`, `check_coverage/3`, `check_case_branches/5`, `branch_index_subst/4`, `specialize_branch_context/2`, `check_motive_wf/3`) surfaced three concrete target hypotheses where a soundness hole could live — the same "found one hole by hand, build an engine to find more" motivation that started Antigen:

1. **Branch-family discipline.** `check_coverage/3` only checks `declared ⊆ covered` (`MapSet.subset?`). It never checks the reverse: a branch naming a constructor of an *unrelated* family is not rejected at that point. It flows into `check_case_branches/5`, which looks the constructor up in the *global* constructor namespace (not scoped to the scrutinee's family) and checks its body against the motive at that foreign constructor's own computed indices. Possible category-confusion route into the type checker.
2. **Coverage exactness.** Untested in the other direction: an omitted required branch must produce `{:error, :coverage}`.
3. **Index-refinement soundness — the crown jewels.**
   - *Compound-index refinement gap:* `branch_index_subst/4` only records a substitution when a constructor's declared result index is a bare `{:var, i}` (line ~548); the `{_other, _}` clause silently **drops** any compound result index (e.g. `S k`, `and(d1, d2)`). Refinement is incomplete for computed-index families — the open question is whether a dropped equation ever lets a branch body typecheck under an assumption that doesn't actually hold at that branch.
   - *Impossible-branch inhabitation:* coverage requires a branch for every declared constructor, including one whose result index provably contradicts the scrutinee's actual index. Nothing detects that contradiction; the branch is specialized and its body is checked against a type that only *looks* real. If a body can inhabit that "impossible" branch with an ordinary value (not `Std.absurd`/an eliminator of an empty type), that is a direct, first-class route to inhabiting `⊥`.
4. **Motive well-formedness.** `check_motive_wf/3` — untested in the negative direction: a malformed motive (not a valid type family over the index telescope + scrutinee) must be rejected as `{:error, :bad_motive}`.

These four obligations are the entire non-trivial surface of dependent `case` typing. Unlike totality (which needed only two known labels, terminating/diverging), this vertical has **four independent obligations**, each bidirectional (accept the good case, reject the bad case) — hence "deep cut."

## 2. Scope

**In scope:** all four obligations above, delivered **one at a time**, each with its own generator self-test + assay test + real-kernel run + (if it catches a real infection) a kernel fix + permanent antibody, before starting the next.

**Out of scope (explicitly deferred, Tier B or never):**
- The general dependent-term generator (bidirectional-inversion + INDIR). Not needed: every challenge here is built directly as Core (family declarations + constructors + a `case` def), the same way `Generators.Positivity` already hand-builds `SF`/`SVDesc`. See §7 for the YAGNI argument in full.
- Differential assays (subject-reduction, infer/check agreement) over arbitrary generated programs.
- Universe/cumulativity and constructor-injectivity/no-confusion verticals — candidate future deep cuts, not this one.
- Elaborator-level index unification (`lib/cure/elab/unify.ex`) — this vertical targets the **trusted kernel's** `case` checker only, matching Antigen's TCB-first mandate. A hole here is a hole in `Cure.Core.*`; a gap in the elaborator's `unify.ex` would only cause spurious elaboration failures (still safe), never unsoundness.

## 3. Architecture

Reuses 100% of the Tier-A harness: `Antigen.Gen`, `Antigen.Backend.StreamData`, `Antigen.Challenge`, `Antigen.Coverage`, `Antigen.Corpus`, `Antigen.Report`, `Antigen.Runner`, `Cure.Core.Serialize` (C2), the two-tier capture (`tmp/antigen/` ephemeral, `test/antigen/corpus.sexp` + `seeds.sexp` committed/never-pruned), the static replayer (`test/antigen/corpus_replay_test.exs`), and the architecture test forbidding `StreamData` under `Antigen.Generators.*`/`Antigen.Assays.*`.

**New modules:**

- **`lib/antigen/generators/indexed.ex`** (`Antigen.Generators.Indexed`) — builds each challenge as raw Core: one or two family declarations (`Inductive` family + constructor records), plus a global def whose body is a `{:case, scrut, motive, branches}`, registered directly into a `Cure.Core.Env`/signature — bypassing the elaborator entirely, identical in spirit to `Generators.Positivity`. One builder function per obligation (see §4), each returning a `Challenge.t()` with `payload: %{sig: ..., env: ..., def_name: ..., ...}` and a `label` of `:well_typed` or `:ill_typed`.
- **`lib/antigen/assays/indexed.ex`** (`Antigen.Assays.Indexed`) — runs `Cure.Core.Kernel.check_def(env, def_name)` and asserts the accept-iff-well-typed invariant:
  - `label: :well_typed` ⟹ expect `:ok` (completeness direction — a real hole here is "the kernel wrongly rejects legal code," annoying but not a soundness bug).
  - `label: :ill_typed` ⟹ expect `{:error, _}` (soundness direction — the kernel accepting this is an **infection**, exactly like `Assays.Totality`'s `:wrongly_certified`).
  - Verdict shape mirrors the existing assays: `:ok` | `{:violation, {:wrongly_accepted, reason}}` | `{:violation, {:wrongly_rejected, reason}}`.

**Unchanged:** `Antigen.Challenge.@known_atoms` gets one addition per PR — the new family/ctor/label atoms this vertical introduces (e.g. `:indexed_case`, `:well_typed`, `:ill_typed`, plus whatever family/ctor names each obligation invents), so a fresh process can decode committed records without having run a generator (the same fix the replayer needed for Tier A).

## 4. The obligation battery (build order)

Each obligation below contributes at least one `:well_typed` and one `:ill_typed` challenge, built by direct Core construction (ground truth is known by *how* the term was assembled — see §7). Built and verified **one at a time**, per the loop in §5.

### 4.1 Branch-family discipline
Two unrelated indexed families, `D` and `E`, each with ≥1 constructor. A `case` on a scrutinee of family `D` with a branch naming a constructor of `E`.
- `:ill_typed` — the foreign-constructor branch, expected rejected.
- `:well_typed` — the same `case` with all branches correctly drawn from `D`, expected accepted.

### 4.2 Coverage exactness
A family with ≥3 constructors.
- `:ill_typed` — a `case` covering only some of them, expected `{:error, :coverage}`.
- `:well_typed` — the same `case` with every constructor covered, expected accepted.

### 4.3 Index-refinement soundness (the crown jewels)
Two sub-probes, both against a family with a **computed** (non-variable) result index on at least one constructor (e.g. an indexed-`Nat`-like family with a `succ`-shaped constructor whose result index is `S k`, not a bare variable):

**(a) Compound-index refinement gap** — a branch for the computed-index constructor whose body's typing only succeeds if the (dropped) equation `index = S k` were substituted in; construct the body so that dropping the substitution changes whether it should typecheck.
- `:ill_typed` — a body that is only well-typed *under the false assumption* that the index equation was never applied (i.e., it exploits the gap), expected rejected.
- `:well_typed` — the analogous body that is correctly well-typed with or without the refinement, expected accepted (regression guard that the fix, if any, doesn't over-reject).

**(b) Impossible-branch inhabitation** — a scrutinee whose actual index provably excludes one declared constructor (e.g. scrutinee statically known to have index `Z`, but the family also declares a `succ`-indexed constructor whose result index can never unify with `Z`). Coverage still requires a branch for that constructor.
- `:ill_typed` — that impossible branch's body is an ordinary, non-absurd term of the motive's type (i.e. it "inhabits" a branch that should be statically unreachable), expected rejected.
- `:well_typed` — the same family/scrutinee with a branch that only reaches inhabitable cases correctly, expected accepted.

### 4.4 Motive well-formedness
- `:ill_typed` — a motive term that is not a valid type family over the index telescope + scrutinee (e.g. wrong arity, or a body that isn't a sort), expected `{:error, :bad_motive}`.
- `:well_typed` — a correct motive, expected accepted.

## 5. Per-obligation loop

For each of 4.1–4.4, in order:

1. **Generator self-test** — assert the label is real **by construction**, independent of the kernel's verdict (e.g. "this branch's constructor genuinely belongs to family `E`, not `D`" checked via `Inductive.get_ctor`/family lookup, not via `check_def`). This is the enduring detection proof, mirroring the Tier-A totality self-tests (`refute Certificate.terminating?(mutual)`).
2. **Assay test** — both directions (`:well_typed` → `:ok`, `:ill_typed` → violation), run against the assay module.
3. **Real-kernel run** — `mix test` scoped to this obligation's test file only (one build/test process at a time, per the standing constraint — never run concurrently with another full-suite invocation).
4. **Triage the result:**
   - If the `:ill_typed` case is correctly rejected and `:well_typed` is correctly accepted: obligation confirmed sound, no kernel change, move on.
   - If the `:ill_typed` case is **wrongly accepted** (a real infection): reproduce minimally, fix `Cure.Core.Kernel` (or `Certificate`/`Inductive` as appropriate) with its own red→green kernel test, bank the exact reproducing term as a permanent antibody in `test/antigen/corpus.sexp`, and re-run this obligation's assay to confirm it now reports `:ok` (no violation).
   - If the `:well_typed` case is **wrongly rejected** (incompleteness, not unsoundness): do **not** silently change kernel behavior. Log the finding and surface the fix-or-accept decision to the operator before touching kernel code.
5. **Full suite once**, commit, proceed to the next obligation.

This mirrors exactly how the totality vertical caught and fixed the mutual-recursion hole (spec `2026-07-01-antigen-tier-a-design.md` + `AUTOPILOT-REPORT.md`), generalized to four obligations instead of one.

## 6. Regression and corpus

Identical mechanics to Tier A: every confirmed infection's reproducing term becomes a permanent, never-pruned antibody in `test/antigen/corpus.sexp`, replayed statically (no generation) by `test/antigen/corpus_replay_test.exs` on every `mix test`. Known-good challenges (the `:well_typed` side of each obligation) seed `test/antigen/seeds.sexp` via the existing coverage-deduped seed bank. Both stores use the existing tab-delimited, C2-serialized (`Cure.Core.Serialize`) record envelope — no format changes.

## 7. Why no term generator is needed here (YAGNI)

The general dependent-term generator (Tier B, bidirectional-inversion + INDIR, per the research synthesis in [[antigen-metatheory-engine]]) solves a different problem: generating an arbitrary well-typed term when the ground truth ("is this legal?") is *not already known* — which forces the oracle problem (checking the kernel's homework with the kernel itself).

Every obligation in §4 avoids that problem by construction: the label is fixed by *how the challenge is assembled*, not inferred by running the checker. "A branch naming a foreign-family constructor" is ill-typed because we picked two families and wired the mismatch in by hand — no generator or oracle needed to know that. This is exactly the technique `Antigen.Generators.Positivity` and `Antigen.Generators.Totality` already use, and it is what let Tier A catch the real mutual-recursion hole without any general term generator existing. Building the general generator now, because this work is "in the area," would be premature generality for a problem this deep cut does not have — the general generator remains a distinct, later initiative (Tier B) that this spec does not touch.

## 8. Testing

- `test/antigen/generators/indexed_test.exs` — one self-test per obligation (§5 step 1), 8 tests total (2 per obligation × 4 obligations).
- `test/antigen/assays/indexed_test.exs` — one accept + one reject test per obligation, 8 tests total.
- Any kernel fixes get their own red→green tests under `test/cure/core/kernel_test.exs` (or a new `test/cure/core/case_soundness_test.exs` if the fixes are substantial enough to warrant a dedicated file — decided at fix time, not speculatively now).
- `test/antigen/corpus_replay_test.exs` requires no changes — it already replays whatever is in `corpus.sexp`/`seeds.sexp` generically via the assay registry; this vertical only adds `"indexed/case" => Assays.Indexed` to that registry.

## 9. Success criteria

1. All four obligations (§4) have generator self-tests, assay tests, and have been run against the real kernel — one at a time, with a full suite run between each.
2. Every confirmed infection (an `:ill_typed` challenge the kernel wrongly accepts) is fixed in the trusted kernel with its own red→green test, and its reproducing term is a permanent antibody in `corpus.sexp`.
3. Every `:well_typed` challenge is accepted by the (possibly now-fixed) kernel — no obligation's fix over-rejects legitimate code.
4. `mix test` is fully green at the end: the new tests pass, the existing 2100 tests are unaffected, and the corpus replayer covers the new `indexed/case` entries.
5. Any incompleteness finding (a `:well_typed` case wrongly rejected) is reported to the operator rather than silently patched.

## 10. Non-negotiable constraints carried over

- Serialize each committed record with `Cure.Core.Serialize` (C2); force-intern new atoms in `Antigen.Challenge.@known_atoms`.
- One `mix test`/`mix compile` process at a time — never concurrent (past concurrent runs caused a kernel panic).
- Ghost-written commits; no co-author trailers.
- Antibodies are never pruned once committed.
