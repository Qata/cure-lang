# Antigen ill-typed mutation corpus — design

**Parity ledger:** Tier-B follow-on (the "ill-typed mutation corpus" item listed
in the Tier-B report §"Reach left open"). Realizes the *second polarity* of
soundness testing.

**One-liner:** generate deliberately ill-typed Core terms whose ill-typedness is
guaranteed by construction, run them through an inverted "rejection" assay, and
bank any term the kernel **accepts** as an unsoundness antibody — because a type
system that admits a bad term is, by definition, unsound.

---

## 1. Motivation — the second polarity

Tier-B's `:typed_term` corpus tests **false breakage**: well-typed terms that the
kernel then mishandles (infer≠check, subject-reduction failure, non-idempotent
normalization). That is one half of soundness. The other half is **false
acceptance**: an *ill-typed* term the kernel should reject but instead admits.

| Class | Term is | Kernel should | Violation = | Assay polarity |
|---|---|---|---|---|
| False breakage (Tier-B, exists) | well-typed | check/reduce consistently | internal inconsistency | self-consistency |
| **False acceptance (this spec)** | ill-typed | **reject** it | kernel returns `{:ok, _}` | **inverted** |

`infer/2` returns `{:ok, Value} | {:error, reason}` and `check/3` returns
`:ok | {:error, reason}`. "The kernel rejected it" = an `{:error, _}`; a
mutation-corpus **violation** = the kernel returns `{:ok, _}` / `:ok` on a term we
*know* is ill-typed.

The banking machinery already supports this with no change: `Runner.explore/1`
banks any challenge whose assay returns `{:violation, _}` via
`Corpus.append(corpus_path, c, Corpus.dedup_key(c, :antibody))` — it is
label-agnostic. This spec supplies the generator that produces ill-typed terms and
the assay whose polarity is inverted.

---

## 2. Scope (v1) and non-goals

**In scope:** the same `SigMenu` v1 fragment (Nat, Bd, indexed Vec, certified
plus/dbl) plus the Sigma/pair and `{:type, i}` term forms the kernel already
supports. Reuses the lazy `gen_term` (`Generators.Term`, commit `4d3eeed`) as the
source of well-typed base material into which faults are injected.

**Trust anchor — construction-guaranteed ill-typedness (LOCKED):** a mutant's
ill-typedness must be decidable from the *edit itself*, independent of the
kernel-under-test. No differential oracle in v1 (that would couple this to the
Idris port and its headless-availability constraints; deferred to a follow-on).

**Non-goals (explicit follow-ons):** differential-oracle mutations; ill-typed
terms outside the v1 menu; value-level or ChoiceSeq shrinking of antibodies (the
`ChoiceSeq` reference spec §9 gate depends on *this* corpus producing real
antibodies first — see §9).

---

## 3. The correctness invariant (why an antibody is real)

An antibody is only genuine if the mutant is truly ill-typed. Every injected fault
MUST satisfy both clauses:

> **(a) Checked position.** Inject only where the mode-directed generator is
> actively checking against a concrete goal — application arguments, constructor
> arguments, function bodies, scrutinees, and (for the universe fault only) sort
> goals. Never into a motive, a type-annotation-only slot, or any position the
> typechecker does not force.
>
> **(b) Decidably non-convertible replacement.** The injected term's type must
> differ from the expected type at the site by a *decidable* witness: either a
> **distinct type-former head** (Nat / Vec / Bd / Pi / Sigma / Type are pairwise
> non-convertible) or, within one family, a **distinct closed index** (expected
> `Vec Z`, inject `Vec (S Z)` — non-convertible because `Z` and `S _` are distinct
> constructors), or a **distinct universe level** (`Type₀ : Type₁ ≠ Type₀`).

**Why (a) is sound for Cure specifically.** Cure's typechecker checks *all* term
positions — erasure is a runtime/compilation concern, not a typechecking one
(e.g. bidirectional application `f a` infers `f : Π A B` and then *checks* `a : A`
regardless of whether the bound variable is used). So a fault in a genuine term
position propagates to a top-level `infer`/`check` error in a correct kernel:
"the kernel should reject this" is a theorem, not a hope.

**Why (b) is sound.** All witnesses are *decidable syntactic* inequalities on
normal forms (distinct head constructors / distinct closed index ctors / distinct
levels), so no appeal to the kernel-under-test is needed to know the mutant is
ill-typed. This rules out the failure mode where a "mutation" accidentally lands
on a still-well-typed term and produces a **false** antibody.

**Guard.** A meta-test (see §7) asserts the invariant reflexively for the
generator: it re-derives, for every operator, that `expected_head ≠ injected_head`
(or the index/level witness) using ONLY the recorded `fault` provenance and menu
metadata — never by calling the kernel — so the "known ill-typed" label is proven
independently of the thing under test.

---

## 4. Challenge model

- **Kind:** new `:mutant_term`. Being a distinct kind, it is automatically excluded
  from the `:typed_term` health gate (`Runner.health_metrics/1` filters
  `match?(%Challenge{kind: :typed_term}, _)`), so the two corpora never contaminate
  each other's metrics.
- **Label:** `:ill_typed`.
- **Assay id:** single `mutation/rejection`.
- **Payload** (extends the `:typed_term` shape):
  ```
  %{
    sig: :v1,
    ctx: [type, ...],           # rebuilt via SigMenu.rebuild_context/2
    type: goal_type,            # the goal at the injection site's ROOT term
    term: mutant_term,          # the ill-typed Core term
    fault: %{
      kind: :head_swap | :ctor_arg | :index_mismatch | :app_domain
          | :out_of_scope_var | :proj_non_pair | :universe,
      expected_head: atom,      # e.g. :Nat / :Vec / :Sigma / {:type, 0}
      injected_head: atom,      # e.g. :Vec / :Bd / :not_a_pair / {:type, 0}
      witness: :head | :index | :level | :scope   # which invariant-(b) clause
    }
  }
  ```
  The `fault` record makes an antibody self-documenting and is what the vacuity
  gate buckets on (§6).

The `:mutant_term` kind gets `Challenge.to_pieces`/`from_pieces` clauses and a
`Coverage.terms_of` clause (mirroring `:typed_term`) so it round-trips through the
C2 corpus serialization and participates in coverage keying.

---

## 5. Fault operators (7, v1)

At generation time `gen_mutant` runs the ordinary lazy `gen_term` but, at exactly
**one** randomly chosen node, dispatches to a fault operator (chosen among those
*applicable* at that node's goal) instead of the normal inhabitant. Each operator
is construction-guaranteed by §3.

| # | Operator (`fault.kind`) | Injection | Applies at | Kernel rejection |
|---|---|---|---|---|
| 1 | `:head_swap` | goal `Nat` → emit a `Vec`; goal `Vec _` → emit a `Bd` | any menu-typed site | conv / type mismatch |
| 2 | `:ctor_arg` | `vcons(n, x, xs)` with `x : Vec` (not `Nat`) | vcons sites | conv mismatch |
| 3 | `:index_mismatch` | goal `Vec Z` → emit well-typed `Vec (S Z)` | Vec sites | conv (index) mismatch |
| 4 | `:app_domain` | `f a` where `f : Nat→Nat`, emit `a : Vec` | app sites | Π-domain mismatch |
| 5 | `:out_of_scope_var` | `{:var, k}` with `k ≥ length(Γ)` | any site | `{:error, {:unbound_var, _}}` |
| 6 | `:proj_non_pair` | `{:fst, e}` / `{:snd, e}` with `e : Nat` | any site (standalone) | `{:error, :not_a_sigma}` |
| 7 | `:universe` | at a `{:type, 0}` goal, emit `{:type, j}` (j ≥ 0) → `Type₀ : Type₀` | sort goals | universe / stratification |

Notes:
- **Operator 3** is the dependent-type fault surface — a kernel sloppy about index
  conversion is exactly the subtle unsoundness most worth catching, and
  generation-time injection buries it in a real, deep surrounding term.
- **Operator 6** is standalone: the kernel rejects `{:fst, e}` the moment it infers
  it (`ensure_sigma(Nat) → {:error, :not_a_sigma}`), before the goal is consulted,
  so it needs no Σ goal in the menu.
- **Operator 7** fires only at sort goals, so `gen_mutant` adds `{:type, 0}` to its
  goal space (the well-typed generator deliberately omits it — see the Tier-B
  goal-space note). This exercises the actual universe rule rather than a generic
  conv-mismatch.
- **Applicability is site-dependent** (universe → sort goals; index-mismatch →
  Vec goals; head-swap/out-of-scope/projection → any site). Operator selection
  weights across the *applicable* set at the chosen site; weights are tuned so no
  single operator dominates (enforced by the §6 diversity floor).

**Generation totality.** If no operator is applicable at the drawn site (or the
draw would produce a degenerate mutant), `gen_mutant` re-draws a different site;
bounded by a fixed attempt budget, after which it falls back to operator 5
(out-of-scope var), which is applicable at any non-empty position. This guarantees
`gen_mutant` always yields a well-formed `:mutant_term` challenge.

---

## 6. The rejection assay + vacuity gate

### 6.1 `Antigen.Assays.Mutation` (`mutation/rejection`)

```
run(%Challenge{kind: :mutant_term, payload: %{ctx: ctx, term: term}}):
  rebuild Γ; case Kernel.infer(Γ, term) do
    {:error, _reason} -> :ok                 # correct rejection — mutant killed
    {:ok, _ty}        -> {:violation, {:accepted_ill_typed, term, fault}}
  end
```

Rationale: `infer` is the strongest gate (a term the kernel cannot even infer a
type for is soundly rejected). We use `infer` rather than `check` because the
mutant's root goal may itself be synthetic; `infer` needs no expected type and
its `{:error, _}` is the unambiguous "rejected" signal. (A mutant that infers a
type but that type is "wrong" is not possible under §3(b): a decidably
non-convertible fault forces the inference itself to fail at the faulted node.)

A **correct rejection returns `:ok`** — so under replay, banked mutants act as a
regression guard that the kernel *stays* appropriately strict (catching a future
change that makes the kernel too permissive). A **violation** banks the mutant as
an antibody. Expected steady state: **0 violations**.

### 6.2 Vacuity gate — rejection-reason diversity floor

A corpus where every mutant trips the *same shallow* rejection gives false
confidence ("0 survivors") while exercising one path. Guard analogously to the
Tier-B health gate:

- **Metric — `reason_diversity`:** the count of **distinct `fault.kind` values that
  were correctly rejected** over the `:mutant_term` subset. Bucketing on
  `fault.kind` (recorded provenance) rather than on the raw kernel `{:error,
  reason}` tag is deliberate: operators 1–3 all bottom out in the kernel's
  conversion-mismatch reason, so raw-tag bucketing would undercount them as one
  path. `fault.kind` distinguishes the exercised rejection *surfaces* correctly.
  (The raw kernel reason still rides along in the antibody for debugging.)
- **Floor:** `reason_diversity ≥ 5` (of the 7 operator kinds). Chosen below 7 so a
  run that happens not to draw a couple of the site-restricted operators
  (universe/index need specific goals) is not spuriously flagged, while still
  forcing broad coverage.
- **Also reported:** `survivors` (violation count; expected 0) and
  `mutants_total`. The **stamp measures vacuity only**, so it is a pure function
  of diversity: `:healthy` when `reason_diversity ≥ 5`, else `:vacuous`.
  `survivors` are NOT part of the stamp — a survivor is a genuine unsoundness
  finding, surfaced separately as an infection/antibody (§6.1), not a vacuity
  signal. (A vacuous-but-survivor-free run and a healthy-with-a-survivor run are
  both possible and mean different things; conflating them into one stamp would
  hide the survivor.)
- Scope: computed over the `:mutant_term` subset only, mirroring the `:typed_term`
  scoping of the existing gate. A `mix antigen` run prints an
  `antigen health[mutant_term]: reason_diversity=… survivors=… → …` line.

---

## 7. Testing strategy (TDD; artifact is executable code)

Red-green per plan step. The behavioral test families:

1. **Construction guarantee (the load-bearing test)** — for every operator, sample
   mutants and assert `Kernel.infer(Γ, term)` returns `{:error, _}`. This is the
   ground-truth that mutants really are ill-typed *and* that a correct kernel
   rejects them. (If the kernel under test had a real permissiveness bug, this test
   would surface it as a genuine failure — which is the whole point; it is not
   masked.)
2. **Invariant-(b) meta-test (kernel-independent)** — for every operator, assert
   `expected_head ≠ injected_head` (or the index/level witness) using ONLY the
   `fault` provenance + menu metadata, NEVER the kernel. Proves the "ill-typed"
   label is warranted without trusting the thing under test (§3 guard).
3. **Assay polarity** — `Assays.Mutation.run/1` returns `:ok` on a correctly
   rejected mutant and `{:violation, {:accepted_ill_typed, _, _}}` on a synthetic
   "kernel accepted" stub (inject a fake `{:ok, _}` via a seam) — proving the
   inverted polarity wiring, since with a correct kernel no real violation occurs.
4. **Diversity floor** — over a sampled `:mutant_term` batch, assert
   `reason_diversity ≥ 5`; a static-replay meta-test enforces the floor on the
   banked corpus (mirrors the Tier-B health-gate meta-test).
5. **Serialization round-trip** — a `:mutant_term` challenge survives
   `Serialize.encode |> decode` unchanged (C2), and the replay registry
   (Runner + `corpus_replay_test`) maps `mutation/rejection → Assays.Mutation`.
6. **Generator totality** — `gen_mutant` never yields a malformed challenge across
   a large sample (the fallback-to-operator-5 path is covered).
7. **Kind isolation** — `:mutant_term` challenges are excluded from
   `health_metrics/1` (the `:typed_term` gate), asserted directly.

**On the corpus-replay/banked seeds:** banked `:mutant_term` seeds carry the
`mutation/rejection` assay id; `corpus_replay_test`'s registry map and
`test/antigen/seeds.sexp` must learn it (the exact gap that bit Tier-B Task 10).

---

## 8. Architecture & integration

New/changed files:
- **Create** `lib/antigen/generators/mutation.ex` — `Antigen.Generators.Mutation`:
  `gen_mutant/2`, `typed_term`-analog `mutant/1` emitting the challenge, the 7
  operator functions, applicability + weighted selection, `fault` provenance.
  Reuses `Generators.Term`/`SigMenu` internals via their public seams; must
  stay **StreamData-free** (architecture_test quarantine — build via `Antigen.Gen`
  only).
- **Create** `lib/antigen/assays/mutation.ex` — `Antigen.Assays.Mutation` (§6.1),
  with the `:ok`-injection seam for test #3.
- **Modify** `lib/antigen/challenge.ex` — `:mutant_term` in `@type kind`,
  `@known_atoms` additions (`:mutant_term, :ill_typed, :head_swap, :ctor_arg,
  :index_mismatch, :app_domain, :out_of_scope_var, :proj_non_pair, :universe,
  :fst, :snd, :pair, :sigma`), `to_pieces`/`from_pieces` clauses.
- **Modify** `lib/antigen/coverage.ex` — `terms_of(%Challenge{kind: :mutant_term})`.
- **Modify** `lib/antigen/runner.ex` — assay registry
  (`mutation/rejection → Assays.Mutation`), the `mutant_term` diversity metric +
  health line, and `mutant/1` wired into `default_gen`.
- **Modify** `lib/mix/tasks/antigen.ex` — add the `:mutant_term` branch to
  `default_gen`.
- **Modify** `test/antigen/corpus_replay_test.exs` — `mutation/rejection` in the
  replay `@registry`; **bank** coverage-deduped `:mutant_term` seeds into
  `test/antigen/seeds.sexp`.

Constraints (verbatim from project conventions):
- **StreamData quarantine:** nothing under `generators/`/`assays/` may reference
  `StreamData` (grep-enforced by `architecture_test.exs`).
- **Ghost-authored commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`,
  no `Co-Authored-By`.
- **One full build/test run at a time** (a past concurrent full-suite run caused a
  kernel panic).
- Health metrics that call `Normalise.nf` pass `fuel:` (the `:mutant_term` gate
  uses `infer` only, so this mostly doesn't apply — but any nf call added must be
  fueled, per the Tier-B locked decision).

---

## 9. Relationship to the ChoiceSeq backlog spec

This corpus is the **precondition** the `ChoiceSeq` reference spec's decision gate
(§9 there) waits on: shrinking has nothing to minimize until a generator produces
real antibodies. The follow-on sequencing is:

1. **This spec** lands the mutation corpus (antibodies now possible).
2. A **value-level greedy post-shrink** (rewrite the reified `%{ctx, type, term}`
   artifact directly, re-validating each edit through the kernel) is the cheap
   first minimizer — its natural home is a small follow-up that uses this corpus'
   antibodies as its test fixtures. *Deliberately not in this spec* (YAGNI: build
   the antibody source before its minimizer).
3. Only if value-level post-shrink leaves deep antibodies visibly non-minimal do we
   build `ChoiceSeq` (its headline red test §7.6 reuses a mutation antibody).

Expected steady state of THIS spec on a correct kernel: **0 survivors, healthy
diversity** — the corpus is a standing net that will bank an antibody the day a
future kernel change makes type-checking unsound in one of the seven ways.
