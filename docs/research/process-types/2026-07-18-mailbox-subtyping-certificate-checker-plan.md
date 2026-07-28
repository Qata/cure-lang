# Plan — Verified certificate checker for mailbox-type subtyping (SMTCoq-style)

**Status:** design + phased plan, ready to hand off.
**Author handoff:** this is a self-contained thread. It does NOT need the general
Presburger/Z3 backend for the commutative-regular mailbox domain — see §2.

## 0. Goal

Decide **semantic subtyping** `E ⊆ F` for mailbox types (the commutative-regex
`Pat` algebra in `metatheory/otp/oracle/otp/mailbox_pattern.cure`: `PZero | POne | PAtom | PPlus
| PTimes | PStar`), where `E ⊆ F` means *every message multiset accepted by `E` is
also accepted by `F`* (`∀m. Accepts(E, m) → Accepts(F, m)`).

The shipped `Incl` inductive + `incl_sound` is a SOUND but INCOMPLETE *syntactic*
subtyping. This thread adds a **verified certificate checker** that decides the full
semantic inclusion with the untrusted search kept out of the TCB — the SMTCoq
architecture, specialized to this one theory.

## 1. The architecture (three components)

1. **Untrusted producer** — searches for a certificate. Kept out of the TCB; may be
   buggy without compromising soundness (a bad certificate is *rejected* by the
   checker).
2. **Verified checker** — a TOTAL Cure function `check_incl(R, E, F) : Bool`, PROVEN
   SOUND: `check_incl(R, E, F) = T → ∀m. Accepts(E, m) → Accepts(F, m)`. This is the
   only trusted addition, and it is trusted only because the existing kernel checks
   its soundness proof — the TCB (the kernel) does NOT grow.
3. **Reflection integration** — when the elaborator faces an `E ⊆ F` obligation it
   can't discharge syntactically, it runs the producer to get `R`, then discharges
   the obligation by *computing* `check_incl(R, E, F) = T` (the kernel evaluates the
   verified checker — computational reflection). No new kernel rule.

## 2. Key insight: NO Z3 needed for this domain

Because mailbox types are commutative *regular* expressions, the certificate is a
**finite derivative-based inclusion invariant** (Hopcroft–Karp / Brzozowski
coinductive style), and the producer is a plain **derivative-closure exploration**,
not an SMT search. Z3/Presburger is only needed if this is later generalized to
richer constraint domains (dependent payloads, counting refinements) — leave that as
a Phase-4 extension point, not part of this thread.

## 3. The certificate format

A certificate is a **finite relation** `R : List (Pat × Pat)` — a candidate
inclusion invariant. `check_incl(R, E, F)` verifies THREE structural conditions:

- **(C0) start:** `(nrm E, nrm F) ∈ R`.
- **(C1) local safety:** for every `(E', F') ∈ R`, `nullable(E') = T ⟹
  nullable(F') = T`. (If `E'` can accept the empty mailbox, so must `F'` — the
  no-orphan condition at each state.)
- **(C2) closure under derivatives:** for every `(E', F') ∈ R` and every tag `t`,
  `(nrm (deriv E' t), nrm (deriv F' t)) ∈ R`.

`∈ R` is decidable list membership under the equality the checker uses. All three
checks are total and structural (evaluate `nullable`/`deriv`/`nrm`, compare `Pat`s,
scan `R`).

### The `nrm` decision (do this first)

Derivatives grow `Pat` syntactically (`deriv(PStar a, t) = PTimes(deriv a t,
PStar a)`), so a finite `R` closed under raw `deriv` does not exist. Two options —
**pick one up front, it shapes everything:**

- **(a) Brzozowski + ACI normalization.** Define `nrm : Pat → Pat` (flatten/sort/dedup
  `PPlus`, unit/zero laws) making derivatives finite up to `nrm`, and PROVE
  `nrm`-soundness: `Accepts(nrm E, m) ↔ Accepts(E, m)`. Reuses the existing `deriv`.
  Soundness of the checker then *steps through* `nrm`, so `nrm`-soundness is load-bearing.
- **(b) Antimirov partial derivatives.** `pderiv : Pat → Tag → Set Pat` yields finite
  sets with NO ACI normalization needed (finiteness is structural). Cleaner
  metatheory, but a new `pderiv` + its soundness/completeness vs `Accepts`.

**Recommendation:** start with (a) — it reuses the shipped `deriv`/`Accepts`/`nullable`
and the full Brzozowski theorem; `nrm`-soundness is a bounded, self-contained lemma.

## 4. The soundness theorem and its proof (the payoff of the shipped Brzozowski work)

`check_incl_sound : check_incl(R, E, F) = T → (m : MS) → Accepts(E, m) → Accepts(F, m)`

Proof chains the **already-shipped** Brzozowski fundamental theorem:

1. **Invariant lemma** (induction on a message word `w`, using C0 + C2):
   `(nfold E w, nfold F w) ∈ R` for all `w`, where `nfold` folds `λE' t. nrm(deriv E' t)`.
   Relate `nfold` to `dfold` via `nrm`-soundness.
2. Given `Accepts(E, m)`: by **`matches_word_complete`** (shipped) there is a word
   `w` with `parikh(w) = m` and `nullable(dfold E w) = T`; hence
   `nullable(nfold E w) = T` (via `nrm`-soundness).
3. By the invariant + **(C1)**, `nullable(nfold F w) = T`, hence
   `nullable(dfold F w) = T`.
4. By **`matches_word_sound`** (shipped), `Accepts(F, parikh(w)) = Accepts(F, m)`. ∎

So the checker's soundness is essentially a corollary of `matches_word_sound` +
`matches_word_complete` + the invariant closure. This is the reason the Brzozowski
completeness half (`8b237eef`) was worth proving.

## 5. Phased plan

- **P1 — Verified checker + soundness (Cure metatheory; oracle `rel=same`).**
  In a NEW oracle probe (e.g. `otp_mailbox_subtyping.{cure,idr}`) OR extending
  `mailbox_pattern` (watch the 30s oracle budget — the module is already ~16s under
  concurrent load; a new self-contained probe re-deriving only the needed subset is
  safer): define `nrm` + `nrm`-soundness, `check_incl` over an explicit `R`, and prove
  `check_incl_sound`. Include a concrete positive certificate (an `E ⊆ F` the syntactic
  `Incl` cannot derive) and a NEGATIVE antibody (a bad `R` where `check_incl = F`, and/or
  an `E ⊄ F` whose counterexample multiset refutes inclusion via the Brzozowski
  decision `matches_word = nullable∘dfold`). Idris mirror, `rel=same`.
  *This is the whole metatheory core; it is fully in-kernel and needs no solver.*

- **P2 — Untrusted producer (Elixir, `lib/cure/…`, NOT TCB).** A derivative-closure
  BFS: from `(nrm E, nrm F)`, repeatedly add `(nrm(deriv E' t), nrm(deriv F' t))`
  until fixpoint (terminates: finitely many derivatives up to `nrm`). Emit `R` if
  every reached pair satisfies C1, else report the witnessing pair (a
  counterexample seed). No Z3.

- **P3 — Reflection integration (E-layer).** Where the elaborator meets an `E ⊆ F`
  mailbox-subtyping obligation the syntactic path can't close: call the P2 producer,
  build the `check_incl(R, E, F)` term, and let the kernel discharge the goal by
  computing it to `T` (reflection). On producer failure, fall back to the existing
  syntactic `Incl` path / honest error. Additive — never weakens soundness (the
  kernel re-runs the verified checker).

- **P4 — (Later, out of this thread) Z3/Presburger backend** for non-regular
  extensions (counting/dependent-payload refinements) — a genuine SMTCoq-style
  arithmetic-certificate checker. Only if a real need appears; commutative-regular
  subtyping does not require it.

## 6. Layer map, files, constraints

- **Layer:** P1 is **K/metatheory** (Cure proofs, oracle-verified — the trust rests on
  the kernel checking `check_incl_sound`, so the TCB does NOT grow). P2 is untrusted
  tooling (`lib/cure/*`, Elixir). P3 is **E-layer** (elaborator), additive, kernel
  re-checks.
- **Two-pipeline steer:** all dependent machinery is in `lib/cure/elab/*` +
  `lib/cure/core/*`. IGNORE `lib/cure/compiler/*` and `lib/cure/types/*` (non-dependent
  decoys). The subtyping obligation surfaces in the elaborator; the checker is a Cure
  proof, not an Elixir kernel change.
- **Oracle discipline:** paired `.cure`/`.idr`, `mix cure.oracle otp`, `rel=same`
  required; replay green before commit. Watch the per-probe 30s Cure budget.
- **TCB discipline:** the ONLY thing trusted here is `check_incl_sound` — and it is a
  kernel-checked Cure theorem, so nothing new is *assumed*. Do NOT add kernel rules; do
  NOT trust the producer or Z3. If P1 seems to need a kernel change, STOP and report
  (prove no untrusted term works first — the elaborator-hard-stop rule).
- **Ghost commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no
  Co-Authored-By, explicit-pathspec staging only.
- **Report:** exact diffs, red→green evidence, oracle output, honest generality
  statement (which inclusions the checker decides vs the producer's completeness).

## 7. Definition of done (P1, the core)

`check_incl` + `check_incl_sound` proven in Cure, Idris `rel=same`, with (i) a positive
certificate for an inclusion outside the syntactic `Incl` fragment and (ii) a negative
antibody, all green under replay. P2/P3 are follow-on integration once P1 lands.
