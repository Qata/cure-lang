# Handoff brief — formalize the OTP process algebra metatheory *in Cure*

*2026-07-16. A cold-start work order for the agent picking up the process-types
formalization. You need no prior context from the conversation that produced this
— everything load-bearing is below, with exact file paths. Read §3's docs before
writing code.*

---

## 0. TL;DR — what you are building

Two type-theory results that the published literature has **not** fully solved,
formalized **in Cure itself** (not Idris/Agda/Lean), shipping as a kernel-checked
stdlib artifact `Std.Otp.Proof` plus Idris oracle mirrors:

1. **Obligation (1) — per-constructor dependent `ReplyOf(req)` with a *linear*
   reply capability.** Each request constructor carries its *own* reply type; the
   reply capability is consumed exactly once. Prove **preservation**: a well-typed
   `reply(cap, v)` requires `v : ReplyOf(req)` and consumes `cap` linearly. This is
   **strictly more expressive than anything in the literature** (NVLang types every
   constructor's reply *uniformly*; see §3). Do this one **first** — it is the
   harder and more novel of the two.
2. **Obligation (2) — send-safety for a clause-*derived* pid message index (F-1).**
   When the message vocabulary is derived from an actor's handler clauses and used
   to index its `Pid`, prove that a well-typed `send` can never deliver a message
   the actor cannot handle. NVLang founds this index *by annotation*; deriving it
   from clauses is the open part.

**Sequencing rule: spike before spec.** Do not write an implementation plan first.
Write the minimal calculus (§6), push it at the compiler, and let the first
roadblock name the missing capability. *Then* spec the capability expansion.

---

## 1. Why this matters and why it is unblocked

`Std.Otp` / `Std.Otp.Raw` was audited for conformance to the BEAM
(`docs/research/process-types/raw-algebra-conformance-checklist.md`). Five defects
where the types claimed more than the BEAM delivers (F-2, F-2c, F-3, F-4, F-5) are
**fixed and merged** into `feature/idris-parity`. Two frontier items remain, and
they are the obligations above:

- **F-1** (pid index founded on nothing) — deferred, "Rung 2."
- **Per-constructor `ReplyOf`** — currently a *free, return-polymorphic* result.
  See the exact spot: `lib/std/otp_raw.cure` `raw_call`, whose docstring says "the
  reply type is where `Std.Otp` threads the dependent `ReplyOf(req)`; here it is a
  free (return-polymorphic) result."

**Common misconception to avoid:** these are *not* blocked on the macro facility.
The macro plumbing (`derive_actor` / `derive_reply_contract` in `lib/std/actor.cure`,
reply inference across call arms, linear callback reply capabilities) is **already
landed and green**. The macro can already *derive and thread* a reply type. What is
missing is the **type theory** — the sound *rule* for a request-indexed, linearly
consumed reply, and for a clause-derived pid index. That theory is what you are
building, and it is independent of and parallel to the (finished) plumbing.

---

## 2. The decision you are executing

**Venue = Cure. Oracle = Idris. A roadblock is a capability to build, not a reason
to retreat.**

- Author every load-bearing lemma in Cure.
- Mirror the core lemmas into the Idris differential oracle (§7) as insurance:
  agreement buys trust; a divergence localizes the fault to one side instead of
  leaving you asking "is it my proof or the prover?"
- When Cure can't yet express something, **expand Cure** (surface syntax, coverage,
  a combinator) rather than route the whole proof to Idris. TCB changes are
  pre-approved *iff* aligned with Idris, Agda, or Lean (Idris-only suffices) — but
  still run the full gate. Fall back to Idris-primary for a *single* lemma only if
  it hits the one known-young spot (§8).

Rationale (why Cure is genuinely the right venue, not a compromise): Cure is
already a working proof assistant for this exact genre — `lib/std/proof.cure`
proves `plus_comm` by induction + `rewrite`/`reflexive`, "the technique Agda's
`Data.Nat.Properties` uses." And Cure has **QTT natively**, so the *linear* reply
capability is a native fit that even Idris 2 (which Cure is modeled on) only
matches and Agda would have to encode. The Lean bridge was deliberately removed
(task #17); Cure's kernel is the checker. This also advances the self-hosted rung
of the correctness ladder and the Evidential-Systems doctrine.

---

## 3. Required reading (do this before writing code)

**Papers (all in `docs/research/process-types/`):**

| File | Read for | Key extraction |
|------|----------|----------------|
| `nvlang-2512.05224.pdf` | The closest shipping system. | `T-Spawn` founds `Pid[τm]` from the actor's **`receive msg : M` annotation** (rule `Extract-Msg`) — the soundness recipe for **obligation (2)**, but *annotation-driven*, so it does **not** solve the clause-*derivation* half. Its **Uniform-Reply** constraint (every constructor replies the *same* `τr`) is **strictly weaker** than obligation (1) — do **not** regress to it. Also: NVLang has **no effect tracking**, so it is not "Cure minus dependent types." |
| `special-delivery-2306.12935.pdf` | Reply typing oracle. | Fresh-reply-mailbox-per-call is the richer model that actually types the **heterogeneous** reply case — the real oracle for obligation (1). |
| `mailbox-types-1801.04167.pdf` | Mailbox typestate background. | Commutative presence/exhaustion/multiplicity discipline. Context, not directly on the critical path. |
| `kwc-signals-monitors-erlang2023.pdf` | Ordered-mailbox + monitor operational semantics. | The operational oracle for message *order* and `monitor`/`demonitor`/`DOWN`. **Excludes timers** — no help on the timer algebra. |
| `deadlock-monitors-gen_server-2508.14851.pdf` | Scoping. | Deadlock/liveness is handled by **runtime monitoring**, not the type system — confirms it is out of scope here. |
| `core-erlang-formalisation-2311.10482.pdf` | Target semantics. | Core Erlang operational model; the reduction relation your preservation proof reduces *over*. |

**Project docs (read in this order):**

1. `docs/research/process-types/raw-algebra-conformance-checklist.md` — the audit; F-1…F-5 defect definitions and the raw algebra.
2. `docs/research/process-types/2026-07-16-oracle-papers-synthesis.md` — how the three newest papers re-rank the ledger (the source of the §3 table above; §2a/§2b there are the F-1 and reply-typing analyses).
3. `docs/superpowers/specs/2026-07-02-lean-shape-matching-design.md` and `2026-07-02-dependent-match-surface-design.md` — the dependent-match coverage algorithm; **its incompleteness is your most likely roadblock** (§8).

---

## 4. What Cure already gives you (with exact pointers)

Confirm each against the cited exemplar before relying on it — surface syntax
evolves.

- **Large elimination / type-valued functions** (needed for `ReplyOf : Req -> Type`):
  - `lib/std/optic.cure:86` — `fn Lens(s: Type, a: Type) -> Type = Optic(s, a, LensKind)`
  - `lib/std/sigma.cure:25` — `type Sigma(a: Type, b: (a) -> Type) indices ()`, and
    `:32/:37` show a **dependent return type** `-> b(sigma_first(p))`.
  - Oracle cluster `test/oracle/largeelim/` — large elimination is regression-tested.
- **Propositional equality + transport:** `lib/std/equivalent.cure` (`Equivalent`,
  the `refl` witness) and `lib/std/proof.cure` (worked inductive proofs with
  `rewrite … in reflexive(…)`). This is your template for a preservation proof.
- **`with … proof` abstraction** (refine a scrutinee while carrying its equality —
  *the* subject-reduction move): `test/oracle/with/wi04_proof_used.cure:8` —
  `with g(n) proof pf`, whose Idris twin `wi04_proof_used.idr:13` is
  `foo n with (g n) proof prf`. Cluster `test/oracle/with/`.
- **Decidability / negation:** `lib/std/decision.cure` — `Decision(P)` = `Yes(proof)`
  | `No(disproof)`, `type Empty = |`, and `Not(P)` spelled `P -> Empty`.
- **Dependent pairs (Σ):** `lib/std/sigma.cure` — package a request with its
  reply-typed continuation: `Sigma(x: a, b(x))`.
- **QTT grades in the kernel:** grades `{0, 1, ω}` are checked (see the QTT gate;
  kernel is `lib/cure/core/**`, TCB). **BUT SEE §8** — surface grades on
  λ-binders / constructor-fields are *deferred*, which is exactly where the linear
  reply capability will bite first.
- **The erased phantom `Plain`/`Server` tag already shipped** — reuse it in the
  calculus; `call`/`cast`/`reply` are `Server`-only. See `lib/std/otp_raw.cure`
  (`RawPid(m, r, k)`, third arg the tag).
- **Totality + exhaustiveness are kernel-enforced** (proof soundness prerequisite):
  `lib/cure/core/certificate.ex` `terminating?/3`, `lib/cure/elab/guard_lint.ex`
  `prove_exhaustive/2`. A definition that does not certify total is *not* a valid
  proof — this is a feature.

---

## 5. The two obligations, stated precisely

Let `Req` be an inductive request vocabulary and `ReplyOf : Req -> Type` the
per-constructor reply assignment.

**Obligation (1) — linear `ReplyOf` preservation.**
> In a `call` handler serving request `req : Req`, the reply capability `cap` is a
> **linear** (grade-1) resource. A handler is well-typed only if it invokes
> `reply(cap, v)` with `v : ReplyOf(req)` **exactly once** on every path. Prove:
> reduction of a well-typed handler preserves typing, and the residual capability
> multiplicity is 0 (consumed) — no path drops or duplicates `cap`.

The novelty vs NVLang: `ReplyOf` **varies per constructor** (large elimination on
`req`), and the capability is **linear**. NVLang has neither (uniform reply, no
linearity). Special Delivery is the reply-typing oracle for the heterogeneous case.

**Obligation (2) — clause-derived pid index send-safety (F-1).**
> Let `derive : Handlers -> Req` extract the message vocabulary from an actor's
> handler clauses, and index its handle as `Pid(derive(handlers))`. Prove: if
> `send(p, m)` is well-typed then `m` is in `derive(handlers)`, i.e. the actor has
> a clause for it — a derived index is as safe as NVLang's annotated one.

NVLang gives you the annotated-index soundness recipe (`Extract-Msg`/`T-Spawn`);
the delta is proving it still holds when the index is *derived* rather than
*declared*.

---

## 6. First spike (write this, then run it, then report the roadblock)

Put a scratch module under `docs/research/process-types/spike/` (or a scratch dir)
— do **not** wire it into the stdlib preload until it typechecks. Goal: probe the
two capabilities most in question — (a) `ReplyOf : Req -> Type` large elimination
with a dependent return, and (b) linear consumption of the reply capability.

**Sketch — surface syntax is illustrative; reconcile against §4 exemplars:**

```cure
mod OtpAlgebraSpike
  # request vocabulary — three constructors with distinct reply types
  type Req = GetCount | SetName(String) | Ping

  # per-constructor reply type: LARGE ELIMINATION (cf. optic.cure:86, sigma.cure).
  # This is the crux of obligation (1) — a reply type that DEPENDS on the constructor.
  fn ReplyOf(r: Req) -> Type = match r
    GetCount()  -> Int
    SetName(_)  -> Atom      # :ok
    Ping()      -> Atom      # :pong

  # a handler must produce EXACTLY ReplyOf(req) — dependent return type indexed by
  # the argument (cf. sigma.cure:37's `-> b(sigma_first(p))`).
  fn handle(r: Req) -> ReplyOf(r) = match r
    GetCount()  -> 0
    SetName(_)  -> :ok
    Ping()      -> :pong
end
```

**What each line probes:**
- Does `fn ReplyOf(r: Req) -> Type = match r …` typecheck? (large elimination on a
  user ADT — very likely yes, `largeelim` cluster exists.)
- Does `fn handle(r: Req) -> ReplyOf(r)` accept branch bodies checked *against the
  computed type per branch*? (dependent return refined by the match — the real
  test.) If a branch body is checked against `ReplyOf(r)` **before** `r` is refined
  to the constructor, you have found roadblock #1 and it is a coverage/refinement
  gap → §8.
- **Then add the linear layer:** introduce a reply capability argument that must be
  consumed once, e.g. a grade-1 `cap`. This is where §8's deferred surface-grade
  syntax will most likely bite — that is *expected*, and the sanctioned response is
  to build the surface (Idris-aligned `1 x : T` multiplicity), not to route around.

Report: what typechecked, the exact error on the first thing that didn't, and which
capability it implicates. That report is the input to the capability-expansion spec.

---

## 7. The Idris oracle workflow (mirror as you go)

The differential oracle is already built and is your trust anchor.

- Clusters live under `test/oracle/<name>/` as paired `*.cure` + `*.idr` files
  (see `test/oracle/with/`, `test/oracle/largeelim/`, `test/oracle/rewrite/`, …).
- Run: `mix cure.oracle <cluster>` (live mode; **needs `idris2` on PATH**). It runs
  each `.cure` through Cure and each `.idr` through Idris and diffs verdicts; see
  `lib/mix/tasks/cure.oracle.ex`. A replay harness exists for offline checking.
- **Add an `otp` (or `replyof`) cluster**: mirror each core lemma as a `.cure`/`.idr`
  pair. Idris 2 is the natural twin — it has native QTT (`1 x : T` multiplicity) and
  `with … proof`, so the linear-reply lemma translates directly.
- **Concurrency rule:** only **one** full `mix test` / suite run at a time (a past
  concurrent full-suite run caused a kernel panic). `mix cure.oracle <cluster>` on a
  single cluster is fine; do not launch it alongside a full suite.

---

## 8. Known roadblocks and the expand-on-roadblock policy

Ranked by likelihood of being the *first* wall:

1. **Surface grades on λ-binders / constructor-fields are DEFERRED.** The kernel
   checks `{0,1,ω}` grades, but the *surface syntax* to declare "this reply
   capability argument is linear (grade 1)" may not be exposed. Obligation (1) needs
   exactly this. **Expected first roadblock.** Sanctioned fix: build the surface
   grade annotation, aligned with Idris 2's `1 x : T` multiplicity (Idris-aligned ⇒
   TCB change pre-approved; still run the full gate). Do **not** fake linearity with
   a runtime token.
2. **Dependent-match coverage on deeply-indexed scrutinees.** The "Lean-shape
   matching" algorithm (`2026-07-02-lean-shape-matching-design.md`) is a 7-phase
   spec, **not fully landed**. A preservation proof that needs a big nested dependent
   match may fail to certify total — and an uncertified total match **cannot** be
   trusted as a proof. This is the one spot where falling back to Idris-primary *for
   that specific lemma* is acceptable while the coverage gap is filed as its own
   expansion task. Recognize it by: a match that is manifestly exhaustive but
   `prove_exhaustive` reports `:not_proven`.
3. **Thin equational-reasoning combinators.** `cong` / `sym` / `trans` / chained
   reasoning may be missing. Cheap to add to `Std.Proof`; becomes reusable stdlib.
4. **No tactic automation.** Not a wall — metatheory here is explicit dependent
   matching (Agda-style), which Cure supports. Just drudgery.

For every roadblock: file a focused capability-expansion task (spec → plan if
non-trivial), verify Idris/Agda/Lean alignment for any TCB touch, and land it green
before resuming the proof.

---

## 9. Deliverables / definition of done

- [ ] Spike module typechecks (or a filed roadblock report if it doesn't) — §6.
- [ ] `lib/std/otp_proof.cure` (`Std.Otp.Proof`) — obligation (1) preservation
      lemma, kernel-checked, totality-certified. Update `raw_call`'s docstring at
      `lib/std/otp_raw.cure` to reference the discharged `ReplyOf`.
- [ ] Obligation (2) send-safety lemma (may be a second module / later milestone).
- [ ] `test/oracle/otp/` cluster — `.cure`/`.idr` mirrors of the core lemmas;
      `mix cure.oracle otp` green.
- [ ] Any capability-expansion landed with its own spec/plan + full gate green.
- [ ] Full suite green **once** at the end; Antigen coverage unregressed.
- [ ] A short findings note appended to
      `docs/research/process-types/2026-07-16-oracle-papers-synthesis.md` (or a new
      dated doc) recording what was proved and what each roadblock cost.

**Explicitly out of scope:** the macro plumbing (done); typestate/§9.5;
`gen_server:call` totality (`try_call` shim — separate); the `start_link` family's
`Effect(Tuple)` honesty; deadlock/liveness (runtime-monitor territory).

---

## 10. Guardrails

- **TCB = `lib/cure/core/**`.** TCB changes pre-approved *iff* aligned with Idris,
  Agda, or Lean (Idris-only suffices) — **still run the full gate**.
- **Author stdlib in `lib/std/`**, never `priv/std/` (that is a generated bundle).
- **Ghost-authored commits** — commits appear as the user only; never co-sign.
- **Explicit pathspec on every `git add`** (`git add -- <path>`) — never `-A`/`.`;
  another agent may share the tree. Work on your own branch.
- **One full suite run at a time** — never launch concurrent full `mix test` runs.
- **Idris oracle needs `idris2` on PATH** for live `mix cure.oracle`.

---

## Appendix — file map

| Path | What |
|------|------|
| `docs/research/process-types/raw-algebra-conformance-checklist.md` | The audit; F-1…F-5 definitions |
| `docs/research/process-types/2026-07-16-oracle-papers-synthesis.md` | Paper analyses (F-1, reply typing) |
| `docs/research/process-types/*.pdf` | The six papers (§3) |
| `lib/std/otp_raw.cure` | `raw_call` — the `ReplyOf(req)` hole; `RawPid(m,r,k)` phantom tag |
| `lib/std/actor.cure` | `derive_actor` / `derive_reply_contract` — the *landed* macro plumbing |
| `lib/std/proof.cure` | Worked inductive proofs — your template |
| `lib/std/equivalent.cure` | `Equivalent` propositional equality + `refl` |
| `lib/std/decision.cure` | `Decision(P)`, `Empty`, `Not(P)` |
| `lib/std/sigma.cure` | Σ types; dependent return-type exemplar |
| `lib/std/optic.cure` | `-> Type` large-elimination exemplar |
| `test/oracle/with/`, `test/oracle/largeelim/`, `test/oracle/rewrite/` | Oracle pattern to copy |
| `lib/mix/tasks/cure.oracle.ex` | The `mix cure.oracle` harness |
| `lib/cure/core/certificate.ex`, `lib/cure/elab/guard_lint.ex` | Totality + exhaustiveness checkers |
| `docs/superpowers/specs/2026-07-02-lean-shape-matching-design.md` | Dependent-match coverage (roadblock #2) |
