# Oracle-paper synthesis — three new formalisations folded in

*2026-07-16. Folds NVLang, the OOPSLA-25 deadlock-monitor paper, and the
Erlang-2023 signals/monitors semantics into the conformance review begun in
`raw-algebra-conformance-checklist.md`. Read that checklist first; this document
only records what the three newly-downloaded papers change or confirm.*

The papers, and what each is:

| File | Venue / date | What it formalises | Machine-checked? |
|------|--------------|--------------------|------------------|
| `nvlang-2512.05224.pdf` | arXiv, Dec 2025 (de Oliveira Guerreiro, U. Lisbon) | A statically-typed functional BEAM language: ADT sum = message vocabulary, `Pid[τ]`, `Future[τ]`, HM inference, compiles to Core Erlang | No — proof *sketches* (Thms 3.1–3.4, 4.1–4.3) |
| `deadlock-monitors-gen_server-2508.14851.pdf` | OOPSLA 2025 (Rowicki, Francalanza, Scalas) | Distributed **black-box runtime monitors** for deadlock detection over RPC/gen_server systems; tool DDMon | Yes — sound + complete, mechanised |
| `kwc-signals-monitors-erlang2023.pdf` | Erlang 2023 (Kong Win Chang, Feret, Gössler) | Small-step semantics of a **subset of Core Erlang with signals + monitoring**, focused on **message order** | Small-step operational, hand-proved |

---

## 1. The headline correction to the checklist's §7 deferral

§7 of the conformance checklist deferred *both* mailbox papers (de'Liguoro/Padovani
Mailbox Types, Fowler et al. *Special Delivery*) on the grounds that their
commutative-regex mailbox is "unordered" whereas Erlang's mailbox is ordered, and
declared the ordered-mailbox axis unmodelled in the literature we held. **The
signals paper (KWC/Feret/Gössler) closes that gap directly.** Its stated focus is
"the **order** of messages"; it models signal handling and monitoring over a Core
Erlang subset. So the ordered-mailbox axis *is* formalised in the literature — we
simply didn't have the paper when §7 was written.

This sharpens, rather than reverses, the earlier self-correction:

- The commutative mailbox-*pattern discipline* (presence/exhaustion/multiplicity,
  typestate `?E`/`!E`) from Special Delivery abstracts away arrival order **on
  purpose**, and selective `receive` is exactly the construct that discipline
  types. That deferral was a category error and remains one.
- The *operational* ordered-mailbox semantics — needed if Cure ever wants to reason
  about receive-order-dependent behaviour or reorder-sensitive races — now has a
  concrete oracle: the KWC signals semantics. It is the missing operational model,
  not a missing type system.

**Caveat that keeps KWC from being a drop-in oracle for AtomVM:** its explicit
simplifications are *spawn never fails, **no timers** (no continuous time), no
nodes, no try-catch*. The "no timers" exclusion is pointed for us — the live
`send_after`/`cancel_timer` conformance defect (the F-series timer row) is exactly
the construct KWC declines to model. So KWC validates the ordered-signal/monitor
core but gives **no** cover for the timer algebra; that defect stays ours to
discharge against the OTP docs, not against a paper.

---

## 2. NVLang — the pragmatic proof-of-architecture, and its two ceilings

NVLang is the closest existing system to where `Std.Otp` is heading, and it ships
+ measures (~7.4–7.5% overhead). It **validates the architecture** Cure is
converging on: ADT sum type as the message vocabulary, typed `Pid[τ]`, typed
`Future[τ]` reply channel, complete type erasure to Core Erlang. That is a real
confidence signal — the shape is known-good.

But on the two questions the conformance audit actually cares about, NVLang stops
short of Cure's ambition:

### 2a. F-1 (pid index founded on nothing) — NVLang founds it, but by annotation

This is the important find. NVLang does **not** leave the message index free. Its
`T-Spawn` rule reads the message type off the *actor definition*: `spawn A() :
Pid[τm]` where `τm` is `A`'s declared message type, extracted (rule `Extract-Msg`)
from the **`receive msg : M` type annotation** the programmer writes and then
checked for exhaustiveness. So NVLang's founding mechanism is precisely the fix
F-1 needs — *tie the result `Pid`'s index to the callee's declared message type,
don't let the caller pick a free implicit* — but the message type is **declared by
annotation, not derived from handler clauses.**

Consequence for Cure: NVLang confirms the *soundness recipe* for F-1 but does **not**
solve Cure's stated F-1 goal. Cure wants `messages <Type>` to be *optional* —
derived from the handler clauses so the annotation can be dropped. NVLang's
`receive msg : M` **is** that annotation, mandatory. NVLang is therefore evidence
that the annotated version is sound and shippable, and evidence that clause
*derivation* (Cure's "Rung 2", gated on the macro facility) is genuinely beyond the
published state of the art — nobody has done it. Ship the annotated form first;
treat derivation as the research delta it is.

### 2b. F-2 (per-constructor reply typing) — NVLang's uniform-reply is strictly weaker

NVLang types replies with a **Uniform-Reply** constraint: *every* constructor of an
actor's message type must reply the **same** type `τr` (`send : Pid[τm] → τm →
Future[rtype(τm)]`, one `rtype` per actor). This sidesteps the multi-channel
`handle_call` problem rather than solving it. Cure's intended per-constructor
dependent `ReplyOf(msg)` — each request constructor carrying its own reply type — is
**strictly more expressive** than anything NVLang types. Special Delivery's
fresh-reply-mailbox-per-call is the richer model that actually types the
heterogeneous case. So on reply typing the ceiling remains Special Delivery, and
Cure's dependent `ReplyOf` ambition **exceeds** NVLang; NVLang is a floor, not a
target.

### 2c. What NVLang explicitly does NOT do

Its own limitations section rules out: mailbox typestate / multiplicity / exhaustion
/ ordering (it is the plain "ADT-sum" level — a `Pid[τ]` is a *set* of accepted
messages, nothing more); distributed properties (network partition, node failure,
cross-node conformance); and — flagged for us — **no effect tracking** (side effects
typed identically to pure computation). That last point is a direct contrast with
Cure's `Effect(T)` core: NVLang buys its clean HM inference precisely by *not*
having the effect discipline Cure already committed to. Confirms the two designs
are non-substitutable — NVLang is not "Cure minus dependent types," it's a
different, effect-blind point in the space.

---

## 3. Deadlock paper — vindicates deferring *static* deadlock-freedom

The OOPSLA-25 paper is a **runtime** result: black-box monitors deployed beside each
service that detect deadlock by observing messages + exchanging probes, proven sound
and complete, mechanised, with a working tool (DDMon) over real gen_server/OTP apps.
It is the strongest available treatment of the inter-process liveness axis §7 named
as confirmed-deferred.

The lesson for Cure is a scoping one, and it points *away* from the type system:
deadlock/liveness across a running process graph is handled in the literature by
**runtime monitoring**, not by the mailbox type discipline. This vindicates the
checklist's deferral of static deadlock-freedom as a type-system goal — the
state-of-the-art answer is external monitors, so Cure is not leaving an achievable
static guarantee on the table by omitting it. If Cure ever wants deadlock coverage
it is a runtime/observability feature (a DDMon-style probe layer), orthogonal to the
`Pid(m)`/`ReplyOf` typing work, and should not be smuggled into the type-system
roadmap.

---

## 4. Net effect on the defect ledger

Nothing in the three papers dislodges the F-1…F-5 defect list; they re-rank
confidence and sharpen scope:

- **F-1** — recipe confirmed sound by NVLang (found the index at spawn from the
  callee's declared message type). The *derivation* half stays a genuine research
  delta (unmatched in the literature), correctly gated behind the macro facility.
  Land the annotated form with confidence.
- **F-2** — Cure's per-constructor `ReplyOf` is above NVLang's uniform-reply ceiling;
  Special Delivery remains the oracle for the heterogeneous-reply case. Do not
  regress `Std.Otp` to uniform reply to match NVLang.
- **Timer defect (`send_after`/`cancel_timer`)** — *no* paper cover; KWC explicitly
  excludes timers. Discharge against OTP docs.
- **Monitors/signals conformance rows** (previously "paper silent") — now have an
  operational oracle in KWC; use it to check `monitor`/`demonitor`/`DOWN`/`exit`
  signal-order behaviour.
- **Deadlock / inter-process liveness** — confirmed out of the type-system scope;
  runtime-monitor territory if ever wanted.

## 5. One correction carried over from the metaprogramming review

Unchanged by these three papers but recorded here so the process-types and macro
tracks stay consistent: the SP5.3 plan's "set-of-scopes hygiene" must deliver **both**
capture-avoidance *and* referential transparency (def-site global resolution). The
`Timer.repeat(500)` → `:unknown_global` symptom is the referential-transparency half,
currently misfiled as SP2 import plumbing. That belongs to the macro-facility
program, not this ledger — flagged only to prevent the two reviews drifting apart.
