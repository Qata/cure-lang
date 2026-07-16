# OTP metatheory in Cure — build-out map (copyable vs. gaps), with arXiv verification

*2026-07-16. What the six process-types papers already formalise that Cure could
port ("just build it"), vs. the gaps no paper covers (Cure's to build). Each paper
was read in full and its identity/claims cross-checked on arXiv. Companion to
`raw-algebra-conformance-checklist.md` and `2026-07-16-oracle-papers-synthesis.md`.*

## 0. TL;DR

- **The operational substrate is copyable and Coq-checked.** Bereczky–Horpácsi–Thompson
  give an ether-based small-step semantics of concurrent Core Erlang with a swappable
  sequential layer — the exact reduction relation a Cure preservation/progress theorem
  would reduce over. This is the single biggest "just port it" item.
- **The typing *plumbing* is copyable but shallow.** NVLang gives `Pid[τ]`, `T-Send/
  Await/Spawn`, clause-derived message+reply extraction, and typed supervision trees —
  but as HM proof-*sketches* with a **Uniform-Reply** restriction (every constructor
  replies the same type) that is the *opposite* of what we want.
- **The mailbox discipline is copyable but commutative.** de'Liguoro–Padovani and
  Special Delivery give a QTT-aligned pattern/capability algebra with conformance +
  deadlock-freedom proofs — but the model is *unordered*; Erlang is *ordered/FIFO with
  selective receive*, which those papers name as future work.
- **The genuine gaps** — no paper formalises them for BEAM/OTP: per-constructor
  **heterogeneous + linear** dependent `ReplyOf`; **preservation of a typed OTP layer**
  over the concurrent reduction relation; typed **monitors/links/DOWN**; **timers**;
  **effect tracking**; `gen_server:call` **failure/totality**; **ordered** selective-
  receive typing; and mailbox **type inference** (the universally-named open problem).
- **Novelty verdict:** the *ingredients* are all published; the *combination*
  (dependent heterogeneous + linear reply on the BEAM, over a real reduction relation)
  is not. And Erlang's own maintainers acknowledge the core gap (OTP issue #5364).

---

## 1. The papers (verified on arXiv)

| Paper (local file) | Verified identity | Machine-checked? | Type system? | Op. semantics? |
|---|---|---|---|---|
| `core-erlang-formalisation-2311.10482` | Bereczky, Horpácsi, Thompson, *A Formalisation of Core Erlang*, Acta Cybernetica 2023 (arXiv 2311.10482) | **Yes — Coq** | No | **Yes** (ether, 3-layer small-step) |
| `nvlang-2512.05224` | de Oliveira Guerreiro, *NVLang: Unified Static Typing for Actor-Based Concurrency on the BEAM*, arXiv Dec 2025 | No (proof sketches) | **Yes** (HM+ADT) | Toy single-actor |
| `special-delivery-2306.12935` | Fowler, Attard, Sowul, Gay, Trinder, *Special Delivery: Programming with Mailbox Types*, **ICFP 2023** (arXiv 2306.12935) | Paper proofs (mechanised later: "Proof of Delivery", COORDINATION 2026) | **Yes** (mailbox, quasi-linear) | Yes |
| `mailbox-types-1801.04167` | de'Liguoro, Padovani, *Mailbox Types for Unordered Interactions*, **ECOOP 2018** (arXiv 1801.04167) | No (paper proofs) | **Yes** (mailbox, commutative-regex) | Yes |
| `kwc-signals-monitors-erlang2023` | Kong Win Chang, Feret, Gössler, *A Semantics of Core Erlang with Handling of Signals*, **Erlang Workshop 2023** (DOI 10.1145/3609022.3609417) | No (Maude in progress) | No | **Yes** (ordered outbox + monitors) |
| `deadlock-monitors-gen_server-2508.14851` | Rowicki, Francalanza, Scalas, *Correct Black-Box Monitors for Distributed Deadlock Detection*, **OOPSLA 2025** (arXiv 2508.14851) | **Yes — Coq** | No (**runtime**) | Yes (SRPC LTS) |

---

## 2. COPYABLE — formalisations we could port into Cure

Ordered by value. "Adaptation" = what changes moving to Cure's dependent/QTT setting.

### C1. The concurrent reduction relation — the preservation target ★
- **Source:** Core Erlang formalisation (2311.10482), Coq-checked.
- **Port:** the node `Σ = (Δ, Π)` with **ether Δ** (map from `(source,target)` pid pairs
  to signal lists), the process quintuple `(K, e, q, pl, flag)`, the signal/action
  grammar `Signal ::= msg | exit(v,b) | link | unlink`, the 3-layer relation (Figs 1–5:
  SEND/MSG/EXITDROP/EXITTERM/EXITCONV/LINK/UNLINK/SELF/SPAWN/RECEIVE/FLAG/TERM + inter-
  process NSEND/NARRIVE/NTERM/NSPAWN), and **Thm 2 (per-sender signal ordering)**.
- **Why:** this is the relation a Cure "well-typed OTP config stays well-typed" theorem
  reduces over. The **modular SEQ-lifting** lets us swap Fig. 1 for Cure's own typed
  core and reuse the concurrency layers unchanged — matches "expand Cure on roadblock."
- **Adaptation:** it is *untyped*; all typing/preservation is Cure's to add. `NSPAWN`
  founds pids on "any unused id" — the exact non-determinism the F-1 pid-index typing pins.

### C2. Typed `Pid[τ]` + actor-primitive typing triangle
- **Source:** NVLang §3.3.4, §3.7 (`T-Send`, `T-Await`, `T-Spawn`, `Pid[τ]`/`Future[τ]`,
  unification cases `U(Pid[τ],Pid[τ'])=U(τ,τ')`).
- **Port:** the skeleton for `actor`/`send`/`await` typing; `Pid` becomes an indexed
  family `Pid : MsgType -> Type`.
- **Adaptation:** drop the `Pid = Pid[Any]` escape hatch (unsound in a QTT kernel); give
  `Future[τ]` a **linear/affine grade** (NVLang's futures are unrestricted).

### C3. Clause-derived message + reply extraction (F-1's derivation)
- **Source:** NVLang §3.6 `ActorAnalysis(A) ⇒ (M,R)`, `Extract-Msg`, `ReplyExpr {Direct,
  Seq, Unit}`.
- **Port:** the elaboration pass that reads the message vocabulary and per-constructor
  reply from an actor's clauses. This *is* Cure's F-1 "derive the pid index from
  clauses," and it is largely already done in the `derive_actor`/`derive_reply_contract`
  macro plumbing.
- **Adaptation:** NVLang reads from a `receive msg : M` **annotation**; Cure derives from
  the clauses with no annotation (the small delta — see §4).

### C4. Typed supervision trees + restart algebra (great dogfooding)
- **Source:** NVLang Def. 4.2 (`R_one_for_one/all/rest_for_one` restart-set functions),
  Def. 4.3 (supervision tree), §4.5 crash-propagation rules.
- **Port:** simple *total* set-valued functions + a tree type — directly expressible as
  Cure total functions with a `children : List` and a restart-limit `Count(sup) < L`
  guard. (Note AtomVM supports only `one_for_one`/`one_for_all` — gate the codegen.)
- **Adaptation:** NVLang never ties restart semantics to a preservation theorem — the
  proof that a restarted child's state stays well-typed is a gap (§3, G6).

### C5. The mailbox pattern/capability algebra — QTT-aligned
- **Source:** de'Liguoro–Padovani (1801.04167) Table 2 (`𝟘/𝟙/m[τ]/E+F/E·F/E*`, `?E`/`!E`
  capabilities, coinductive subtyping Def. 9, combination `∥` Def. 16, `relevant/
  reliable/usable` Def. 10); Special Delivery (2306.12935) makes it an *algorithmic*
  system (Pat) with **quasi-linear** typing to tame aliasing.
- **Port:** the pattern algebra maps onto a grade semiring (`𝟙`≈0, `m·m`≈ω, `E*`≈ω, `!/?`
  ≈ linear/affine capabilities); `relevant/irrelevant` ≈ Cure's `{0,1,ω}` must-use/
  discardable; `T-NEW`'s `?𝟙` side condition ≈ a linear "mailbox fully drained"
  obligation; the `!reply[!reply[…]]` idiom (Ex. 2) ≈ the **one-shot typed reply
  channel**. Theorems 23–25 give conformance + deadlock-freedom + junk-freedom.
- **Adaptation — LOAD-BEARING:** the model is **commutative/unordered**; Erlang is
  **FIFO-ordered with selective receive**. It ports for tag-dispatched `gen_server`
  handlers (order-insensitive) but *cannot* express arrival-order-sensitive protocols.
  Recovering order = indexing the pattern by position = **new type theory** (see G8).

### C6. Ordered-mailbox + monitor operational model
- **Source:** KWC (Erlang 2023): outbox-per-process (no inbox) preserving per-sender
  FIFO via `first_sig/first_msg`; the MONITOR/SIG_MONITORED_BY/SIG_EXIT_MONITORED trio
  (monitor birth + DOWN-as-message); the EoP two-phase exit protocol (exactly-once exit
  emission); `Ref_L` monitor-reference identity (node,src,tgt,counter).
- **Port:** the *operational* model for ordered-mailbox and monitor/DOWN reasoning — the
  reduction relation a typed ordered-mailbox or typed-monitor discipline is sound
  against. `Ref_L` is a concrete scheme for per-monitor unique indices.
- **Adaptation:** untyped, unmechanised (Maude in progress); no `trap_exit` conversion
  (exit-via-link always kills here). Use for the *ordered* axis Core Erlang's ether and
  the commutative mailbox types both leave open.

### C7. Session-types-into-mailboxes encoding
- **Source:** de'Liguoro–Padovani §4.3–4.4 (binary sessions + fork/join encode into
  mailbox types via continuation-passing).
- **Port:** lets one Cure mailbox discipline subsume both actor and (encoded) session
  protocols; Thm 24 then yields session safety + progress as a corollary.

### C8. Exhaustiveness / dead-letter prevention
- **Source:** NVLang Thm 4.3 `Exhaustive(M,{p_i})`.
- **Port:** Cure *already has* a dependent exhaustiveness checker — reuse directly.

---

## 3. GAPS — no paper formalises these for BEAM/OTP; Cure builds them

- **G1. Per-constructor HETEROGENEOUS + LINEAR dependent `ReplyOf(req)`.** NVLang's
  **Uniform-Reply** forces one reply type per actor (must be *replaced*). Special
  Delivery types the heterogeneous case but with *quasi-linear*, not full QTT-dependent,
  and not indexed per request-constructor. Dependent session types (Toninho–Caires–
  Pfenning) do dependent messaging but for **π-calculus/linear channels**, not BEAM
  mailboxes/actors. → *This is obligation (1). The combination is the frontier.* Already
  demonstrated in Cure as kernel-checked exemplars (`Std.Otp.Proof`); a full
  **preservation proof** over C1's relation is still unbuilt (see G2).
- **G2. Preservation/progress of a TYPED OTP layer over the concurrent reduction
  relation.** Core Erlang gives the *untyped* relation; NVLang's preservation is over a
  *toy* single-actor step (no interleaving, no ether). Nobody has typed-OTP subject
  reduction over a real concurrent semantics. → Cure builds: state the typing invariant
  on `Σ=(Δ,Π)` and prove it preserved by Figs 2–5. Biggest *proof* undertaking.
- **G3. Typed monitors / links / DOWN.** NVLang has `MonitorRef` in the grammar only
  (prose §2.5, no rules/theorems); Core Erlang omits monitors; KWC has the *operational*
  monitor model but untyped. → Cure builds the typing + the DOWN-as-message discipline.
- **G4. Timers / `send_after` / `receive after`.** **No paper** — KWC *explicitly*
  excludes timers, Core Erlang omits them, mailbox types list timeouts as future work.
  → Discharge against OTP docs (and the live AtomVM `send_after` cancellation defect).
- **G5. Effect tracking for OTP ops.** NVLang *explicitly* excludes it (§8.4); Cure has
  `Effect(T)`. → Cure builds effect-honest OTP op types (this is work-order item G).
- **G6. `gen_server:call` failure/totality.** No paper types the 5000 ms timeout /
  caller-`exit` failure mode; NVLang's `await` is total. → Cure builds `Effect(Result(r,
  _))` / an exceptional index; supervision-restart tied to state preservation.
- **G7. `Pid` vs `GenServer` separation + `whereis` partiality** (conformance F-2/F-2c).
  No paper; Cure's own audit. → distinct opaque types; `whereis -> Option(Pid)`.
- **G8. ORDERED selective-receive typing.** Mailbox types are commutative; Erlang is
  ordered. Recovering order (position-indexed patterns) is *new type theory* both mailbox
  papers name as future work. → Cure builds if arrival-order-sensitive protocols matter.
- **G9. Mailbox type INFERENCE.** The **universally-named open problem** — Special
  Delivery, de'Liguoro–Padovani, and the OTP tooling literature all name inference as
  THE gap ("users must specify explicit patterns on each guard"). → Cure builds if it
  wants annotation-free mailbox typing.
- **Out of scope (confirmed):** static **deadlock/liveness** is a *runtime* result
  (deadlock paper explicitly rejects the static route as undecidable + needs whole
  source); if ever wanted it is a DDMon-style probe layer, orthogonal to the type system.

---

## 4. Novelty verification (arXiv + primary sources)

**The problem is acknowledged-open on the BEAM.** Erlang OTP issue **#5364** states
plainly that Erlang's type language "doesn't allow expressing the ways in which the
return of `call(ServerRef, Request) -> Reply` is dependent on callback implementations,"
and that extending the type language to relate behaviour and callback types "has been
proposed." So obligation (1)'s target is a *recognised, unsolved* BEAM gap.

**The ingredients are all published; the combination is not:**
- Typed pids / reply-from-interface: NVLang (`Pid[τ]`), CAF (C++), Akka Typed (Scala) —
  but **uniform reply**, not per-constructor dependent, and not on a dependent kernel.
- **Heterogeneous + LINEAR reply for actors: Special Delivery is the closest prior art.**
  A reply channel is a **fresh mailbox per call** with an **input (`?`) capability, which
  IS linear** — statically catching forgotten-reply and self-deadlock (their Thm 2). And
  **mailbox interfaces (§5.4)** make the reply payload heterogeneous per tag. So linear +
  heterogeneous reply for BEAM-style actors is *done*. What it is **not**: DEPENDENT —
  interfaces are **static finite tag→type maps**, not a type-level function over a request
  GADT. The delta obligation (1) actually adds is exactly "replace the static interface
  map with a dependent `ReplyOf(req)` indexed by the request constructor/value," on a
  native-QTT kernel (dropping Special Delivery's quasi-linear apparatus, which their own
  §2.1 says "is not an issue with a fully linear type system" — which Cure has).
- **Dependent + linear session types: also done, but for channels not actors.** TLLC
  (Fu, Xi, Das, Boston U, arXiv 2510.19129, Oct 2025) extends a two-level linear dependent
  type theory with Martin-Löf-dependent session types — verifying queues, map-reduce, by
  relating concurrent programs to sequential ones. Toninho–Caires–Pfenning likewise. But
  these are **intuitionistic session-typed CHANNELS (π-calculus lineage)**, not the BEAM's
  monolithic-mailbox actor request-reply. And **Idris 2** (Brady, ECOOP 2021) has QTT +
  linear + dependent + session types *in general*. So the *machinery* — dependent + linear
  concurrency typing — is thoroughly known-good; **nobody has applied it to the specific
  BEAM OTP `gen_server`-style per-constructor reply / clause-derived pid problem.**
- Clause-derivation of the message index: NVLang's `ActorAnalysis`/`Extract-Msg` already
  derives message+reply from clauses (reading a `receive msg:M` annotation). Cure's
  no-annotation derivation is a **small delta**, not a deep new result.

**So obligation (1)'s genuine, narrow delta is precise:** apply the *known* dependent+
linear concurrency machinery (TLLC/Idris-2-style) to the *known* actor request-reply
pattern (Special Delivery), replacing Special Delivery's **static interface map** with a
**dependent `ReplyOf(req)`** over the request GADT, on the **BEAM monolithic mailbox**.
That intersection is unpublished, but it is an *application/combination* of established
techniques — not a fundamentally new type theory.

**Honest verdict (unchanged from the earlier deflation):** what Cure built is a
kernel-checked *demonstration* that per-constructor heterogeneous + linear dependent
reply and a clause-derived pid index are *expressible and sound* in a QTT dependent
setting on the BEAM. That specific combination is under-explored (NVLang uniform-reply;
Special Delivery quasi-linear/commutative; dependent-session for π-calculus), and the
BEAM community treats the underlying problem as open (#5364). But: (a) it is a *demo /
type-rule soundness*, not a preservation theorem over C1's relation (G2); (b) "nobody
published this exact combination" needs the real lit review this doc begins, not a
blanket "solved an open problem" claim; (c) the derive-from-clauses part is essentially
NVLang minus one annotation.

---

## 5. NEW papers found (not in the repo) — get these

These surfaced during the arXiv verification and are NOT in `docs/research/`. Ranked by
relevance to actually building the metatheory.

1. **"Proof of Delivery: Mechanized Mailbox Types"** — Schiebelbein, Bieniusa, Fowler,
   **COORDINATION 2026** (simonjf.com/writing/proof-of-delivery.pdf). **Rocq/Coq
   mechanisation of Pat**; *identifies and corrects oversights in the original
   mailbox-type definitions*. ★ Get before porting C5/C6 — it is the fixed, machine-
   checked version of Special Delivery; the paper PDF we have is the unmechanised one.
2. **"Dependent Session Types for Verified Concurrent Programming" (TLLC)** — Fu, Xi, Das
   (Boston U), **arXiv 2510.19129**, Oct 2025. ★ The single most important novelty check:
   dependent + linear session types (Martin-Löf dependency over linear session channels),
   used to verify queues/map-reduce by relating concurrent↔sequential programs. Confirmed
   **channel/π-calculus-based, not BEAM actors** — so complementary, but its "novel
   formulation of intuitionistic session types" is exactly the dependent-session machinery
   an obligation-(1) preservation proof would mirror. Read it before writing G2.
3. **"An Introduction to Mailbox Types"** — Fowler, Gay, Padovani (Jan 2026 draft,
   simonjf.com/drafts/mb-behapi-draft-jan26.pdf). Survey distilling the mailbox-type line;
   good orientation for C5–C7.
4. **"An Erlang Implementation of Multiparty Session Actors"** — Fowler, ICE 2016
   (simonjf.com/writing/ice2016.pdf). Session types for *Erlang gen_server* — but via
   **runtime monitoring**, not static types. Confirms the "session-types-for-Erlang =
   runtime" pattern (like the deadlock paper); relevant scoping evidence, not a type-theory
   source.
5. **Mostrous & Vasconcelos**, session typing for *ordered* (featherweight) Erlang — the
   ordered counterpart to C5, relevant to G8 (weaker conformance, no deadlock-freedom).
6. **Toninho–Caires–Pfenning**, dependent session types via intuitionistic linear logic
   (PPDP 2011) + "Depending on Session-Typed Processes" (arXiv 1801.08114) — the origin of
   dependent session types; TLLC's lineage.

**Primary-source signal worth recording:** Erlang OTP issue **#5364** (github.com/erlang/
otp/issues/5364) is the maintainers acknowledging that the `gen_server:call`
request→reply dependency is inexpressible in Erlang's type language — direct evidence
the obligation-(1) gap is real and open on the BEAM.

## 6. Suggested sequencing (if building toward "full metatheory")

1. **Port C1** as `Std.Otp.Sem` (the untyped reduction relation) — the substrate.
2. **State the typing invariant + prove G2 preservation** for the send/receive/reply
   fragment first (obligation 1's rule *as a theorem over C1*, not just exemplars).
3. **Port C4** (supervision algebra) — cheap, high-confidence dogfooding.
4. **Do G5/G6** (effect honesty + call failure) — already work-order items.
5. **C6 + G3** (ordered mailbox + typed monitors) as one operational+typed slice.
6. Defer **G8/G9** (ordered selective-receive typing, inference) — genuinely new theory.
7. Never put **deadlock/liveness** in the type system — runtime-monitor territory.
