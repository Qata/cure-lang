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
  demonstrated in Cure as kernel-checked exemplars (`Std.Otp.Proof`); the reply
  *type* is now also carried through the reduction (G1×G2, see `Std.Otp.ReplyPreservation`
  below), AND the LINEAR *capability*'s consumed-exactly-once is now ALSO an operational
  conservation theorem over the relation — `Std.Otp.ReplyConservation`
  (`lib/std/otp_reply_conservation.cure`): the reply capabilities are a conserved resource,
  a single step preserves `pending + answered` (`step_conserves`, via `Std.Proof.plus_succ_right`),
  a whole run preserves it (`total_invariant`, induction over the reflexive-transitive closure
  `LStar`), and a COMPLETE run from `MkConfig(n, Z)` to `MkConfig(Z, m)` forces `n ≡ m`
  (`drain`) — every capability answered exactly once, none lost or duplicated. Plus the
  linearity guard `no_answer_without_cap` (no reply without a capability). Kernel-checked,
  Idris-mirrored (`test/oracle/otp/reply_conservation`, rel=same), tests in
  `otp_reply_conservation_test.exs`. This is the operational DUAL of `Std.Otp.Proof`'s
  intrinsic QTT-grade proof — so obligation (1) is now discharged both intrinsically and
  operationally. (It dogfoods the cross-module lemma-import fix landed the same session —
  `module_slice_env` now merges the auto-prelude, so `Std.Proof` lemmas are reusable across
  modules.)
- **G2. Preservation/progress of a TYPED OTP layer over the concurrent reduction
  relation.** Core Erlang gives the *untyped* relation; NVLang's preservation is over a
  *toy* single-actor step (no interleaving, no ether). Nobody has typed-OTP subject
  reduction over a real concurrent semantics. → **DONE (progress + preservation = type
  safety).** `Std.Otp.Preservation` (`lib/std/otp_preservation.cure`) proves SUBJECT
  REDUCTION for the send/arrive/receive fragment (single receiver, message-type safety) —
  the NVLang Thm 4.1 property over the *actual* ether→mailbox reduction, not a toy step.
  `Std.Otp.Safety` (`lib/std/otp_safety.cure`) adds PROGRESS — a well-typed config is
  never stuck (either final, or an arrive/receive step is available) — and combines the
  two into the canonical safety theorem `safety : (c) -> WT(c) -> Safe(c)` (a well-typed
  config is either final or steps to a WELL-TYPED config). Both kernel-checked, totality-
  certified, Idris-mirrored (`test/oracle/otp/preservation`, `.../safety`, rel=same); tests
  in `otp_preservation_test.exs`, `otp_safety_test.exs`. `safety` exercises plain-`match`
  sibling refinement — matching `c` refines the witness `wt` so `preservation(wt, step)`
  type-checks. **Multiple pids / interleaving now DONE — `Std.Otp.System`
  (`lib/std/otp_system.cure`):** a `System` is a pool of per-process `Config`s, a `SysStep`
  is ANY one process taking a step while the others stay fixed (asynchronous, no global
  lock), and `sys_preservation` proves GLOBAL well-typedness (every process well-typed) is
  preserved by any interleaved step — NVLang's toy single-actor step cannot state this.
  Idris-mirrored (`test/oracle/otp/system`, rel=same), tests in `otp_system_test.exs`.
  Exit/link/monitor signals are `Std.Otp.Monitor`/`Std.Otp.Link`. **Cross-process message
  delivery now DONE — `Std.Otp.Routing` (`lib/std/otp_routing.cure`):** `Deliver(before,
  after)` routes a message into SOME process's ether (`DeliverHere` head / `DeliverThere`
  deeper — the scan is the routing), REQUIRING `Accepted(t)` (a message may only be routed
  to a process that accepts it — the typed inter-process send). `deliver_preservation`
  proves routing preserves GLOBAL well-typedness, so a system of COMMUNICATING processes
  stays well-typed. Idris-mirrored (`test/oracle/otp/routing`, rel=same). **Mailbox FIFO
  order now DONE — `Std.Otp.Fifo` (`lib/std/otp_fifo.cure`):** `SArrive` appends to the
  mailbox END (FIFO) and `SRecv` consumes the FRONT; preservation is re-proved via the
  `all_accepted_snoc` lemma (appending an accepted message keeps the mailbox all-accepted)
  — exactly the `AllAccepted`-over-append lemma the order-abstracted modules deferred, now
  discharged once and for all. Idris-mirrored (`test/oracle/otp/fifo`, rel=same).
  **HETEROGENEOUS routing now DONE — `Std.Otp.HetRouting` (`lib/std/otp_het_routing.cure`):**
  each process carries its OWN accepted-set (interface); `WTProc` types its ether/mailbox
  against that set via a `Member`/`AllMember` predicate; `Deliver` requires `Member(t, set)`
  — `t` must be in the TARGET process's own interface — and `preservation` proves routing
  preserves global well-typedness even when every process speaks a different protocol. This
  is the interface-indexed core `Registry`'s `GenServer(q, r)` handles denote. Idris-mirrored
  (`test/oracle/otp/het_routing`, rel=same). The G2 concurrent-reduction line is now
  complete (interleaving + FIFO + homogeneous AND heterogeneous typed delivery). The
  composition with obligation (1) is **DONE for the reply TYPE** — see G1×G2 below.
- **G1×G2. COMPOSE: dependent reply typing preserved through delivery.** **DONE —
  `Std.Otp.ReplyPreservation` (`lib/std/otp_reply_preservation.cure`).** Strengthens G2's
  payload from a message *tag* to a request-answering *reply* `(r, v)` and proves
  `preservation : WT b -> Step b a -> WT a` where `WT` demands every in-flight/delivered
  reply is well-typed for its request (`HasReply(r, v)`). The `reify : HasReply(r, v) ->
  ReplyOf(r)` bridge shows `HasReply` faithfully reflects obligation (1)'s large-
  elimination `ReplyOf` — so preserving `HasReply` IS preserving the dependent `ReplyOf`
  typing through send/arrive/receive. Kernel-checked, totality-certified, Idris-mirrored
  (`test/oracle/otp/reply_preservation` + `reply_neg_wrong_reply`, rel=same); behavioural
  negatives in `test/cure/stdlib/otp_reply_preservation_test.exs`. **Honest remainder:**
  this carries the reply *type*; the LINEAR *capability*'s consumed-exactly-once is not
  yet an operational conservation theorem over the relation (a request-response
  conservation over a config of outstanding reply capabilities) — that is the last G1
  piece.
- **G3. Typed monitors / links / DOWN.** NVLang has `MonitorRef` in the grammar only
  (prose §2.5, no rules/theorems); Core Erlang omits monitors; KWC has the *operational*
  monitor model but untyped. → **DONE for monitors — `Std.Otp.Monitor`
  (`lib/std/otp_monitor.cure`).** The typing rule: a monitor reference is EVIDENCE its
  holder accepts `DOWN` (`MkMRef : Accepted(TDown) -> MRef`; `monitor_accepts` reads it
  back). The death step `SDown` delivers `DOWN` into the monitor's ether and requires an
  `MRef`, so `preservation` shows delivery preserves well-typedness — a monitor never
  gets a `DOWN` it cannot handle. Dually, a receiver whose vocabulary excludes `DOWN`
  cannot form an `MRef` (uninhabited `Accepted(TDown)`), so unmonitored processes are
  DOWN-safe by construction. Composes with `Std.Otp.Safety` (`SDown` is one more typed
  delivery rule). Kernel-checked, Idris-mirrored (`test/oracle/otp/monitor`, rel=same),
  tests in `otp_monitor_test.exs`. **Links DONE too — `Std.Otp.Link`
  (`lib/std/otp_link.cure`).** The bidirectional companion: on a linked peer's death the
  outcome is gated by the `trap_exit` flag — a TRAPPING process receives a well-typed
  `EXIT` message (`SExitTrap`, requiring `Accepted(TExit)` carried by `LinkTrap`), a
  NON-trapping process propagates to a terminal `Dead` state (`SExitProp`). `preservation`
  holds for BOTH outcomes — the novel content is the message-vs-death DISPATCH on the flag,
  neither branch reaching an ill-typed state. The step rules are gated to the correct flag
  (a wrong-flag step is unconstructible). Idris-mirrored (`test/oracle/otp/link`, rel=same),
  tests in `otp_link_test.exs`. **`demonitor` now DONE — `Std.Otp.Demonitor`
  (`lib/std/otp_demonitor.cure`):** an `MRef` is indexed by an `Active`/`Removed` lifecycle
  state, `demonitor` moves `Active → Removed`, and the death step `SDown` REQUIRES an
  `Active` monitor — so a DOWN delivered after `demonitor` is unconstructible (mirrors
  `Std.Otp.Timer`'s Pending/Cancelled discipline, completing the monitor lifecycle
  establish→observe→cancel). Idris-mirrored (`test/oracle/otp/demonitor`, rel=same); the
  parallel `unlink` over `Std.Otp.Link`'s trap-flagged link is the same shape. **Remaining
  in G3:** cascading-exit liveness, and the `DOWN`/`EXIT` reason/ref payload (abstracted to
  bare tags here).
- **G4. Timers / `send_after` / `receive after`.** **No paper** — KWC *explicitly*
  excludes timers, Core Erlang omits them, mailbox types list timeouts as future work.
  → **DONE — `Std.Otp.Timer` (`lib/std/otp_timer.cure`).** Two typing obligations: (1)
  `send_after` is a typed send — `MkTimer : Accepted(t) -> TimerRef(t, Pending)`, only an
  accepted message can be scheduled; (2) cancellation is observable in the type — a
  `TimerRef` is indexed by a `Pending`/`Cancelled` lifecycle state, `cancel` moves
  `Pending → Cancelled`, and `SFire` requires a `Pending` timer, so "fire after cancel" is
  UNCONSTRUCTIBLE. `preservation` shows a fired timer delivers an accepted message;
  `TTimeout` models the `receive ... after` branch. Kernel-checked, Idris-mirrored
  (`test/oracle/otp/timer`, rel=same), tests in `otp_timer_test.exs`. Delay/clock ordering
  abstracted (a fired timer is one that reached its deadline).
- **G5. Effect tracking for OTP ops.** NVLang *explicitly* excludes it (§8.4); Cure has
  `Effect(T)`. → **DONE for the send algebra — `Std.Otp.SendEffect`
  (`lib/std/otp_send_effect.cure`).** The effect-honest companion to obligation (2):
  `spawn_actor`/`post` return `Effect(Pid(m))`/`Effect(Response)` and the client threads
  them with monadic `let` (`effect_bind`). The point proven is that the clause-DERIVED
  message index survives the effect discipline — the bind refines the implicit `m := Msg`
  from the handler's domain, and the effectful `post` still forces `msg : Msg`. So
  send-safety is an invariant of the send, not of purity. Kernel-checked; Idris-mirrored
  with a user-defined `Eff` monad (`test/oracle/otp/ob2_eff_send_safe` +
  `ob2_eff_neg_wrong_msg`, rel=same); behavioural negatives in
  `test/cure/stdlib/otp_send_effect_test.exs`. (The wider typed OTP library `Std.Otp`
  already returns `Effect` for every op; this module isolates the *derived-index ×
  effect-bind* interaction as a metatheory result.)
- **G6. `gen_server:call` failure/totality.** No paper types the 5000 ms timeout /
  caller-`exit` failure mode; NVLang's `await` is total. → **DONE — `Std.Otp.Call`
  (`lib/std/otp_call.cure`).** A total call reifies its failure as a VALUE:
  `CallOutcome(r) = Replied(r) | Failed(CallError)` (`Timeout`/`NoProc`/`ServerDied`). The
  totality enforcement is the kernel's exhaustiveness check — `resume` matches both
  constructors, and a consumer that ignores `Failed` is REJECTED as non-total
  (`{:missing_branch, Failed}` in `otp_call_test.exs`). So "assume the call succeeded" is
  not expressible in a total program. A call typed as bare `r` would be unsound (it cannot
  always produce an `r`); `CallOutcome(r)` is the honest total type, and a
  `try_call : … -> Effect(CallOutcome(r))` on top of `Std.Otp.SendEffect` is the total
  wrapper. Idris-mirrored (`test/oracle/otp/call`, rel=same). **Supervision-restart now
  DONE — `Std.Otp.Supervisor` (`lib/std/otp_supervisor.cure`):** a `Fleet(specs)` is a
  supervisor's running children indexed by the whole spec list, and `restart_all`
  (one-for-all) / `restart_one` (one-for-one) return `Fleet(specs)` with the SAME `specs` —
  so the TYPE certifies the supervision invariant: a restart revives children but never
  changes what children the supervisor has. `establish : (specs) -> Fleet(specs)` says a
  running fleet of exactly the declared children always exists. Idris-mirrored
  (`test/oracle/otp/supervisor`, rel=same), tests pin that restart cannot reshape the spec
  list. Restart-intensity limits (max_restarts/max_seconds) are an operational bound not
  modelled.
- **G7. `Pid` vs `GenServer` separation + `whereis` partiality** (conformance F-2/F-2c).
  No paper; Cure's own audit. → **DONE — `Std.Otp.Registry` (`lib/std/otp_registry.cure`).**
  F-2: a `GenServer(q, r)` WRAPS a pid and carries its protocol; a bare `Pid` cannot be
  used where a `GenServer` is expected (`server_pid(MkPid)` fails to unify — a Pid is not a
  GenServer), and `expect_server` is the explicit protocol assertion (FFI trust boundary),
  not a silent identity. F-2c: `whereis` returns `PidOption` (`NoPid | SomePid`), never a
  bare `Pid`; consuming it (`with_pid`) must handle `NoPid` or fail totality certification.
  Idris-mirrored (`test/oracle/otp/registry`, rel=same), tests in `otp_registry_test.exs`
  (both the Pid≠GenServer and non-total-consumer negatives). `Pid` abstract, `q`/`r` phantom
  on the handle (the request-reply typing itself is `Std.Otp.Proof`/`Std.Otp.SendEffect`).
- **G8. ORDERED selective-receive typing.** Mailbox types are commutative; Erlang is
  ordered. Recovering order (position-indexed patterns) is *new type theory* both mailbox
  papers name as future work. → **SLICE DONE — `Std.Otp.SelectiveReceive`
  (`lib/std/otp_selective_receive.cure`).** `SelRecv(before, x, after)` types Erlang's
  front-to-back scan directly: `SelHere` (head is `x`, consume it) and `SelSkip` (head is
  another tag, keep it and recurse) ARE the arrival-order scan — order is the inductive
  structure of the receive, not abstracted. `preserves` (selective receive keeps the
  mailbox well-typed) and `received_accepted` (the received message is accepted) hold by
  induction on the scan; a receive of a tag absent from the mailbox is unconstructible.
  Idris-mirrored (`test/oracle/otp/selective_receive`, rel=same), tests in
  `otp_selective_receive_test.exs`. **Still open (the hard core):** arbitrary
  pattern-directed selective receive with protocol-level ordering of a whole conversation.
  This is the ordered-scan primitive that a full solution builds on.
- **G9. Mailbox type INFERENCE.** The **universally-named open problem** — Special
  Delivery, de'Liguoro–Padovani, and the OTP tooling literature all name inference as
  THE gap ("users must specify explicit patterns on each guard"). → **DECIDABLE CORE DONE
  — `Std.Otp.Inference` (`lib/std/otp_inference.cure`).** Two parts: (1) the interface is
  already DERIVED not annotated — `spawn_actor(handler)` infers `Pid(<handler domain>)` via
  the elaborator's metavariable solving, demonstrated in `otp_inference_test.exs`; (2) the
  metatheory that makes that trustworthy — mailbox membership is DECIDABLE: `decide_handles`
  (is a tag in the inferred interface?) and `decide_all_handled` (are all a process's
  self-sends handled? — the closure constraint) are TOTAL, proof-carrying decision
  procedures, built on decidable tag equality (`tag_eq`, from constructor disjointness).
  So the "is this message handled?" check the literature discharges by annotation is settled
  by an algorithm. Idris-mirrored (`test/oracle/otp/inference`, rel=same). **Still OPEN (the
  research core):** inference across an EVOLVING protocol (a session where the accepted set
  changes over a conversation) is constraint-solving over the whole behaviour, not a
  membership check; and GLOBAL interface inference from the system-wide send/receive graph.
  This slice is annotation-free mailbox typing for the FIRST-ORDER, finite-algebra, single-
  receiver case — the decidable foundation a full solution builds on. **Inference LAWS**
  (`Std.Otp.InferenceLaws`: monotonicity, weakening/subtyping, principality) and **ADEQUACY**
  (`Std.Otp.InferenceAdequacy`) are also proved: for SEQUENTIAL behaviours, the inferred
  interface is operationally SAFE — `adequacy : Runs(b, c) -> WTat(c, infer(b))`, i.e. every
  config reachable by running `b` is well-typed at `infer(b)` (the operational-preservation
  half Proof of Delivery deferred, tied to inference, Idris rel=same). The OPEN research core
  (evolving-protocol constraint solving; branching/recursion adequacy) is mapped to concrete
  fills in `2026-07-17-{mailbox-inference-fixpoint-shape,frontier-matching-shapes,adequacy-shape}.md`:
  mailbox types = commutative regex (mathlib `Computability/RegularExpressions`); solving =
  Presburger/semilinear (mathlib `ModelTheory/.../Presburger`, Lean `omega`); the recursion
  fixpoint (mathlib `Order/FixedPoints`+`OmegaCompletePartialOrder`); transfer monotonicity
  (Lean `Tactic/Monotonicity`); constraint gen (mbcheck); fundamental theorem (Actris logrel).
  Holed scaffolds in `scaffolds/`. Refs cloned to `~/Develop`.
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

## 5. NEW papers found — now PULLED IN (six of seven)

These surfaced during the arXiv verification. All but Mostrous–Vasconcelos are now in
`docs/research/process-types/` (Mostrous is Springer-paywalled; HAL serves only a JS
landing page). Ranked by relevance to actually building the metatheory.

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
