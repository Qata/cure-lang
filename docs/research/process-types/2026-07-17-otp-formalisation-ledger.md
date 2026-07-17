# OTP formalisation ledger — implemented vs remaining, toward FULL formalisation beyond the papers

*2026-07-17. Fine-grained status of the OTP process-algebra metatheory formalised in Cure.
"Beyond the papers" baseline: **NVLang** (typing plumbing, proof sketches, toy single-actor),
**Special Delivery / Proof of Delivery** (mailbox types, commutative, operational preservation
for the type language DEFERRED), **de'Liguoro–Padovani** (commutative-regex mailbox, paper
proofs), **KWC** (ordered signals + monitors, no types). Our delta: **mechanized, dependently +
linearly typed, operational preservation over the REAL reduction, tied to inference.***

---

## PART A — IMPLEMENTED (shipped in `lib/std/otp_*.cure`, each Idris `rel=same`)

### A1. Concurrent reduction + preservation / progress
- [x] Ether→mailbox concurrent reduction (Core Erlang, Bereczky–Horpácsi–Thompson 2311.10482) — `otp_preservation.cure`
- [x] Subject reduction (tag safety) over that real reduction — `preservation` *(beyond NVLang: its preservation is over a toy step)*
- [x] Progress + type safety: a well-typed config is final or steps to a well-typed config, never stuck — `otp_safety.cure` *(NVLang has no progress theorem)*
- [x] Multi-pid INTERLEAVING preservation (async; any one process steps, others fixed) — `otp_system.cure` *(beyond NVLang's single-actor step)*
- [x] Mailbox FIFO order (arrive=snoc/end, recv=front) + `AllAccepted`-over-append lemma — `otp_fifo.cure`

### A2. Obligation 1 — per-constructor HETEROGENEOUS + LINEAR dependent reply
- [x] `ReplyOf(req)` via large elimination (per-request reply type) — `otp_proof.cure`
- [x] Linear reply capability consumed EXACTLY ONCE (QTT grade + usage; drop/dup/one-branch-drop/launder all reject) — `otp_proof.cure`
- [x] Branching reply handler (per-branch reply), drop/dup rejected — oracle `ob1_branching*`
- [x] Reply preservation through delivery = COMPOSE G1×G2 (`HasReply(r,v)`, `reify` bridge) — `otp_reply_preservation.cure`
- [x] Reply CONSERVATION, operational exactly-once (drain: complete run `(n,Z)→(Z,m) ⟹ n≡m`) — `otp_reply_conservation.cure`

### A3. Obligation 2 — clause-DERIVED pid message index
- [x] `Pid(m)` carries its handler; index derived via `spawn_actor`; `post` dispatches — `otp_proof.cure`
- [x] Effect-honest `spawn_actor`/`post` returning `Effect(...)`, threaded by `effect_bind` — `otp_send_effect.cure` *(NVLang explicitly excludes effects §8.4)*

### A4. Monitors / links / signals (G3)
- [x] Typed monitor / DOWN-as-message (`MRef` carries `Accepted(TDown)`) — `otp_monitor.cure` *(NVLang: MonitorRef in grammar only)*
- [x] Typed links + `trap_exit` dispatch (message-vs-death on the flag) — `otp_link.cure`
- [x] Demonitor (`MRef` Active/Removed; DOWN-after-demonitor unconstructible) — `otp_demonitor.cure`
- [x] Unlink (`LinkRef` Linked/Unlinked; no exit signal after unlink, keeping trap dispatch) — `otp_unlink.cure`
- [x] Reason-dependent exit propagation (`Step` indexed by `Normal`/`Abnormal`/`Kill`; normal doesn't kill a non-trapper, kill is untrappable) — `otp_exit_signal.cure`

### A5. Timers (G4) — *no paper types timers*
- [x] `send_after` typed; `TimerRef` Pending/Cancelled; fire-after-cancel unconstructible; `receive after` branch — `otp_timer.cure`

### A6. `gen_server:call` failure/totality (G6) — *no paper types the timeout*
- [x] `CallOutcome(r) = Replied(r) | Failed(CallError)`; consumer ignoring `Failed` rejected non-total — `otp_call.cure`

### A7. Registry / naming (G7) — conformance F-2/F-2c
- [x] `GenServer(q,r)` wraps a `Pid` (bare `Pid` ≠ `GenServer`); `whereis → PidOption` partiality; ignoring `NoPid` rejected — `otp_registry.cure`

### A8. Selective receive (G8 slice)
- [x] ORDERED selective receive (front-to-back scan; order = inductive structure); `preserves` + `received_accepted` — `otp_selective_receive.cure` *(mailbox papers name ordered receive as future work)*

### A9. Routing / inter-process communication
- [x] Cross-process delivery (homogeneous), routing preserves global WT — `otp_routing.cure`
- [x] HETEROGENEOUS routing (per-process interfaces via `Member`/`AllMember`) — `otp_het_routing.cure`

### A10. Supervision (C4)
- [x] `Fleet(specs)` indexed by spec list; `restart_all`/`restart_one` return same specs (type certifies restart preserves declared children) — `otp_supervisor.cure` *(NVLang never ties restart to preservation)*

### A11. Mailbox type INFERENCE (G9) — *the universally-named open problem (OTP #5364)*
- [x] Decidable core: `tag_eq`, `decide_handles`, `decide_all_handled` (total, proof-carrying) — `otp_inference.cure`
- [x] Inference LAWS: monotonicity, weakening/subtyping-transitivity, principality (`self_member`) — `otp_inference_laws.cure`
- [x] ADEQUACY, sequential + branching (`BNil`/`BRecv`/`BSend`/`BSeq`): `preservation_at`, `coverage`, `adequacy` over runs — `otp_inference_adequacy.cure` *(the operational half Proof of Delivery deferred, tied to inference)*
- [x] Pre-fixpoint bound (`lfp_le`, principality direction of Knaster–Tarski) via monotone Kleene iteration — **SHIPPED** `otp_inference_fixpoint.cure` (Idris `rel=same`)

### A12. Cross-cutting
- [x] Exhaustiveness / dead-letter prevention (C8): kernel-certified totality + exhaustiveness on every proof term
- [x] 19/22 modules pure intrinsic (indexed types + total match, no `reflexive`/`rewrite`/`with`); 35 Idris oracle pairs `rel=same`

---

## PART B — REMAINING (fine-grained), toward FULL formalisation

### B1. Near-term, in-Cure provable (small or elaborator-gated)
- [x] `unlink` (demonitor-shape over `Link`, keeping the trap dispatch) — SHIPPED `otp_unlink.cure`
- [x] EXIT **reason axis** — reason-dependent dispatch (`normal`/`abnormal`/`kill`) in `otp_exit_signal.cure`. Still open: a full reason *term* as payload, and monitor-ref correlation on DOWN
- [x] Cascading exit-signal propagation across a link CHAIN — `otp_cascade_exit.cure` (`Cascade` relation + `run_cascade` totality: terminates, survivors = suffix from first trapper). Open: a general link GRAPH (fan-out) vs the chain slice
- [ ] **E1** sibling-context refinement on `match` (elaborator ergonomics — removes the data-first tax) — spec `2026-07-17-proof-authoring-elaborator-ergonomics-design.md`
- [ ] **E3 / task #15** cross-module resolution of implicit-carrying stdlib fns (lets proof lemmas factor across modules)
- [ ] **E4** partial-app codegen (eta-expand explicit-arg partial applications)

### B2. Recursion fixpoint — genuine in-Cure research (Knaster–Tarski / Kleene)
- [x] `BRec` behaviour representation (`RBody` with single recursion variable `RVar`) + syntax-derived transfer `tset(body, I)` + `infer(BRec) = rec_infer` — **SHIPPED** `otp_recursive_transfer.cure` (Idris `rel=same`)
- [x] transfer MONOTONICITY generic over syntax (`tset_mono`, induction on the body; `orb_mono`/`join_mono`/`setbit_mono`) — the hypothesis `map_lfp_le` needs — **SHIPPED** `otp_recursive_transfer.cure`
- [x] fixed-point property at a syntactic transfer (`rec_fixed = map_lfp_le(tset(body,-), tset_mono(body))`) — **SHIPPED** `otp_recursive_transfer.cure`
- [x] `lfp` construction via bounded Kleene iterate `iterate(f, ⊥, height)` — **SHIPPED** (`rec_infer = iter(tset(body,-), 4)`)
- [x] `?lfp_le` pre-fixpoint bound — **SHIPPED** `otp_inference_fixpoint.cure`
- [ ] `?le_lfp` (lfp below any upper bound of pre-fixed points)
- [x] **STABILIZATION**: `iterate(f, ⊥, |Tag|)` IS a fixed point — finite-height counting (interface size ≤ 3, strict-increase-or-fixed) — **SHIPPED** `otp_finite_fixpoint.cure` over the height-3 `IF` lattice (Idris `rel=same`). *The hard half, mathlib `monotone_chain_condition` port.*
- [x] `?map_lfp` (fixed-point property `f(lfp) ⊑ lfp`) — **SHIPPED** `map_lfp_le` in `otp_finite_fixpoint.cure`
- [x] `IF ↔ TagList` bridge (`denote`, `denote_complete`, `sub_allhandled`) — **SHIPPED** `otp_interface_bridge.cure` (Idris `rel=same`); transfers `map_lfp_le`'s `Sub` conclusion to `AllHandled` membership, so the finite fixpoint is usable in the adequacy representation
- [x] `?is_least` principality — `lfp_le` (Kleene pre-fixpoint bound over the `IF` lattice) + `rec_is_least` (the inferred interface is contained in every self-consistent interface; with `rec_fixed` it is the LEAST fixed point) — **SHIPPED** `otp_recursive_transfer.cure` (Idris `rel=same`)
- [x] BRec **coverage** — every direct send tag of a recursive behaviour is a member of its inferred fixed-point interface (`RSendsIn`, `tset_covers`, `brec_covers`), in both bit-set and membership (`brec_handles : Handles(t, denote(rec_infer(body)))`) form — **SHIPPED** `otp_recursive_adequacy.cure` (Idris `rel=same` on the `tset_covers` induction; the membership bridge reuses the oracle-verified `denote_complete` + `rec_fixed`). Canonical `Tag` now shared across `InterfaceBridge`/`RecursiveTransfer`/`RecursiveAdequacy`.
- [x] BRec **adequacy** proper — every config reachable by running a recursive behaviour is well-typed at `denote(rec_infer(body))` (`preservation_at` + `adequacy_at` + `rec_send_step` + `rec_adequacy`) — **SHIPPED** `otp_recursive_run.cure` (Idris `rel=same` on the operational core; `rec_send_step` justifies recursive sends via `brec_handles`). BRec inference is now operationally sound end to end for the finite universe: coverage (fundamental theorem) + preservation (operational closure).
- Scaffold: `scaffolds/inference_fixpoint.cure`; shape doc `2026-07-17-mailbox-inference-fixpoint-shape.md`

### B3. Counting / multiplicity fragment — commutative-regex mailbox types (Special Delivery, de'Liguoro–Padovani)
*(the tag-SET model does not reach this; it is a set, not a multiset with counts)*
- [ ] Mailbox types as COMMUTATIVE REGEX (patterns `𝟙`, `E+F`, `E·F` commutative, `*E`) — not flat tag sets
- [ ] Brzozowski derivatives for pattern matching
- [ ] Pattern SUBTYPING (inclusion) with multiplicities
- [ ] Conformance (`reliable`/`usable`, de'Liguoro–Padovani Def. 10)
- [ ] Bidirectional constraint GENERATION from a behaviour
- [ ] **Presburger / semilinear (Parikh) SOLVING** — external Z3/omega backend, **OUT OF TCB** (untrusted lint per the SMT trust-boundary decision), not a kernel proof
- [ ] Session-types-into-mailboxes encoding (C7; de'Liguoro–Padovani §4.3–4.4, fork/join)
- [ ] Evolving-protocol inference (accepted set changes over a conversation) — composes B2 fixpoint + this solving

### B4. Full ordered / protocol selective receive (rest of G8)
- [ ] Arbitrary PATTERN-DIRECTED selective receive with protocol-level ordering of a WHOLE conversation (current slice = single-tag ordered scan)

### B5. Signals semantics depth (KWC parity and beyond)
- [ ] Ordered OUTBOX-per-process with per-sender ordering (KWC's model; current = mailbox FIFO, not the outbox/signal-ordering model)
- [ ] link / monitor / exit modelled as SIGNALS with KWC ordering guarantees

### B6. Supervision depth
- [x] Restart INTENSITY bound (`max_restarts`) — `otp_restart_intensity.cure` (budget index; can't restart at zero). `max_seconds` window abstracted; bounded-run liveness theorem E6-blocked (probe)
- [x] Differential restart-SET semantics `one_for_one` / `one_for_all` / `rest_for_one` tied to preservation (NVLang Def. 4.2) — all three strategies in `otp_supervisor.cure`, each preserving `Fleet(specs)`, differing only in which children they revive
- [ ] Dynamic children / `simple_one_for_one`

### B7. Effects depth
- [ ] Full effect row/algebra for OTP ops (current = inert `Effect(T)` + `bind`); effect ordering; effect handlers

### B8. Full gen_server / gen_statem lifecycle
- [ ] Typed full callback protocol (`init`/`handle_call`/`handle_cast`/`handle_info`/`terminate`/`code_change`) as one state machine (current = call totality + reply typing, not the full lifecycle)
- [ ] `gen_statem` state-function typing

### B9. Out of scope (confirmed)
- Static DEADLOCK / LIVENESS — undecidable, a runtime result; a DDMon-style probe layer if ever wanted, orthogonal to the type system.

---

## "Beyond the papers" — the delta already achieved

| Property | Papers | Here |
|---|---|---|
| Operational preservation for mailbox-typed configs | Proof of Delivery DEFERS it | DONE (tag fragment), tied to inference |
| Mechanized | de'Liguoro–Padovani / NVLang = paper/sketch proofs | DONE, kernel-certified + Idris cross-checked |
| Dependent + LINEAR reply (`ReplyOf`, exactly-once) | none | DONE, intrinsic + operational |
| Progress + multi-pid interleaving | NVLang single-actor, no progress | DONE |
| Timers, call-totality, effect-honesty | no paper | DONE |
| Inference adequacy (infer ⇒ operational safety) | literature only STATES it | DONE, sequential + branching |
| Recursion fixpoint inference (`infer(BRec)` = least fixed point, operationally safe) | literature STATES the lfp exists; leaves coverage/adequacy for recursion open | DONE — syntax-derived transfer, finite Kleene stabilization, coverage, adequacy, principality, all kernel-certified + Idris cross-checked (finite universe) |

## Critical path to "FULL"
B2 (recursion fixpoint) is **COMPLETE** (transfer derivation → monotonicity → finite Kleene
stabilization → coverage → operational adequacy → principality; `otp_finite_fixpoint` /
`otp_interface_bridge` / `otp_recursive_transfer` / `otp_recursive_adequacy` / `otp_recursive_run`),
for the finite (bounded-tag) universe. B3 (counting fragment) is the largest remaining piece and is
partly EXTERNAL (Presburger/Z3). B5–B8 are depth/fidelity extensions. B1 is cleanup + ergonomics.
Everything in B1/B2/B4/B5/B6/B7/B8 is in-Cure provable; only B3's solver step sits outside the TCB.
