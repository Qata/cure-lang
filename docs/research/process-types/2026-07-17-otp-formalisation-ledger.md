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
- [x] Mailbox types as COMMUTATIVE REGEX (patterns `PZero`/`POne`/`PAtom`/`PPlus`/`PTimes`/`PStar`) over MULTISETS (Parikh vectors `MkMS(Nat,Nat,Nat)`), with the `Accepts` relation and the COMMUTATIVE-MONOID laws of `(Pat, PTimes, POne)`: `times_comm` (`E·F ≡ F·E`), `times_assoc`, `one_times` (unit), plus `plus_comm` (choice) — all via `msadd` arithmetic (`msadd_comm`/`msadd_assoc`/`msadd_zero_left` over Nat `plus_comm`/`plus_assoc`) — **SHIPPED** `otp_mailbox_pattern.cure` (Idris `rel=same`). The counting model the tag-set inference cannot express.
- [~] Brzozowski derivatives for pattern matching: `nullable` + `nullable_sound`; the commutative `deriv(E,t)` and **`deriv_sound`** — the SOUNDNESS half of the fundamental theorem, `Accepts(deriv(E,t), m) → Accepts(E, m ⊎ {t})` — proved for the full pattern algebra incl. `PStar` (constructive; relocates the peeled `{t}` with the bag-algebra laws) — **SHIPPED** `otp_mailbox_pattern.cure` (Idris `rel=same`). REMAINING: the CONVERSE (`deriv_complete`) and `nullable_complete` both need `msadd` zero/one INVERSION, blocked by a Cure elaborator gap (stuck-index equation not retained on GADT match; and sequential-match refinement — see below).
  - **Elaborator parity gaps found (cataloged for the ergonomics spec):** (1) matching an `ATimes`-style ctor whose index is a stuck function-app (`msadd(m1,m2)`) does not retain the index equation `m = msadd(m1,m2)` as a usable proof — blocks any inversion. (2) SEQUENTIAL-MATCH refinement: `match pat` then a separate `match acc → … → ATimes` does not propagate the second match's index refinement into the goal the first match already specialized (Idris matches all patterns simultaneously per clause; Cure's `match` is independent per scrutinee). WORKAROUND for (2): helper-delegation — match the evidence as a function PARAMETER (no prior data-match freezing the goal). Used in `deriv_sound`'s `ds_times`/`ds_star`.
- [x] KLEENE STAR FIXPOINT LAW `*E ≡ 𝟙 ⊕ E·(*E)` (`star_unfold`/`star_fold`, both directions, pure constructor rearrangement) — **SHIPPED** `otp_mailbox_pattern.cure` (Idris `rel=same`).
- [x] SEMIRING left-DISTRIBUTIVITY `E·(F⊕G) ≡ (E·F)⊕(E·G)` (`dist_fwd`/`dist_bwd`, both directions) — **SHIPPED** `otp_mailbox_pattern.cure` (Idris `rel=same`).
- [x] ADDITIVE monoid + ANNIHILATOR: `⊕` associative (`plus_assoc_fwd`/`bwd`) with unit `PZero` (`plus_zero_fwd`/`bwd`), and `PZero` absorbs `·` (`zero_times`) — `(Pat, ⊕, 𝟎, ·, 𝟙, *)` is a commutative KLEENE ALGEBRA up to acceptance — **SHIPPED** `otp_mailbox_pattern.cure` (Idris `rel=same`).
- [x] Pattern SUBTYPING (inclusion): inductive `Incl(E,F)` (refl, `𝟎`-least, choice lub/injections, `·`/`*` monotone, transitive) + `incl_sound` (implies semantic inclusion — a mailbox typed `E` is usable where `F` is expected) — **SHIPPED** `otp_mailbox_pattern.cure` (Idris `rel=same`). Note: this is the SOUND syntactic subtyping; the DECISION procedure for semantic inclusion needs the Presburger solver (out of TCB).
- [x] Derivative MONOTONICITY under subtyping (`deriv_mono : Incl(E,F) → Incl(deriv(E,t), deriv(F,t))`, pure `Incl` recursion) — **SHIPPED** `otp_mailbox_pattern.cure` (Idris `rel=same`).
- [x] BRZOZOWSKI MATCHING (operational membership decision): `dfold` folds the derivative along a message `Word`, matching = residual `nullable`; `matches_word_sound` proves it sound (`nullable(dfold(E,w))=T ⟹ Accepts(E, parikh(w))`) — **SHIPPED** `otp_mailbox_pattern.cure` (Idris `rel=same`). The operational use of the derivative; completeness is E9-blocked.
- [ ] Conformance (`reliable`/`usable`, de'Liguoro–Padovani Def. 10)
- [ ] Bidirectional constraint GENERATION from a behaviour
- [ ] **Presburger / semilinear (Parikh) SOLVING** — external Z3/omega backend, **OUT OF TCB** (untrusted lint per the SMT trust-boundary decision), not a kernel proof
- [~] Session-types-into-mailboxes encoding (de'Liguoro–Padovani §4.3–4.4): binary session types + DUALITY foundation — `dual`, `dual_involution` (dual is an involution), `Compat` + `compat_dual` (compatible endpoints are exactly dual endpoints, i.e. communication safety = duality) — **SHIPPED** `otp_session.cure` (Idris `rel=same`). plus `SStep` + `session_preservation` (subject reduction: a communication step between compatible endpoints yields compatible endpoints — a safe session stays safe as it runs). Plus `SRun` + `session_run_safe` (safety over a WHOLE run: a session from compatible endpoints stays compatible through every step — never gets stuck on a type mismatch). Plus `Progress` + `session_progress` (PROGRESS: a compatible pair is either finished (`SEnd`/`SEnd`) or a communication redex — a well-typed session never deadlocks; with preservation this is full type safety, well-typed ⟹ never stuck). Plus `compat_terminates` (NORMALISATION: every compatible finite session runs all the way to `(SEnd, SEnd)` — an explicit full `SRun` built by structural induction; packages progress + preservation + termination, so a well-typed session never deadlocks, never mistypes, and always terminates). The construction uses the explicit-`tail` pattern to pin `SRStep`'s floating target indices past the E6-residual construction-position gap (documented in the ergonomics spec). Plus RECURSIVE session types (`Std.Otp.RecursiveSession`): `RSType` with `μX`/`RVar`, `subst`/`unfold`/`rdual`; `rdual_involution`, `subst_dual` (dual distributes over substitution), and the headline `dual_unfold_commute` (`dual(unfold(μX.S)) = unfold(μX.dual(S))` — a looping protocol's endpoints stay dual across every unfolding); generalized to `rdual_unfold` (`dual(unfold(S)) = unfold(dual(S))` for EVERY shape, of which `dual_unfold_commute` is the `RMu` instance). Plus MULTIPARTY session types (`Std.Otp.MultipartySession`): `Global` protocol type + `project(G, role)` to per-role `Local` types; `projection_duality` proves COHERENCE (a two-party global projects to DUAL endpoints — global well-formedness yields local communication safety, Honda–Yoshida–Carbone). Plus `GStep` + `twoparty_preserved` (GLOBAL SUBJECT REDUCTION: firing the head interaction of a well-formed two-party protocol yields a well-formed two-party protocol — so with `projection_duality` the projected endpoints stay coherent through every step of the protocol's execution). Plus `GProgress` + `global_progress` (GLOBAL PROGRESS: a well-formed two-party protocol is either finished or its head can fire — never deadlocks; with `twoparty_preserved` this is full safety for the global protocol). Plus the SESSION→MAILBOX ENCODING (`Std.Otp.SessionMailbox`, the de'Liguoro–Padovani headline): an endpoint is realized as a process with a MAILBOX = the commutative multiset (`MS`) of tags it receives; `recvs`/`sends` measure the received/emitted multisets, and `recvs_dual` proves ENCODING FIDELITY — `recvs(dual(L)) = sends(L)`, the mailbox an endpoint must service is exactly what its dual peer sends (with the mirror `sends_dual`), so the encoding preserves communication safety. Plus FORK/JOIN (parallel session composition `LPar`): an endpoint may run two independent sub-sessions in parallel, whose mailbox is the multiset SUM (`msum`) of the components'; `recvs`/`sends`/`dual` extend componentwise and fidelity (`recvs_dual`/`sends_dual`) still holds via `msum_cong` — so parallel composition preserves the encoding's communication safety. Open: >2-role multiparty coherence
- [ ] Evolving-protocol inference (accepted set changes over a conversation) — composes B2 fixpoint + this solving

### B4. Full ordered / protocol selective receive (rest of G8)
- [x] PATTERN-DIRECTED selective receive (a pattern = a set of acceptable tags, generalizing the single-tag scan): `SelRecv(set, before, got, after)` with `selrecv_matches` (received message matches the pattern) + `selrecv_present` (it was actually in the mailbox) — **SHIPPED** `otp_pattern_receive.cure` (Idris `rel=same`). **DONE**: whole-conversation protocol-level ordering — `Std.Otp.Conversation`: `ConvRecv` runs a `Protocol` (sequence of expected tags) over a mailbox via per-step selective receive; `conv_order` proves the received conversation equals the protocol's tag sequence regardless of the mailbox's arrival order (a protocol-directed client always receives in protocol order). Idris `rel=same`

### B5. Signals semantics depth (KWC parity and beyond)
- [x] PER-SENDER signal ordering (KWC's pairwise guarantee): a mailbox is an `Interleave` of per-sender streams; `proj_left`/`proj_right` prove projecting to a sender recovers exactly that sender's stream in order — each sender's signals stay FIFO regardless of the interleaving — **SHIPPED** `otp_signal_order.cure` (Idris `rel=same`). Refines the single global mailbox-FIFO model to Erlang's actual pairwise ordering.
- [ ] link / monitor / exit modelled as SIGNALS with KWC ordering guarantees

### B6. Supervision depth
- [x] Restart INTENSITY bound (`max_restarts`) — `otp_restart_intensity.cure` (budget index; can't restart at zero). `max_seconds` window abstracted; bounded-run liveness theorem E6-blocked (probe)
- [x] Differential restart-SET semantics `one_for_one` / `one_for_all` / `rest_for_one` tied to preservation (NVLang Def. 4.2) — all three strategies in `otp_supervisor.cure`, each preserving `Fleet(specs)`, differing only in which children they revive
- [x] Dynamic children / `simple_one_for_one`: `Pool(spec)` indexed by a SINGLE spec (not a list) certifies UNIFORM children; `start_child`/`terminate_child` vary the pool at runtime, `restart_pool` preserves spec + size — **SHIPPED** `otp_supervisor.cure` (Idris `rel=same`)

### B7. Effects depth
- [x] Effect ALGEBRA + LAWS: OTP message ops carry no result, so effect programs form a MONOID under sequential composition (`seq` = append) — `seq_nil_l`/`seq_nil_r`/`seq_assoc` certify `(Eff, seq, ENil)` is a monoid, the reassociation/unit-simplification an effect handler relies on — **SHIPPED** `otp_eff_algebra.cure` (Idris `rel=same`). effect HANDLERS: a handler interprets the algebra and its correctness is a MONOID HOMOMORPHISM — `count_sends` (a send-counting handler into `(Nat,plus,0)`) + `count_hom` (`handle(a;b) = handle(a)+handle(b)`) — **SHIPPED** `otp_eff_algebra.cure` (Idris `rel=same`). Open: a value-returning free-monad `bind` (higher-order reduction in an index position, E10) + effect ROW/multiple-handler composition

### B8. Full gen_server / gen_statem lifecycle
- [x] Typed CALLBACK LIFECYCLE as a phase state machine — `Std.Otp.Lifecycle`: `Callback` = typed phase transition (init `PInit→PRunning`, handle_* keep `PRunning`, stop `→PTerminated`, terminate final); `Lifecycle` = well-formed callback sequence. Proves `init_only` (init is the only first callback), `nothing_reinits` (no callback returns to `PInit`), `terminated_absorbing` + `no_resurrection` (a terminated server stays terminated). **SHIPPED** `otp_lifecycle.cure` (Idris `rel=same`). Open: `code_change` version transitions; per-callback message/reply typing threaded through (the `Std.Otp.Proof`/`Std.Otp.Call` layer)
- [x] `gen_statem` EVENT POSTPONING: `SStep` (handle/postpone/redeliver) with per-move conservation of the unprocessed count — `handle_progresses` (only handling advances), `postpone_conserves`/`redeliver_conserves` (deferring/redelivering relocate an event, never drop it) — **SHIPPED** `otp_gen_statem.cure` (Idris `rel=same`). *No paper types postpone; this is gen_statem's defining feature.* Open: full state-function callback protocol

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
