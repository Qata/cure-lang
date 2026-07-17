# Preservation over Core Erlang — findings

*2026-07-16. `Std.Otp.Preservation` proves subject reduction for the Core Erlang
send/arrive/receive reduction, in Cure, kernel-checked and Idris-mirrored. This is the
first of the build-out map's G2 (typed-OTP preservation over a real reduction relation)
— the piece the exemplars-plus-negatives approach did NOT give.*

## What was proven

An extrinsic typed subject-reduction theorem over a faithful fragment of Bereczky–
Horpácsi–Thompson's Coq-checked concurrent Core Erlang semantics (arXiv 2311.10482):

- **Operational model** — one receiver's slice of the ether/mailbox: `Config =
  MkConfig(ether, mailbox)` (tag lists), and a small-step `Step` with the three rules
  that touch it: `SSend` (SEND+NSEND — a typed send puts an *accepted* tag in the
  ether), `SArrive` (NARRIVE — deliver front-of-ether into the mailbox), `SRecv`
  (RECEIVE — consume a mailbox message).
- **Typing** — `WT(c)`: every message in flight and in the mailbox is one the receiver
  *accepts*, where the accepted set is the inductive predicate `Accepted` (the
  receiver's clause-derived message type; here it accepts `Inc`/`Query` but not `Dec`).
- **Theorem** — `preservation : WT b -> Step b a -> WT a`, proven by cases on the step,
  shuffling the `AllAccepted` witnesses. Total ⇒ a genuine proof term.

**Significance.** NVLang states message-type safety (its Thm 4.1) but proves it over a
*toy single-actor step* with no ether. Here the same property is proven over the
*actual* ether→mailbox reduction. Safety content pinned by tests: the excluded `Dec`
is unaccepted (`Accepted(TDec)` uninhabited — absurd match), no `SSend` can put it in
flight, and no `WT` can hold it.

## Trust

- Kernel-checked + totality-certified in Cure (re-checked every build; stdlib preload).
- **Idris mirror** `test/oracle/otp/preservation.{cure,idr}` — `mix cure.oracle otp` is
  `rel=same` (both provers accept the identical proof). Frozen in oracle replay.
- Behavioural tests `test/cure/stdlib/otp_preservation_test.exs` (4): the proof + a
  non-vacuous config accept; a `TDec`-holding config and a `TDec` send both reject.

## Cure capability it exercised

The proof matches on `s : Step(b, a)` with `wt : WT(b)` in scope — the index refinement
from matching the indexed `Step` family must refine the sibling `wt`'s type. This is
exactly the indexed-scrutinee sibling refinement (validated earlier by `idx_scrut2`) and
the plain-`match` sibling routing (work-order item C). So the metatheory proof is real
dogfooding of the sibling-refinement work landed this session.

## Honest scope / what remains (build-out map G2)

- Single receiver; **mailbox order abstracted** (SArrive prepends — message-type safety
  is order-independent; a FIFO-faithful version adds one `AllAccepted`-over-append lemma
  and changes nothing about the invariant).
- Not modelled: exit/link/monitor signals, timers, multiple pids / interleaving, spawn.
- **Composed with obligation (1) for the reply TYPE — DONE.** `Std.Otp.ReplyPreservation`
  (`lib/std/otp_reply_preservation.cure`) strengthens the payload from a tag to a
  request-answering reply `(r, v)`, proves the same subject reduction over it, and adds
  the `reify : HasReply(r, v) -> ReplyOf(r)` bridge showing `HasReply` faithfully reflects
  obligation (1)'s large-elimination `ReplyOf` — so the dependent reply typing is carried
  through send/arrive/receive. Idris-mirrored (`test/oracle/otp/reply_preservation` +
  `reply_neg_wrong_reply`, rel=same); tests in `otp_reply_preservation_test.exs`. The
  remaining G1 piece is the LINEAR *capability*'s consumed-exactly-once as an operational
  conservation theorem over the relation (proven intrinsically via QTT today, not yet
  operationally).
