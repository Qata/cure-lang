# Mailbox-type inference (G9) — the decidable core, and what stays open

*2026-07-17. `Std.Otp.Inference` mechanizes the part of mailbox-type inference that can be
settled definitively, in Cure, kernel-checked and Idris-mirrored. This note is rigorously
honest about what is and isn't solved, because G9 is the open problem the whole field
names.*

## What G9 is

Every mailbox-typing system — Special Delivery (Pat), de'Liguoro–Padovani mailbox types,
the OTP tooling literature — names the same gap as future work: **the programmer must
annotate the accepted-message patterns**; the type is not inferred. "Mailbox-type
inference" is deriving each process's accepted-message set from how it is used.

## What is solved here

Two pieces, together = annotation-free mailbox typing for the first-order case.

**1. The interface is DERIVED, not annotated (elaborator, already shipping).** Cure's
obligation-(2) result (`Std.Otp.Proof`) infers the mailbox type from the handler:
`spawn_actor(handler)` returns `Pid(<handler domain>)`, the message type solved from the
handler by the elaborator's metavariables — no annotation. `otp_inference_test.exs`
demonstrates `post(spawn_actor(dispatch), msg)` type-checking with the message type `Msg`
never written down. This is exactly the annotation-free typing the papers call open, for a
single first-order handler.

**2. The metatheory that makes it trustworthy — membership is DECIDABLE.** An inferred
interface is only useful if you can decide, without annotation, whether a message belongs
to it. `Std.Otp.Inference` provides:
- `tag_eq : (a, b) -> Decision(a = b)` — decidable tag equality, from constructor
  disjointness (`Std.Decision`'s `impossible` discharge).
- `decide_handles : (t, iface) -> Decision(Handles(t, iface))` — a TOTAL, proof-carrying
  procedure: is `t` in the inferred interface? `Yes` carries a membership proof, `No` a
  disproof.
- `decide_all_handled : (sends, iface) -> Decision(AllHandled(sends, iface))` — decides the
  SELF-SEND CLOSURE: are all the tags a process sends to its own mailbox handled by its
  interface? This is the constraint that makes an inferred interface safe for a process
  that talks to itself.

All total and kernel-certified; the "is this message handled?" check the literature makes
the programmer discharge by annotation is settled by an algorithm. Idris-mirrored
(`metatheory/otp/oracle/otp/inference`, rel=same).

## What stays open (the research core)

- **Evolving-protocol inference.** When a process's accepted set CHANGES over a conversation
  (session/behavioural types), inference is a CONSTRAINT-SOLVING problem over the whole
  behaviour — generate constraints from every send/receive site and solve for the least
  interface at each program point — not a membership check. Not addressed here.
- **Global interface inference.** Deriving every process's interface from the system-wide
  send/receive graph (who can send what to whom) is a whole-program fixpoint. Not addressed.
- **Infinite / open message algebras.** `tag_eq` here is over a finite, closed tag type;
  decidable equality for open/parametric message types is a separate obligation.

This slice is the DECIDABLE FOUNDATION — annotation-free typing plus decidable membership
and self-send closure for the first-order, finite-algebra, single-receiver case — that a
full inference algorithm would build on. It does not close G9; it mechanizes the part that
is decidable and is honest about the constraint-solving core that remains.

## Incidental finding (codegen)

Building this surfaced a real BEAM-codegen gap: **partial application of an
explicit-argument function does not lower** — the elaborator eta-expands it for typing, but
codegen emits a direct call at the partial arity (`f/1` when only `f/2` exists), an
`erl_lint {:undefined_function, ...}`. Worked around here by lambda-wrapping the disproofs
(`No(fn(p) -> helper(closed_over, p))`), which lowers cleanly. The underlying codegen
eta-expansion for partial application is a separate fix (C-layer / `lib/cure/compiler`).
