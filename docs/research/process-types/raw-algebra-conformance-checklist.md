# `Std.Otp.Raw` conformance checklist — against the Core Erlang formalisation

**Status:** open working checklist (not yet executed).
**Oracle:** Bereczky, Horpácsi & Thompson, *A Formalisation of Core Erlang, a
Concurrent Actor Language* (Acta Cybernetica 2023, arXiv 2311.10482) — a
Coq-machine-checked small-step (frame-stack) semantics of concurrent Core
Erlang, incl. messages, the ordered mailbox with selective receive, and the
signal layer (`link`/`unlink`/`exit`, `trap_exit`, signal ordering).
PDF: `core-erlang-formalisation-2311.10482.pdf` (this directory).

## Why this exists

Cure compiles to BEAM bytecode and runs on **any BEAM**: mainline Erlang/OTP is
the general target, AtomVM is one *capability-restricted embedding*. The typed
BEAM process algebra (`docs/superpowers/specs/2026-07-09-typed-beam-process-algebra-design.md`;
memory `typed-beam-process-algebra`) is a checked Cure surface (`Std.Otp`) that
*narrows* a sealed, permissive raw base (`lib/std/otp_raw.cure`). The narrowing
is only sound if the raw base's assumed contracts match what the BEAM actually
does. This paper is the reference semantics for that check on the general
target.

Two distinct products come out of running this checklist:

1. **Conformance** — does the typed narrowing assume anything the paper's
   semantics forbids? (ordering it doesn't guarantee, delivery it doesn't
   promise, a signal outcome it can't control.) Any "yes" is a soundness bug in
   the algebra, per the elaborator hard-stop principle.
2. **Capability profile** — for each guarantee the algebra relies on, is it
   *universal* (true on every BEAM) or *platform-gated* (real on OTP-BEAM,
   absent/partial on AtomVM)? This is the ledger that decides the open design
   fork: target full BEAM and treat AtomVM as a restricted profile, or target
   the intersection so everything runs everywhere. It does **not** gate undoing
   the §9.5 mailbox-typing deferral — that is gated on inference, separately.

## Scope caveat: what the paper does and does not govern

The paper formalises the **Core Erlang primitive layer**: `send` (`!`),
`receive`, `spawn`, `self`, `link`, `unlink`, `exit`, the `trap_exit` flag, and
the signal-ordering guarantee. It does **not** formalise the OTP *libraries*
(`gen_server`/`gen_statem`/`supervisor`), timers, the name registry, or
(verify) monitors — those are Erlang-level code built atop the primitives. So:

- For **PRIM** ops below, the paper is a *direct* oracle.
- For **OTP** ops, the paper is an *indirect* oracle only — it constrains the
  primitives the behaviour desugars to (spawn/link/monitor/send/receive), not
  the wrapper contract. Direct semantics for those come from the OTP Design
  Principles / `gen_server` docs, not this paper.

## The checklist

Legend — Layer: PRIM = Core-Erlang primitive (paper-direct) · OTP = library
(paper-indirect). Profile: U = expected universal · G = platform-gated, AtomVM
divergence likely · V = must verify.

| Raw op (`otp_raw.cure` → BIF) | Layer | Paper contract the typed layer must respect | Profile | Conformance question / action |
|---|---|---|---|---|
| `raw_self` → `erlang:self/0` | PRIM | Returns own pid; total, pure-ish. | U | Trivial; confirm `self` typing outside a behaviour context is sound (memory notes this is an open encoding). |
| `raw_send` → `erlang:send/2` | PRIM | **Async, fire-and-forget.** Never blocks; sending to a dead pid silently succeeds (message dropped). Ordering holds **only pairwise** (same sender→receiver), never globally. | U | Does typed `send` anywhere assume delivery, acknowledgement, or cross-sender ordering? It must not. |
| `raw_spawn` → `erlang:spawn/1` | PRIM | Creates a process; child may exit before parent observes it. | V | Surface raw `spawn` is E043; raw base uses it internally — fine. AtomVM: verify spawn/1 arity + fun-capture. |
| `raw_spawn_link` → `erlang:spawn_link/1` | PRIM | Link is established **atomically** with spawn — no window where the child can exit unlinked. | G | Typed wrapper must not emulate this as spawn-then-`link` (reintroduces the race). Verify AtomVM provides atomic spawn_link, not a two-step shim. |
| `raw_link` → `erlang:link/1` | PRIM | Bidirectional; establishes mutual exit propagation. | G | AtomVM link/exit-signal support is partial — **verify**. This is the crux of the profile fork. |
| `raw_unlink` → `erlang:unlink/1` | PRIM | Has *acknowledgement* semantics — an in-flight `exit` may still arrive after `unlink` returns; the link is not severed instantaneously. | G | Typed `unlink` must not promise immediate isolation. Verify AtomVM honours the flush/ack semantics (or document that it doesn't). |
| `raw_exit` → `erlang:exit/2` | PRIM | Sends an **exit signal**, not a guaranteed kill. Outcome depends on target `trap_exit`: (1) terminate, (2) drop (`normal` to another process), (3) convert to a `{'EXIT',From,Reason}` message at the **end** of the mailbox. Reason `kill` is **untrappable** (always terminates). | G | Typed `exit`/`stop` must not type-guarantee the target dies. Encode `kill` as the one untrappable case. Verify AtomVM's trap_exit conversion + `kill` handling. |
| *(missing)* `erlang:process_flag(trap_exit,_)` | PRIM | The flag that selects the exit-signal outcomes above. | G | **Deliberately absent** from the raw base (behaviours own the mailbox; no raw `receive`). Confirm this omission is intended and that no typed op silently needs it. |
| `raw_monitor` → `erlang:monitor/2` | PRIM? | Unidirectional; non-failing; delivers `{'DOWN',Ref,process,Pid,Reason}`. | V/G | Verify the paper's signal set covers monitors (or marks them future work). Verify AtomVM monitor support. |
| `raw_demonitor` → `erlang:demonitor/1` | PRIM? | Removes monitor; `flush` variant discards a pending `DOWN`. | V/G | As above; note the raw op omits the `flush` option — check whether typed layer needs it. |
| `raw_cast` → `gen_server:cast/2` | OTP | Async, no reply; desugars to a tagged `send`. Same delivery/ordering caveats as `raw_send`. | V | Indirect: inherits `send` contract. Verify AtomVM `gen_server:cast/2`. |
| `raw_call` → `gen_server:call/2` | OTP | **Synchronous** request-reply built on `send` + a one-shot monitor + selective `receive`; **can fail/time out** (default 5s), raising an exit in the caller. | V | The dependent `ReplyOf` typing must account for the failure/timeout mode — a `call` is not a total function. Verify AtomVM call/monitor path. |
| `raw_start_link` → `gen_server:start_link/3,4` | OTP | Returns `{ok,Pid}` \| `{error,_}` \| `ignore`; links to caller. | V/G | Works on AtomVM **with the exavmlib + `ets:whereis` patches** (CLAUDE.md). Note the patch dependency in the profile. |
| `raw_statem_start_link` → `gen_statem:start_link/3,4` | OTP | As above, gen_statem callback contract. | V/G | Same patch dependency; verify. |
| `raw_supervisor_start_link` → `supervisor:start_link/3` | OTP | Starts a supervision tree; restart semantics per child spec. | V/G | Verify AtomVM supervisor support + patch set. |
| `raw_stop` → `gen_server:stop/1` | OTP | Orderly termination via `terminate/2`; synchronous. | V | Verify AtomVM. |
| `raw_send_after` → `erlang:send_after/3` | OTP/BIF | Timer; delivers `msg` after `delay`; returns cancellable `Ref`. Not formalised by the paper. | V | Verify AtomVM timer support + resolution. Paper N/A. |
| `raw_cancel_timer` → `erlang:cancel_timer/1` | OTP/BIF | Cancels; may return remaining time or `false` if already fired. | V | Verify AtomVM. Paper N/A. |
| `raw_is_alive` → `erlang:is_process_alive/1` | PRIM/BIF | Point-in-time liveness; racy by construction. | V | Typed layer must treat the result as immediately stale. Verify AtomVM. |
| `raw_register` → `erlang:register/2` | BIF | Local name table entry. | G | CLAUDE.md flags Elixir `Registry` + `persistent_term` as **absent on AtomVM**; the basic `erlang:register`/`whereis` table may differ — **verify** and gate. Paper N/A. |
| `raw_unregister` → `erlang:unregister/1` | BIF | Removes name. | G | As above. |
| `raw_whereis` → `erlang:whereis/1` | BIF | Name→pid or `undefined`; the raw type `RawPid(m,m)` **asserts success** — a dynamic lookup that can fail. | G | Conformance flag: `raw_whereis` returns `RawPid` not an option; confirm the typed facade re-introduces the `undefined` case (memory names this the "name→protocol facade" open item). Verify AtomVM. |
| `raw_term` → `erlang:element/2` | BIF | Builds an erased `RawTerm` for heterogeneous OTP arg lists. | U | Not concurrency; the one sanctioned type-forgetting boundary. Confirm confinement. |

## Cross-cutting conformance questions (not per-op)

- **Ordered mailbox + selective receive.** The paper's mailbox is ordered by
  arrival with selective receive — on *every* BEAM, not an AtomVM quirk. The
  typed algebra governs the typed channels *sent*, not the raw mailbox (which
  the runtime also injects `EXIT`/`DOWN`/system messages into). Confirm no part
  of the algebra assumes a set-like (unordered) or exhaustively-typed mailbox.
  This is the fact that makes the §9.5 commutative-regex typestate model
  non-trivial to port (that theory is stated for *unordered* interactions).
- **Signal ordering guarantee.** Pairwise-ordered signal delivery is a property
  the paper proves for OTP-BEAM. If any typed guarantee leans on it, mark it
  **G** and verify AtomVM before relying on it.
- **`normal` vs abnormal exit reasons.** The three-way `trap_exit` outcome hinges
  on the reason being `normal`/`kill`/other. Any typed lifecycle story must
  carry the reason precisely, not collapse it to `Unit`.
- **Determinism/confluence results.** The paper proves side-effect-free
  evaluation is a bisimulation — relevant later to the `backend-decoupling`
  portable-process-effect interface, not to this conformance pass.

## What running this does *not* settle

- It does **not** justify undoing the §9.5 deferral of typestate/multiplicity/
  junk-freedom. Those are gated on an inference story for ordered/selective-
  receive mailboxes (Special Delivery names inference as the open problem), not
  on having this reference semantics.
- It does **not** call for a mechanised bisimulation proof relating `Std.Otp.Raw`
  to the paper's Coq development. That is a separate, much larger project; this
  checklist is a reading/audit pass over assumed contracts.
