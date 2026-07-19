# Gleam OTP ↔ Cure OTP parity audit (2026-07-19)

Source-of-truth: the actual Gleam sources cloned to `~/Develop/gleam-otp` (`gleam_otp` **1.2.0**) and
`~/Develop/gleam-erlang` (`gleam_erlang` **1.3.0**). Goal: confirm Cure has every capability Gleam's OTP
abstractions provide, at **equivalent or greater ergonomics**.

## Verdict

Cure **matches or exceeds** Gleam on the *semantic* axis — typed call/reply, supervision, monitors, links,
timers, and far beyond (dependent per-request reply types, total call-failure, session types, an effect
discipline, kernel-checked metatheory). The gaps are all on the **ergonomic surface / addressing model**, where
Gleam has three ideas Cure lacks as *usable* APIs:

1. **`Subject(message)`** — a typed message *address* decoupled from the pid; a process owns *many*.
2. **`Selector`** — a usable, composable typed selective-receive API over heterogeneous subjects.
3. **`Name(message)`** — typed process registration + take-over (Cure's deferred **F-1**).

Everything else is at parity or Cure-favoured. Details below.

## Gleam's OTP surface (from source)

### `gleam/erlang/process` — the foundation
- **`Pid`**, `self`, `spawn(fn)`, `spawn_unlinked`, `is_alive`, `kill`, `send_exit`, `send_abnormal_exit`, `link`, `unlink`, `trap_exits`.
- **`Subject(message)`** = `Subject(owner: Pid, tag: Dynamic)` | `NamedSubject(Name)`. A typed address: a unique `tag` (a ref) scopes messages so ONE process can own MANY subjects of different types. `new_subject()`, `send(subject, msg)`, `receive(subject, timeout) -> Result(msg, Nil)`, `receive_forever`. Receiving is owner-only (panics otherwise).
- **`Name(message)`** — a typed, globally-unique registration identity (an atom). `new_name(prefix)`, `named_subject(name)`, `register(pid, name)`, `unregister`, `named(name) -> Result(Pid, Nil)`. Enables top-down wiring and transparent take-over (a new process adopts a failed one's name).
- **`Selector(payload)`** — typed selective receive across heterogeneous subjects mapped into one `payload`: `new_selector`, `select(sel, subject)`, `select_map(sel, subject, transform)`, `map_selector`, `merge_selector`, `deselect`, `selector_receive(sel, timeout)`, `selector_receive_forever`. Plus `select_record` (raw tagged tuples from other BEAM langs), `select_other` (catch-all), `select_trapped_exits`, `select_monitors`.
- **`call(subject, timeout, make_request: fn(Subject(reply)) -> message) -> reply`** — synchronous call. **The reply type rides in the request constructor's reply-`Subject` field, inferred per request** (`SayHello(reply, name)` → `reply : Subject(String)`). `call_forever`. Crash-on-timeout (panics; not a `Result`).
- **Monitors**: `monitor(pid) -> Monitor`, `Down`, `select_monitors`, `demonitor_process`. **Timers**: `send_after(subject, delay, msg) -> Timer`, `cancel_timer -> Cancelled`. `sleep`, `flush_messages`.

### `gleam/otp/actor` — the typed actor (builder API)
- `new(state) -> Builder(state, message, Subject(message))`, `on_message(builder, fn(state, message) -> Next)`, `named(builder, name)`, `new_with_initialiser(timeout, fn(Subject) -> Result(Initialised, String))`, `start(builder) -> Result(Started(data), StartError)`.
- **`Next(state, message)`**: `continue(state)`, `stop()`, `stop_abnormal(reason)`, **`with_selector(next, selector)`** — the loop can SWAP the selector at runtime, changing which messages it handles next (dynamic protocol).
- `Initialised` init can return a custom selector (`selecting`) and a custom parent-return value (`returning`).
- Actors process messages sequentially; `call`/`send` re-exported.

### Supervision
- **`supervision`**: `ChildSpecification(data)`, `worker(start_fn)`, `supervisor(start_fn)`, `Restart`, `ChildType`, `significant`, `timeout`, `restart`, `map_data`.
- **`static_supervisor`**: `new(strategy)`, `restart_tolerance`, `auto_shutdown`, `add(child)`, `start`, `supervised`. `Strategy` = OneForOne/OneForAll/RestForOne.
- **`factory_supervisor`**: DYNAMIC supervisor (start children on demand) — `worker_child`, `named`, `restart_strategy`, `start`, `start_child`, `get_by_name`.
- `system` (OTP sys/debug), `port` (typed ports).

Note: `task` (async/await) is NOT in `gleam_otp` 1.2 — neither library ships a future/await in core OTP today.

## Capability map

| Capability | Gleam | Cure | Parity |
|---|---|---|---|
| Typed process handle | `Pid`, `Subject(message)` | `Pid(m)`, `GenServer(q,r)` | Cure lacks Subject multiplexing (see gaps) |
| Synchronous call | `call` (reply-Subject-in-msg) | `call`, **`call_dep`** (dependent `ReplyOf(req)`) | **Cure ≥** (dependent, not just structural) |
| Per-request reply types | via reply-Subject per constructor | `ReplyOf : Req -> Type` (large elim) + `behavior` sugar | **Cure ≥** |
| Call failure | crash / panic on timeout | **`CallOutcome = Replied\|Failed`** (total, reified) | **Cure ≥** |
| Cast (fire-and-forget) | `send` | `cast`, `tell` | = |
| Actor definition | builder `new\|on_message\|start` | `actor` / `behavior` macros | = (both nice; Cure declarative) |
| Loop continue/stop | `Next` continue/stop | callback results `%[:reply,…]`/`%[:noreply,…]` | = |
| Dynamic protocol (swap handled msgs) | `with_selector` at runtime | `fsm` state machine | ≈ (different model; see gap D) |
| Supervisor (static) | `static_supervisor` | `Std.Supervisor` (`sup` macro), `otp_supervisor` Fleet | = (+ Cure has restart-preservation PROOFS) |
| Supervisor (dynamic) | `factory_supervisor` | `otp_supervisor` `Pool` (start/terminate_child) | = |
| Monitors / Down | `monitor`, `Down`, `select_monitors` | `Std.Process.monitor`, `otp_monitor` (typed + proof) | = / Cure ≥ |
| Links / trap_exit | `link`, `trap_exits` | `Std.Process.link`, `otp_link` (typed + proof) | = / Cure ≥ |
| Timers | `send_after`, `cancel_timer` | `send_after`, `cancel_timer`, `otp_timer` (proof) | = / Cure ≥ |
| Named/registered process | **`Name(message)`** typed | raw `register`/`whereis` → **untyped `BarePid`** (F-1) | **Gleam ≥** (gap C) |
| Typed message address, many-per-proc | **`Subject`** | — | **Gleam ≥** (gap A) |
| Selective receive (usable API) | **`Selector`** (rich, composable) | metatheory only (`otp_selective_receive`) | **Gleam ≥** (gap B) |
| Session types / duality | — | `Std.Otp.Session` (dual involution, compat⟺dual) | **Cure ≥** |
| Effect discipline (no dup/drop/reorder) | — | `Effect(T)` former | **Cure ≥** |
| Linear exactly-once reply | — | `ReplyCap(r)` linear capability | **Cure ≥** |
| Mailbox exhaustiveness / progress proof | — | `mailbox_exhaustive`, `otp_*` metatheory | **Cure ≥** |

## Where Cure already exceeds Gleam

Dependent per-request reply types (`ReplyOf` by large elimination) vs Gleam's structural reply-Subject; **total**
call-failure (`CallOutcome`) vs crash; **session types + duality** (communication safety Gleam has no analog for);
the **`Effect(T)`** discipline; the **linear** reply capability (exactly-once); and a large body of
**kernel-checked metatheory** (preservation, progress, mailbox exhaustiveness, restart-preservation, Fidge–Mattern
soundness+completeness). None of this exists in Gleam OTP.

**More behaviours than Gleam.** Gleam ships exactly ONE behaviour — the `actor` (gen_server-shaped); it has **no
`gen_statem`/FSM and no `gen_event`** (state machines are hand-rolled as an actor over a sum-type state). Cure has
typed `fsm` + `otp_gen_statem` + `otp_gen_event`. So on the behaviour axis Cure is strictly ahead.

**Neither ships `task`** (async/await). Gleam *had* a `task` module and deliberately removed it in
`gleam_otp` 1.0.0-rc1 (2025-05); the current guidance is to model async work as a monitored `spawn` + selector or
an actor. So a typed future/await is a *potential shared addition*, not a Cure gap — worth a small `Std.Otp.Task`
(spawn + monitor + typed await) if we want the ergonomic, since it's cheap on top of gap A's `Subject`.

## Status: gaps A/B/C CLOSED (2026-07-19)

All three addressing/ergonomics gaps are now landed in `Std.Otp` and runtime-verified on host OTP (`Cure.Otp.Builtins`
runtime helpers; tests `otp_subject_test` / `otp_selector_test` / `otp_name_test`):

- **A. `Subject(m)`** — `new_subject` / `subject_send` / `subject_receive`; two subjects of different types received
  independently by one owner. Erases to `{pid, ref}`; no registry (AtomVM-safe).
- **B. `Selector(p)`** — `new_selector` / `select` / `select_map` / `selector_receive`; heterogeneous subjects merged
  into one payload, dispatched by tag (mirrors Gleam's `gleam_erlang_ffi:select`).
- **C. `Name(m)`** — `name` / `register_name` / `whereis_name : Effect(Option(Pid(m)))` / `unregister_name`; the
  typed lookup **closes F-1** (a name now yields a typed, sendable handle, not a bare `BarePid`).

Remaining: **D** (dynamic accepted-set swap) and the ergonomic SUGAR (`beam_ops` verbs over subjects + a declarative
`select` block macro that desugars to the Selector API and ties to `Std.Otp.SelectiveReceive`).

## The gaps to close (all ergonomic / addressing-model)

### A. `Subject` — a typed address, many per process  ⟵ biggest conceptual gap
Cure's model is **one message type per process** (`Pid(m)`). Gleam's `Subject(message)` is a `(pid, unique tag)`
pair, so one process can own several typed channels and a caller addresses a *specific* channel. This is what
makes Gleam's `call` reply-typing and `Selector` compose. Feasible on AtomVM: a Subject is just a pid + a `make_ref`
tag used to wrap sent messages — **no registry / persistent_term** (which AtomVM lacks) is needed. Cure could add
`typealias Subject(m)` over `(Pid, Ref)` with `new_subject`, `send`, and receive-by-tag.

### B. `Selector` — a usable typed selective-receive API
Cure has `otp_selective_receive` as *proof* but no runtime surface. Gleam's `Selector(payload)` lets a process
receive from N heterogeneous subjects, each mapped into one payload type, composed with `select`/`map`/`merge`.
Cure rejects raw `receive` (E043) in favour of `fsm`/`actor`; a typed `Selector` would be the sanctioned,
composable way to do multi-channel selective receive — and its safety is exactly what the existing metatheory
proves. Build the API on top of Subjects (A).

### C. Typed named registration (`Name(message)`) — this is Cure's F-1
Cure's `raw_register`/`raw_whereis` exist but a name lookup yields an **untyped, unsendable `BarePid`** because the
name→message-type association is unbuilt (F-1, `otp_raw.cure` §6). Gleam's `Name(message)` closes exactly this: a
typed identity registered to a process, with take-over semantics. AtomVM caveat: Gleam `Name` uses atom
registration; confirm AtomVM's `erlang:register` support, or back `Name` with a Subject-style ref instead of the
atom table.

### D. Dynamic protocol via runtime handler/selector swap
Gleam's `Next.with_selector` lets an actor change *which messages it accepts* between steps. Cure expresses
protocol change through `fsm` (explicit state machine) — arguably clearer, but a `behavior`/actor that can swap its
accepted-message set at runtime (guided by the session type it's currently at) would match Gleam's flexibility and
tie directly to `Std.Otp.Session`. Lower priority than A–C.

## Recommended order

1. **A. `Subject(m)`** over `(Pid, Ref)` in `Std.Otp` — unlocks B and C, AtomVM-safe.
2. **B. `Selector`** on top of Subjects — typed multi-channel selective receive; back it with the existing
   `otp_selective_receive` metatheory.
3. **C. Typed `Name(m)`** — finally discharges F-1 (typed name→handle), reusing Subject tagging or atom
   registration once AtomVM support is confirmed.
4. **D.** dynamic accepted-message-set swap tied to `Std.Otp.Session` (optional polish).

Each is additive to the existing typed algebra and leaves the dependent/total/session advantages intact — i.e. the
end state is "everything Gleam does, plus dependent replies, total failure, sessions, effects, and proofs."
