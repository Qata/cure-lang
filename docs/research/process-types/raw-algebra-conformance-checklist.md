# `Std.Otp.Raw` conformance audit — against the Core Erlang formalisation

**Status:** ✅ **EXECUTED 2026-07-14.** Was an open checklist; this is now the
filled result. Two products delivered: a **conformance verdict** per op (§3) and
a **capability profile** (U/G/V) per op (§3), feeding the **fork decision** (§5).

**Oracle (primary):** Bereczky, Horpácsi & Thompson, *A Formalisation of Core
Erlang, a Concurrent Actor Language* (Acta Cybernetica 2023, arXiv 2311.10482) —
Coq-machine-checked small-step frame-stack semantics of concurrent Core Erlang.
PDF: `core-erlang-formalisation-2311.10482.pdf` (this directory). Cited below by
rule name (Fig. 2–5) and theorem number.

**Oracle (secondary, where the paper is silent):** the OTP reference manual, plus
**empirical probes** run against OTP 27 on this machine (§2.2) and a **source
audit of the AtomVM clone** at `/Users/ch/Develop/esp32-beam/AtomVM` @ `efa90df6`
(v0.7.0-alpha.1-209), cited by `file:line` (§4).

**Code under audit:** `lib/std/otp_raw.cure` (sealed raw base, 24 ops) narrowed by
`lib/std/otp.cure` (typed surface). Design: `docs/superpowers/specs/beam/2026-07-09-typed-beam-process-algebra-design.md`.

---

## 1. Headline

**Two of the three questions the checklist was written to answer came back the
opposite of what it predicted.**

1. **The signal layer is NOT the platform-gated crux.** The checklist marked
   `link`/`unlink`/`exit`/`monitor`/atomic `spawn_link` as **G** ("AtomVM
   divergence likely"). They are all **U**. AtomVM implements the signal layer at
   full OTP fidelity — including the OTP-23+ unlink/ack protocol, atomic
   `spawn_link`, all three `trap_exit` outcomes, untrappable `kill`, monitors with
   `flush`, and pairwise signal ordering. **This dissolves the design fork rather
   than deciding it** (§5).
2. **The real gates are one layer up, in the OTP *behaviour libraries*** —
   `gen_statem` (a `gen_server` shim), `supervisor` (2 of 4 strategies), and
   timers (which carry an outright **defect**). Those are macro/codegen concerns,
   not typed-algebra concerns.
3. **The conformance pass found four real defects**, three of them confirmed by
   executing the compiler (§2.2). The most severe is not on the checklist's
   suspect list: **the pid index `m` in `Pid(m)` is founded on nothing** — every
   pid-producing op lets the caller choose it freely.

---

## 2. Method and evidence

### 2.1 Scope of the paper (what it does and does not govern)

The paper formalises exactly: `send` (`!`), `receive` (no `after`), `spawn`,
`self`, `link`, `unlink`, `exit/1,2`, the `trap_exit` flag, and the signal-ordering
guarantee. Signals are `Signal ::= msg(v) | exit(v,b) | link | unlink` (Def. 4).

It **does not** formalise — and is therefore *not* an oracle for — **monitors**,
**exceptions**, **timers**, the **name registry**, the **module system**, or any
of `gen_server`/`gen_statem`/`supervisor` (§7 Future Work). It also does **not**
formalise `spawn_link`: `NSpawn` (Fig. 5) creates the child with an **empty** link
set. So the checklist's attribution of the `spawn_link` atomicity contract "to the
paper" was wrong; that contract comes from the OTP reference manual, and is
verified against implementations below.

### 2.2 Probes actually run (not assumed)

**BEAM BIF return values, OTP 27** — every raw op the base types as `Effect(Unit)`
was executed and its real return value captured:

| BIF | actual return |
|---|---|
| `erlang:send/2` | the **message** (`hello`) |
| `erlang:link/1`, `unlink/1`, `exit/2`, `register/2`, `unregister/1`, `demonitor/1` | `true` |
| `gen_server:cast/2`, `gen_server:stop/1` | `ok` |
| `erlang:cancel_timer/1` | `5000` (an **Int**) — or `false` once fired |
| `erlang:whereis/1` on an unknown name | **`undefined`** (a bare atom, not a pid) |
| `erlang:send/2` to a **dead** pid | the message; no raise (delivery silently dropped) |
| `erlang:exit(Other, normal)` on a non-trapping target | target **stays alive** (confirms `ExitDrop`) |

**Cure elaborator probes** — four programs put through `Program.elaborate/1`:

| # | program | result |
|---|---|---|
| A | `spawn` a thunk that handles **nothing**, ascribe `Pid(Cmd)`, then `tell(p, Inc)` | **`:ok`** — typechecks |
| B | `call` that same plain (non-`gen_server`) pid as a server | **`:ok`** — typechecks |
| C | `whereis(:nobody)` ascribed `Pid(Cmd)`, then `tell(p, Inc)` | **`:ok`** — typechecks |
| D | *control:* send a **wrong-typed** message to a `Pid(Cmd)` | **`:error {:index_mismatch, …}`** — correctly rejected |

Probe D matters: it shows the tag/payload check **does** work — *conditional on the
index being right*. Probes A–C show nothing establishes that condition.

---

## 3. The audit table

**Layer:** PRIM = Core-Erlang primitive (paper-direct) · OTP = library (paper is
*not* an oracle). **Profile:** U = universal (holds on OTP-BEAM *and* AtomVM) ·
G = platform-gated · V = verify. **⇄** marks a letter that came back **opposite to
the checklist's prediction**.

| Raw op → BIF | Layer | What the semantics actually guarantees | Profile | Conformance verdict |
|---|---|---|---|---|
| `raw_self` → `erlang:self/0` | PRIM | `Self` (Fig. 4): total, yields own pid. | **U** | ⚠️ **F-1.** Typed `self : Effect(Pid(m))` at a **free** `m` — the caller picks its own accepted-message set. Unfounded (see F-1). |
| `raw_send` → `erlang:send/2` | PRIM | `Send` (Fig. 3) emits into the *ether*; arrival is a **separate, nondeterministic** step (`NArrive`, Fig. 5). Delivery is **not** promised; a send to a dead pid silently succeeds. Ordering is **pairwise only** (Thm. 2: same sender → same target); cross-sender order is **unspecified** (Ex. 3). | **U** | ✅ **Conforms.** `tell` is fire-and-forget `Effect(Unit)`; nothing sequences on delivery, liveness, or cross-sender order. ⚠️ *But* `otp_raw.cure`'s docstring says the effect discipline "forbids duplicating, dropping, or reordering a `send`" — that is about the **program's effect sequence**, not mailbox arrival. Reword before a reader mistakes it for a delivery guarantee. |
| `raw_spawn` → `erlang:spawn/1` | PRIM | `NSpawn` (Fig. 5): child starts with **empty mailbox, no links, `trap_exit` = ff**. | **U** | ⚠️ **F-1.** The thunk is `() -> Unit` — it carries **no** message type — yet the result is `Pid(m)` at a free `m`. Nothing relates `m` to what the process receives. |
| `raw_spawn_link` → `erlang:spawn_link/1` | PRIM | **Paper is silent** (it formalises only `spawn`). OTP manual: the link is established **atomically**; no window in which the child can die unlinked. | **U** ⇄ | ✅ **Conforms.** The base calls the real `erlang:spawn_link/1`, not a `spawn`-then-`link` shim. AtomVM is **atomic too**: `do_spawn` installs *both* half-links on *both* contexts (`nifs.c:1500-1515`) **before** `scheduler_init_ready` makes the child runnable (`nifs.c:1541`). Zero race window. |
| `raw_link` → `erlang:link/1` | PRIM | `Link` (Fig. 3) / `LinkArr` (Fig. 2): bidirectional; mutual exit propagation. A dead process still notifies its links (`Dead`, Fig. 3; `Term`, Fig. 4). | **U** ⇄ | ✅ **Conforms.** AtomVM: genuinely bidirectional — two half-links, one installed locally, one shipped as a `MonitorSignal` (`nifs.c:5067-5099`). |
| `raw_unlink` → `erlang:unlink/1` | PRIM | **The checklist's row was wrong.** Correct contract: once `unlink` returns, the link has **no further effect** on the caller — a link-flagged exit from a peer no longer in the link set is **dropped on arrival** (`ExitDrop` clause 2, Fig. 2: `ι₁ ∉ pl ∧ bₑ = tt`). What *may* persist is an `{'EXIT',…}` **message already in the mailbox** from before the unlink (if trapping). | **U** ⇄ | ✅ **Conforms** (the typed `unlink` promises nothing). AtomVM implements the real **OTP-23+ unlink protocol**, not a list removal: `context_set_unlink_id` stamps the half-link *inactive* (`context.c:963-974`) → `UnlinkIDSignal` → peer acks (`context.c:1000-1019`) → originator drops its half (`context.c:1047`). Terminate skips inactive links (`context.c:749-752`). |
| `raw_exit` → `erlang:exit/2` | PRIM | **Sends a signal, not a kill.** Three outcomes on the target's `trap_exit` (`ExitDrop`/`ExitTerm`/`ExitConv`, Fig. 2). Converted exits land at the **end** of the mailbox. **Two corrections to the checklist:** (a) `kill` is untrappable **only when sent explicitly** via `exit/2` (link flag `ff` → `ExitTerm`, reason rewritten to `killed`). A `kill` arriving **through a link** (`bₑ = tt`) **is trappable** — `ExitConv` admits it; paper Ex. 4 states this outright. (b) `exit(self, normal)` **does** terminate (`ExitTerm`, `ι₁ = ι₂`), whereas `exit(other, normal)` is dropped. | **U** ⇄ | ✅ **Conforms on the death question** — typed `exit → Effect(Unit)` makes **no** type-level claim that the target dies. ⚠️ **F-3:** `reason: {r: Type}` is fully polymorphic, erasing the `normal`/`kill`/other distinction every one of the three rules turns on. A typed lifecycle story must carry the reason as a precise 3-way sum. AtomVM: all three outcomes + untrappable `kill` correct (`nifs.c:4709-4749`). |
| *(absent)* `erlang:process_flag(trap_exit,_)` | PRIM | `Flag` (Fig. 4) — selects the outcomes above; **returns the previous value**, not `ok`. | **U** | ✅ **Omission is intentional and currently sound**: no raw op needs it (behaviours own the mailbox; raw `receive` is E043). ⚠️ **Ledger:** no Cure-authored process can therefore *trap exits*. Today the `sup` behaviour gets trapping from Erlang's own `supervisor` module. Any Cure-level supervisor **will** need this op. |
| `raw_monitor` → `erlang:monitor/2` | PRIM? | **Paper is silent** — monitors are not in its signal set (Def. 4). Oracle = OTP docs. Unidirectional, non-failing; delivers `{'DOWN',Ref,process,Pid,Reason}`; a dead target yields an immediate `DOWN` with `noproc`. | **U** (paper N/A) | ✅ Conforms. AtomVM: full native monitors, incl. registered-name targets and immediate `noproc` `DOWN` (`nifs.c:4921-5013`). |
| `raw_demonitor` → `erlang:demonitor/1` | PRIM? | Removes the monitor; the **`flush`** option discards an already-delivered `DOWN`. | **U** (paper N/A) | ⚠️ **F-5.** The raw op omits `flush`, so a stale `DOWN` can survive a `demonitor` — meaning the `infos` code **must** admit `DOWN`. AtomVM *does* support `flush` **and** `info` (`nifs.c:5022-5061`), so the omission is Cure's choice, not a platform limit. |
| **Signal ordering** (cross-cutting) | PRIM | **Thm. 2:** signals from the *same* sender to the *same* target arrive in order — and this covers **messages and exit signals alike** (the ether is keyed by `(source,target)`, Def. 5). Cross-sender order is unspecified (Ex. 3). | **U** ⇄ | ✅ **Conforms** — no typed op leans on ordering at all. AtomVM preserves it *by design*: messages and signals share one CAS-pushed queue (`mailbox.c:214-233`); the trap-exit and monitor-down paths deliberately **re-enqueue** their `{'EXIT'}`/`{'DOWN'}` tuples as *normal messages* so they land behind earlier messages from the same sender (`context.c:406-410`, `:438`). |
| `raw_cast` → `gen_server:cast/2` | OTP | Async tagged `send`; inherits the `send` contract. Returns **`ok`**. | **U** | ✅ Conforms (async, no reply assumed). ⚠️ **F-4** (result typed `Unit`, actually `ok`). |
| `raw_call` → `gen_server:call/2` | OTP | **Not a total function.** `send` + one-shot monitor + selective `receive`, default **5000 ms**; on timeout or server death the **caller exits**. (Note: the paper's `receive` has **no `after`** — the timeout mechanism is entirely outside the formalised fragment.) | **U** | ❌ **F-2. Non-conforming.** `raw_call : … -> Effect(r)` types `call` as **total**. The `ReplyOf` story must carry the failure mode. AtomVM behaves exactly like OTP here — monitor-based call (`gen.erl:51-77`), 5000 ms default (`gen_server.erl:406`), `exit(timeout)` in the caller (`gen.erl:75-76`). The gap is Cure's, on **every** platform. |
| `raw_start_link` → `gen_server:start_link/3,4` | OTP | Returns `{ok,Pid}` \| `{error,_}` \| **`ignore`** — and `ignore` is a **bare atom**, not a tuple. | **G**(patched) | ❌ **F-4b.** Typed `Effect(Tuple)` — a lie in the `ignore` case **on OTP**. (Honest on AtomVM only because AtomVM's `gen_server` doesn't implement `ignore`: its `init` result type is `{ok,State} | {stop,Reason}`, `gen_server.erl:79`.) Targeting OTP ⇒ the return must become a union. Patch dependency (exavmlib + `ets:whereis`) per CLAUDE.md stands. |
| `raw_statem_start_link` → `gen_statem:start_link/3,4` | OTP | `gen_statem` callback contract. | **G** | ⚠️ **Real gate.** AtomVM's `gen_statem` is a **shim over `gen_server`**: **state-functions mode only** (no `handle_event_function`), **no** `postpone`, `keep_state`, `repeat_state`, `hibernate`, or state-enter calls; locally-named only (`gen_statem.erl:31-40`). `state_timeout` *is* supported. The `fsm` macro must not emit the unsupported forms. |
| `raw_supervisor_start_link` → `supervisor:start_link/3` | OTP | Supervision tree; restart semantics per child spec. | **G** | ⚠️ **Real gate.** AtomVM supports **`one_for_one` and `one_for_all` only** — **no `rest_for_one`, no `simple_one_for_one`** (`supervisor.erl:84`). Restart types (`permanent`/`transient`/`temporary`) and intensity limits are present. |
| `raw_stop` → `gen_server:stop/1` | OTP | Orderly, synchronous termination via `terminate/2`. Returns `ok`. | **U** | ⚠️ **F-2b.** Typed `stop` accepts **any** `Pid(m)` — including a plain spawned process that is not a `gen_server`, where the call cannot succeed. Same root cause as F-2 (`Pid` ≡ `GenServer`). |
| `raw_send_after` → `erlang:send_after/3` | BIF | Delivers `msg` after `delay`; returns a **cancellable** `Ref`. Paper N/A. | **G** 🔴 | 🔴 **Platform defect (AtomVM).** `erlang:send_after/3` mints a **fresh ref** and returns it, while the timer it registers with `timer_manager` carries a **different** ref (`timer_manager.erl:87-91`). ⇒ **`cancel_timer/1` on that ref always returns `false` and the message still fires.** `erlang:start_timer/3`'s ref *is* cancellable (different message shape: `{timeout,Ref,Msg}`). Also: one process per timer, and `timer_manager` lives in **eavmlib** — it must be packed into the `.avm`. |
| `raw_cancel_timer` → `erlang:cancel_timer/1` | BIF | Returns **remaining ms (Int)** or **`false`**. Paper N/A. | **G** 🔴 | ❌ **F-4c — the worst of the `Unit` lies:** an `Int` typed as `Unit`. Plus the AtomVM defect above makes it a **no-op** on the ref `send_after` hands you. |
| `raw_is_alive` → `erlang:is_process_alive/1` | BIF | Point-in-time; **racy by construction** — stale the instant it is produced. | **U** | ✅ Conforms — nothing branches on it. Must never be used to justify a later send. |
| `raw_register` → `erlang:register/2` | BIF | Local name table. Returns `true`. `badarg` if the name is taken or the pid is dead. | **U** ⇄ | ✅ Conforms. **The checklist's suspicion was misplaced:** CLAUDE.md's "avoid `Registry`/`persistent_term`" is about *Elixir* `Registry`. The **raw** `erlang:register` name table is native on AtomVM (`nifs.c:1239`). ⚠️ **F-4.** |
| `raw_unregister` → `erlang:unregister/1` | BIF | Removes the name. Returns `true`. | **U** ⇄ | ✅ Conforms. ⚠️ **F-4.** |
| `raw_whereis` → `erlang:whereis/1` | BIF | Name → pid **or the bare atom `undefined`**. | **U** ⇄ | ❌ **F-2c. The hardest type lie in the base.** `raw_whereis : Atom -> Effect(RawPid(m,m))` **asserts the lookup succeeds**. It does not: on both OTP (probed) and AtomVM (`globalcontext.c:641`) an unknown name yields the atom `undefined`. Probe C: `whereis(:nobody)` then `tell` **typechecks**, and emits `erlang:send(undefined, …)` → `badarg` at runtime. |
| `raw_term` → `erlang:element/2` | BIF | 1-based tuple projection; `badarg` out of range. | **U** | ✅ **Confined.** `Std.Otp` re-exports the *type* (`typealias BeamTerm = RawTerm`) but **not** the function, so user code cannot construct a `RawTerm` — the type-forgetting boundary is closed. (Corollary: the "heterogeneous OTP arg list" use case it exists for currently has no path.) Nit: `index: Int` is unconstrained where `Nat`/`Bounded` is the honest type. |

---

## 4. Findings, by severity

### F-1 🔴 The pid index is founded on nothing (the headline defect)

Every pid-producing op takes the message index as a **free implicit**:

```cure
fn self({m: Type})                          -> Effect(Pid(m))   # m: caller's choice
fn spawn({m: Type}, thunk: () -> Unit)      -> Effect(Pid(m))   # thunk says NOTHING about m
fn spawn_link({m: Type}, thunk: () -> Unit) -> Effect(Pid(m))
fn whereis({m: Type}, name: Atom)           -> Effect(Pid(m))
```

Nothing relates `m` to the messages the process actually handles. Probe A: a thunk
that handles nothing, ascribed `Pid(Cmd)`, happily accepts `tell(p, Inc)`.

This is **not** a violation of the BEAM's semantics — it is the **narrowing having
no foundation**. The spec's answer is §4.2: *"The user never writes a `MsgType`. It
is projected, at compile time, from the message ADTs and the handler clauses."*
That derivation is **Rung 2 and is unbuilt**; `MessageCode` in `otp.cure` is
vestigial (a tag/arity list, with `handles`/`subset`/`union` defined over it but
**not wired to any pid**). Until it is, `Pid(m)`'s guarantee is *conditional on an
index the user asserts* — i.e. an unchecked cast in the shape of an inference hole.

Sharpen the honest claim: **the floor catches wrong-tag/wrong-payload sends
relative to a declared index (probe D proves it works), but nothing yet checks the
index against the process.** Do not describe the floor as "send only what the
receiver handles" until the derivation lands.

*(Aside: today the implicit doesn't even solve — bare `spawn(f)` fails with
`:unsolved_metavariables`, the known goal-directed-solving gap — so in practice the
index must be supplied by ascription, which makes the cast explicit but no more
checked.)*

### F-2 🔴 `call` is typed as a total function; `Pid` and `GenServer` are the same type

Two defects with one root:

- `typealias Pid(m) = RawPid(m, m)` and `typealias GenServer(q, r) = RawPid(q, r)`
  ⇒ **`Pid(m)` *is* `GenServer(m, m)`.** Probe B: `call` on a plain spawned pid
  typechecks. Runtime: the caller blocks 5 s, then `exit(timeout)`. Same for
  `stop` (F-2b). These are aliases, not distinct opaque types — they give **zero**
  separation.
- `raw_call : … -> Effect(r)` claims **totality**. `gen_server:call` can time out
  (default 5000 ms) or the server can die; either way the **caller exits**. The
  dependent `ReplyOf` typing must carry that failure mode — `Effect(Result(r, _))`,
  or an exceptional index. This is platform-independent: AtomVM matches OTP exactly.

### F-2c 🔴 `whereis` asserts a lookup that can fail

`raw_whereis` returns `RawPid(m,m)`; the BEAM returns the atom `undefined` for an
unknown name (probed on OTP; `globalcontext.c:641` on AtomVM). A well-typed Cure
value of type `Pid(m)` is then **the atom `undefined`**, and the next `tell` emits
`erlang:send(undefined, …)` → `badarg`.

The machinery to fix it already exists: Cure has **anonymous unions**, and
`emit.ex:284-318` **re-tags** an extern's union result at the FFI boundary. So
`raw_whereis -> Effect(RawPid(m,m) | Atom)` is expressible today, with the typed
facade returning `Effect(Option(Pid(m)))`. Spec ledger §13.7 files this as an
ergonomics question; it is a **soundness** bug.

### F-3 🟡 The exit reason is polymorphic, erasing the distinction the rules turn on

`raw_exit(pid, reason: {x: Type})`. But `ExitDrop`/`ExitTerm`/`ExitConv` all case
on `reason ∈ {normal, kill, other} × trap_exit × link-flag`. Collapsing the reason
to a type variable means the typed layer cannot express — and a reader cannot
recover — which of the three outcomes a given `exit` can have. Carry it as a
precise sum. (Good news: the typed `exit` correctly makes **no** claim that the
target dies, which was the checklist's chief worry. ✅)

### F-4 🟡 Ten raw ops declare `Effect(Unit)` for BIFs that return real terms

The spec demands (§3.1) *"every function an `@extern` at its most permissive
**honest** BEAM type"* and ships a validator for exactly this (§12
`no_widening_narrow`). Both are being violated. `emit.ex:260-271` emits a **bare
remote call with no result coercion**, so the term flowing into Cure as `Unit`
(runtime atom `unit` — `emit.ex:12`, `program.ex:444`) is really:

| raw op | declared | actually returns (probed, OTP 27) |
|---|---|---|
| `raw_send` | `Effect(Unit)` | **the message itself** (paper agrees: `Send`, Fig. 3, reduces to `v`) |
| `raw_link`, `raw_unlink`, `raw_exit`, `raw_register`, `raw_unregister`, `raw_demonitor` | `Effect(Unit)` | `true` (paper agrees: `Exit`, Fig. 3, reduces to `'true'`) |
| `raw_cast`, `raw_stop` | `Effect(Unit)` | `ok` |
| **`raw_cancel_timer`** | `Effect(Unit)` | **`5000` — an `Int`** — or `false` |
| `raw_start_link` (+ statem, supervisor) | `Effect(Tuple)` | `{ok,Pid}` \| `{error,_}` \| **`ignore`** (a bare **atom**, on OTP) |

Latent today (nothing in the stdlib observes these `Unit`s), but it is precisely
the class §12's validator exists to catch — which means the validator is **unbuilt
or not run** over the raw base. `raw_cancel_timer` is the sharp one: an integer
inhabiting `Unit`.

### F-5 🟢 Minor

- **`Ref` is one type for two things.** `typealias MonitorRef = Ref` and
  `TimerRef = Ref` are aliases ⇒ the same type, so `cancel_timer(monitor_ref)` and
  `demonitor(timer_ref)` both typecheck. Harmless on the BEAM (each returns
  `false`/`true`), trivially fixed with two distinct opaque types.
- **`demonitor` omits `flush`** ⇒ a stale `DOWN` can outlive it; the `infos` code
  must admit `DOWN`. AtomVM supports `flush` — this is Cure's omission, not a gate.
- **The `otp_raw.cure` docstring's "forbids … reordering a `send`"** is about the
  effect *sequence*, not mailbox arrival. Reword: the BEAM guarantees pairwise
  sender→target ordering **only** (Thm. 2), and **no delivery at all**.

### ✅ What the audit *cleared*

- `send` assumes **no** delivery, **no** acknowledgement, **no** cross-sender
  ordering. Conforms.
- `exit` makes **no** type-level guarantee that the target dies. Conforms.
- The `trap_exit` omission from the raw base is intentional and currently sound.
- `raw_term` is properly confined — user code cannot construct a `RawTerm`.
- The tag/payload check genuinely works (probe D) — *given* an index.

---

## 5. The fork: **DISSOLVED — target full OTP-BEAM; AtomVM is not a restricted profile at this layer**

The open fork was: *target full OTP-BEAM and treat AtomVM as a capability-restricted
profile (algebra may lean on signal-ordering/link guarantees, feature-gate what
AtomVM lacks), or target the intersection so everything runs everywhere but weaker.*
It was explicitly premised on **the signal-layer ops being the crux**.

**That premise is false.** Every signal-layer guarantee the algebra could want is
**U — universal**:

| guarantee the algebra might lean on | OTP-BEAM | AtomVM | evidence |
|---|---|---|---|
| atomic `spawn_link` (no unlinked window) | ✔ | ✔ | both half-links installed before `scheduler_init_ready` (`nifs.c:1500-1541`) |
| bidirectional links | ✔ | ✔ | `nifs.c:5067-5099` |
| OTP-23+ unlink/ack (no future effect after `unlink` returns) | ✔ | ✔ | `unlink_id` → `UnlinkIDSignal` → ack (`context.c:963-1055`) |
| all three `trap_exit` outcomes | ✔ | ✔ | `nifs.c:4709-4749` |
| `kill` untrappable when sent via `exit/2` | ✔ | ✔ | `nifs.c:4722-4724` (checked *before* the trap branch) |
| `{'DOWN',…}` monitors, incl. `flush` | ✔ | ✔ | `nifs.c:4921-5061` |
| pairwise sender→target signal ordering | ✔ (Thm. 2) | ✔ | one shared queue + deliberate re-enqueue (`mailbox.c:214-233`, `context.c:406-410`) |

**Therefore: take the full-OTP-BEAM target. The algebra may rely on the signal
layer unconditionally.** There is no meaningful intersection to retreat to — *the
intersection is the full layer*. Choosing "intersection" would surrender
link-based supervision and buy **nothing**, since nothing is actually missing.

Equally important: **there is no need for a capability index on `Effect` or on the
typed ops.** That was the latent cost of the "restricted profile" branch — it would
have infected every operation's type with a platform parameter. It is now
unnecessary.

**The gating that *is* real moves up one layer, to the behaviour macros** — where it
is ordinary codegen restriction, not a typed-algebra concern (and belongs to the
Rung-1 lowering-target fork, spec §13.1):

1. **`fsm` macro** must not emit `handle_event_function`, `postpone`, `keep_state`,
   `repeat_state`, `hibernate`, or state-enter calls — AtomVM's `gen_statem` is a
   `gen_server` shim supporting **state-functions mode only** (`state_timeout` is
   fine).
2. **`sup` macro** must restrict to **`one_for_one` / `one_for_all`** — AtomVM has
   no `rest_for_one`, no `simple_one_for_one`.
3. **Timers are the one genuine 🔴 defect.** `Std.Otp.send_after` + `cancel_timer`
   are in the *sanctioned* surface, and on AtomVM the ref `send_after` returns is
   **uncancellable** (`timer_manager.erl:87-91`): `cancel_timer` returns `false`
   and the message fires anyway. Either re-target the pair at
   `erlang:start_timer/3` (cancellable; message shape `{timeout,Ref,Msg}`) or fix
   AtomVM upstream. Until then, `Std.Otp.cancel_timer` is a **no-op on device** —
   which is far worse than a missing feature, because it type-checks.
4. **`start_link`'s `ignore`** return exists on OTP and not on AtomVM — targeting
   OTP means the raw return type must widen to a union (F-4b).

**One-line asymmetry worth recording:** on the signal layer AtomVM ≡ OTP; on the
behaviour libraries **OTP is strictly wider**; and on timers **AtomVM is broken**,
not merely narrower.

---

## 6. Follow-up batch (not done here — this was an audit)

Ordered by severity. F-1 and F-2c are hard-stop-flavoured: they make the typed
layer *claim* something the BEAM does not deliver.

1. **F-2c** — `raw_whereis -> Effect(RawPid(m,m) | Atom)`; typed facade returns
   `Option(Pid(m))`. Machinery already exists (anonymous unions + `emit.ex`'s
   union re-tagging). *Smallest fix, real soundness win.*
2. **F-2** — split `Pid` and `GenServer` into **distinct opaque types** (not
   aliases), and give `call` a failure mode.
3. **F-1** — the Rung-2 code derivation (§4.2): project the message code from the
   ADTs/handler clauses so `m` stops being a free choice. *This is the big one and
   it is a whole rung, not a patch.*
4. **F-4** — honest raw result types + actually run the §12 `no_widening_narrow`
   validator over `Std.Otp.Raw`.
5. **F-3 / F-5** — precise exit reason; distinct `MonitorRef`/`TimerRef`; `flush`;
   docstring reword.
6. **Timers** — re-target `send_after`/`cancel_timer` at `start_timer/3`, or fix
   AtomVM.

## 7. What running this did *not* settle (unchanged)

- It does **not** justify undoing the macro-spec §9.5 deferral of typestate /
  multiplicity / junk-freedom. That is gated on an **inference** story for
  ordered/selective-receive mailboxes (Special Delivery names inference as the open
  problem) — independent of this audit. Note the paper *reinforces* why: the mailbox
  is **ordered with selective receive** (`Receive`, Fig. 4 — first matching message,
  first matching clause) on **every** BEAM, while the commutative-regex typestate
  models are stated for *unordered* interactions.
- It does **not** call for a mechanised bisimulation relating `Std.Otp.Raw` to the
  Coq development. (The paper's Thm. 9 — sequential evaluation is a weak
  bisimulation — is relevant later to `backend-decoupling`'s portable
  process-effect interface, not here.)
