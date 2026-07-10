# Checked BEAM Concurrency: Linear Session-Typed Processes and Resources

**Date:** 2026-07-10
**Status:** design — approved direction, targets 0.35/0.36 (after the inert `Effect(T)` former ships)
**Supersedes / overturns:** four specific decisions in prior specs, each flagged inline and collected in §12.
**Companions:**
- `2026-07-09-effect-type-former-design.md` (the inert `Effect(T)` this design builds ON, not against)
- `2026-07-09-typed-beam-process-algebra-design.md` (rungs 0–2 stand; rung 3 is replaced by §4 here)
- `macros/2026-07-08-protocol-macro-design.md` (its affine-handle choice is overturned by §6)
- `docs/cure_reactive_runtime_design_bible_v12_release_hierarchical.md` (the layer rule this design slots into)

---

## 1. Problem and principle

Cure currently has no concurrency on the dependent pathway at all. The classic
pipeline's `fsm`/`actor`/`sup`/`app` containers check the shape of a state
machine but not the conversation between processes, and they die with the
classic rip-out. The 0.34 plan restores concurrency over an opaque, inert
`Effect(T)` whose type says nothing about what the effect *does* — send a
message, spawn a process, delete the filesystem: all `Effect(Unit)`.

The long-term defect in `Effect(T)` is **not** that it is irreducible. Inertness
(zero equations, no monad laws, structural congruence in Conv) is correct and is
deliberately retained by this design: if effect structure reduced during
conversion, typechecking could rewrite the program's operational behaviour —
the exact door the Effect spec closes. The defect is that the **index is
uninformative**. The fix is to keep inert and enrich what the types say around
it.

**Core principle:** BEAM processes are not Cure's concurrency semantics. Cure
has a checked concurrency semantics — session-typed channels and linear
capabilities — that *lowers to* BEAM processes under a narrow, explicit backend
contract.

## 2. Ground truth this design is built on

Verified against the code (not specs) on 2026-07-10:

- **Core grammar** (`lib/cure/core/term.ex:14-20`): six formers, no effect
  former yet. The inert `Effect` is spec'd, unbuilt. Greenfield — nothing to
  migrate, only to preempt.
- **Quantities** (`lib/cure/elab/relevance.ex`, `erase.ex`): two-valued
  `:erased | :present` on def params and ctor fields; the kernel is
  quantity-blind. Multiplicity `1` explicitly out of scope *today* — but the
  operator has confirmed (2026-07-10) that linear/affine types are planned, and
  this design is shaped around them (§5).
- **Concurrency surface**: classic-pipeline only; raw `spawn`/`receive` rejected
  with E043 (`lib/cure/types/checker.ex:1517`). No macro facility, no
  `Std.Otp`, no dependent-pathway concurrency exists.
- **Cure's `let` is surface substitution, not a binder**
  (`elaborate_let_block`): the rhs is inlined per use and dropped at zero uses.
  This is a hard prerequisite blocker for linear values (§5.4).
- **AtomVM facts** (audited in the clone, file:line in §9/§10): single scheduler
  thread on C3-class targets; port handlers run on the scheduler thread; I²C
  blocks with `portMAX_DELAY`; SPI busy-polls; the receive-marker optimization
  does not exist (opcodes are no-ops); a 16-slot shared event queue drops ISR
  events silently when full; `mailbox_message_create_from_term` silently drops
  a message when its malloc fails; `exit(Pid, kill)` is untrappable; OOM is a
  catchable per-process error, except during termination-message construction
  where it aborts the whole VM.

## 3. Architecture: three layers, one boundary rule

```
Layer 1  Kernel (TCB)         — UNCHANGED. No new judgement, no indexed bind.
                                Checks Chan/Resource as ordinary indexed
                                families; Effect(T) stays inert and
                                non-dependent.

Layer 2  Elaborator + Std     — protocol/state indices on channel and resource
                                types; {0,1,ω} linearity check in the E layer
                                (extension of relevance.ex, kernel stays
                                quantity-blind); `process`/`protocol`/
                                `resource` macros elaborate direct-style code
                                into bind chains; all macro output re-elaborated
                                and kernel-checked like hand-written code.

Layer 3  Backend (trusted)    — lowers accepted terms to BEAM spawn/send/
                                receive/monitor under the contract in §9.
                                All protocol/quantity information erases;
                                emitted code is byte-shaped like hand-written
                                Erlang.
```

**Boundary rule (from the reactive-runtime bible, unchanged):** flow computes;
fsm reduces; reactor advances islands; **program interprets commands and
performs effects; resource owns local external capability; port owns remote
session.** No effects below Program. This design supplies the typed content of
`resource` (§8) and `port` (§4–§7).

## 4. Core model: linear session channels over inert `Effect(T)`

### 4.1 Why not a world-indexed `Proc(a, pre, post)`

The predecessor plan (process-algebra spec §10, "rung 3") called for a
parameterized monad `Effect(pre, post, T)` with an indexed bind — a real kernel
extension, flagged there as the one research-grade TCB-touching item. With
linear types available, **that machinery is unnecessary**: the world index
exists only to simulate linearity where the type system lacks it (Idris 1's
`ST`; Idris 2's session libraries dropped the world once QTT landed). When the
handle carries its own protocol state in its own type and is consumed linearly,
there is nothing left for a monad index to track.

**Overturned decision #1:** rung 3's `Effect(pre,post,T)` indexed bind is not
needed and will not be built. Concurrency becomes elaborator + stdlib work with
**zero kernel change**.

**Overturned decision #2:** the same spec's "the discipline rides on indices —
not linear types (out per the post-parity teardown)" is reversed, and its
citation was wrong in the first place: `post-parity-teardown-batch` orders three
teardowns (lean4lean revert, classic deletion, refinement removal) and says
nothing about linear types. The question was open; it is now decided in favour
of linear capabilities.

### 4.2 The types

`Protocol` is an ordinary inductive (a code, in the sense of the process-algebra
spec §4 — data, derived, erased):

```
Protocol ::= Send(MsgShape, Protocol)
           | Recv(MsgShape, Protocol)
           | Offer(List(%[MsgShape, Protocol]))     -- external choice
           | Select(List(%[MsgShape, Protocol]))    -- internal choice
           | Done
```

`Chan : Protocol -> Type` is an ordinary indexed family (same machinery as
`Bounded`/`Vector`). The operations return the *next-state channel inside the
result*, so the plain non-dependent `Effect(T)` bind suffices:

```
send   : (1 c : Chan(Send(m, next))) -> El(m) -> Effect(Chan(next))
recv   : (1 c : Chan(Recv(m, next)))          -> Effect(%[El(m), Chan(next)])
select : (1 c : Chan(Select(bs))) -> (tag : TagOf(bs)) -> El(payload(bs,tag))
                                              -> Effect(Chan(cont(bs, tag)))
offer  : (1 c : Chan(Offer(bs)))              -> Effect(Branches(bs))
close  : (1 c : Chan(Done))                   -> Effect(Unit)
cancel : (1 c : Chan(s))                      -> Effect(Unit)   -- any state
```

`offer` returns a **sum whose constructors carry the correctly-typed
continuation channel** (`Branches([Deposit → s1, Balance → s2]) =
Deposit(Int, Chan(s1)) | Balance(ReplyChan, Chan(s2))`); the caller `match`es
on it. The value dependency lives inside the returned value, not in the bind —
this is what removes the need for a dependent/indexed bind.

`El : MsgShape -> Type` is the decoder from the existing codes design,
unchanged. `ReplyOf` remains a lookup in the code — not a type family, not a
GADT.

### 4.3 Duality, checked by computation

`dual : Protocol -> Protocol` is an ordinary total function (`Send ↔ Recv`,
`Offer ↔ Select`, `Done ↔ Done`). `spawn`/`connect` mint a channel pair at
`p` and `dual(p)`; the obligation discharges by normalisation for concrete
protocols — consistent with the locked no-subtyping stance (inclusion and
duality are `Bool`-valued computation, never a `<:` judgement).

### 4.4 Two levels of process reference

- **`Pid(m)`** — an *address*: ordinary, copyable, ω, storable, sendable,
  exportable to foreign code, survives supervisor restarts. Typed by the flat
  message-set code it *offers* (the rung-2 floor, unchanged).
- **`Chan(p)` / a session** — a *conversation*: linear, confined to Cure,
  does not survive restart.

Sessions are confined **for free** by an existing rule: message payloads are
restricted to the first-order code universe (BEAM copies messages). A channel
is not a first-order value, so it is not a legal payload. Stated explicitly:
`Pid(m)` is a legal payload type; `Chan(p)` is not (v1 — see delegation, §9.4).
The honest supervision rule follows: **addresses survive restarts,
conversations don't** — a session against a restarted worker is dead and
surfaces as failure (§7).

## 5. Quantities: {0, 1, ω} in the E layer

### 5.1 Placement

The linearity check extends `lib/cure/elab/relevance.ex`'s two-point lattice to
three points. It remains an **E-layer pass; the kernel stays quantity-blind**
(as Idris keeps `LinearCheck` outside its core checker). No kernel change.

- `0` erased — proofs, protocol indices, codes (exactly as today)
- `1` linear — channels, resource capabilities, task handles
- `ω` unrestricted — everything else (default; existing code is untouched)

### 5.2 What the check rejects

For a `1`-binder: use twice (aliasing), use zero times (dropped obligation),
capture in a closure that is not itself one-shot, storage in an ω container,
return from a scope without transfer. The error message must name the protocol
state at the point of loss ("`acct : Account@Open` is dropped on the branch
where …") — source spans preserved through macro expansion.

### 5.3 Linear vs affine

**Overturned decision #3:** the `protocol` macro spec chose affine handles
("an error path may drop a dead handle"). Affine drop of a session endpoint is
precisely the peer-left-blocked-forever leak this design exists to prevent, on
the path where it hurts most. Handles are **linear**; the error path is handled
by elaborator-inserted `cancel` (§7), which notifies the peer. Affine (`≤1`)
remains correct for one thing: **ownership transfer** — a `Task` handed to a
supervisor, which the giver is thereby relieved of. Different type, deliberate
annotation.

### 5.4 Hard prerequisite: bind-once `let`

Cure's `let` inlines its rhs at every use site and drops it at zero uses
(`elaborate_let_block`; see the `bind-once β-redex` finding — this is already
the recorded root cause of three landed bugs, and the Effect spec §5.1 already
special-cases effectful `let` around it). A linear value routed through
substituting `let` is duplicated or discarded *below* the level where the
linearity check runs — the check would pass while the elaborator manufactures
the very aliasing it forbids. **The bind-once `let` fix must land before any
linear value exists.** It is sequenced first in §11 and is independently
motivated (join-point residual).

### 5.5 One-shot closures and linear containers

- A closure capturing a `1` value must itself be typed one-shot (linear arrow
  `-o` or capture restriction); v1 may simply reject capture of linear values
  in ω closures and provide combinators.
- Dynamic topologies need linear containers: `LinList(Chan(p))`, with `lmap`,
  `lfold`, `await_any : (1 ls : LinList(Task(a))) -> Effect(%[a, LinList(Task(a))])`,
  `cancel_all`. This is the acknowledged stdlib cost of linearity, and it buys
  the capability the world-index route could not offer (pools, racing,
  runtime-determined spawn counts).

## 6. Surface syntax

Users never write binds, worlds, or explicit rebinding. The elaborator threads
the linear handle through each statement, retyping it at each protocol
transition; use-after-transition and dropped obligations are linearity errors
with protocol-state diagnostics.

### 6.1 Protocol declaration

```cure
protocol Account
  state Open
    recv Deposit(Int)        -> Open
    recv Balance() reply Int -> Open
    recv Close()             -> Closed
  state Closed
    done
```

Compact linear form (elaborates to explicit states):

```cure
protocol Worker(i: Type, o: Type)
  recv Job(i)
  send Result(o)
  close
```

Protocols may be polymorphic; **codes are always ground** — derived after
instantiation. A code parameterized by a type variable would force `El` to
interpret variables (a staging calculus inside the message universe); rejected.
Message shapes are keyed by `(tag, arity)`; the same `(tag, arity)` with two
different field types is rejected (it is an untagged union whose separability
would be unpredictable — make the discriminator explicit in the payload).
Dependent protocols (later states' payload types depending on earlier
communicated values, e.g. `recv n : Nat` then `recv Vec(Byte, n)`) are in
scope: a `Protocol` code constructor `Depends(shape, El(shape) -> Protocol)`,
elaborated like any other indexed data — ledgered for v1.1, not load-bearing
for the floor.

### 6.2 Server: a receive loop, not a callback triple

```cure
process Account.serve(balance: Int) : Account@Open =
  receive
    Deposit(amt)   -> Account.serve(balance + amt)
    Balance(reply) -> reply(balance)
                      Account.serve(balance)
    Close()        -> done
```

Elaborates to `offer` + total `match`; a missing clause for a message legal in
the current state is a totality error (in Erlang that message sits in the
mailbox forever — that bug class becomes unrepresentable).

### 6.3 Client: straight-line statements

```cure
process main() -> Int =
  acct = spawn Account.serve(0)   # acct : Account@Open
  send acct, Deposit(100)
  b = call acct, Balance()        # b : Int, from ReplyOf lookup
  send acct, Close()              # acct : Account@Closed, discharged
  b
```

When a handle reaches a terminal protocol state, the elaborator inserts the
final `close` at scope end — the user neither writes it nor may omit the path
to it. `close`/`cancel` remain in §4.2 as the elaborated forms.

Compile-time rejections: wrong state (`Deposit` after `Close`), wrong payload
type, dropped handle (spawn without reaching a terminal state or `cancel`),
handle duplication, handle in ω container, handle captured by non-one-shot
closure.

### 6.4 Macro placement

`protocol`, `process`, `accepts`, `resource` are Tier-3/Tier-5 macros of the
planned facility: they derive codes, mint behaviour-shaped modules via
`lift module`, and emit against `Std.Proc`. **Macro output is re-elaborated and
kernel-checked exactly like hand-written code** — a macro cannot emit an
unchecked send any more than a user can. Hygiene, spans, and the no-raw-BEAM
rule come from the macro facility spec unchanged. The macro buys the surface;
the elaborator and kernel buy the guarantee.

## 7. Failure model: let it crash, typed

BEAM reality: `exit(Pid, kill)` is untrappable (AtomVM `nifs.c:4722`,
`context.c:307`); any process can die at any moment. Therefore no session
operation against a peer may be typed infallible. But surfacing that as
`Result` on every operation would be un-BEAM-like noise. Following EGV
(Fowler–Lindley–Morris–Decova, POPL 2019):

- **Failure is an exit, not a value.** `call acct, Balance() : Int`. If the
  peer is dead, the caller unwinds (monitor `DOWN` → exit), exactly like
  `gen_server:call`.
- **Unwinding cancels the ledger.** At a raise, the elaborator knows every
  live linear handle in scope and inserts `cancel` for each; `cancel` notifies
  the peer, whose blocked `recv`/`offer` raises `PeerCancelled` there. The
  theorem this buys: no unwind strands a peer or leaks a session.
- **Recovery is scoped and explicit:**

```cure
process safe_balance() -> Int =
  try
    acct = spawn Account.serve(0)
    b = call acct, Balance()
    send acct, Close()
    b
  rescue
    PeerDown(_) -> 0
```

- `Task(a)` states (`Running/Done/Failed(e)/Cancelled`) type structured
  spawn/await; `await` on a possibly-failing task either raises (default) or
  is matched via `try`. Detached spawn requires transferring the (affine)
  task to a supervisor capability; an unjoined, untransferred task is a
  linearity error.

## 8. Resources: peripherals are linear capabilities, not processes

Peripheral drivers on AtomVM are **not** concurrent: on C3-class chips there is
one scheduler thread (SMP force-disabled, `platforms/esp32/CMakeLists.txt:44-49`)
and port handlers run on it (`scheduler.c:296`). Wrapping I²C in a process buys
zero isolation — the blocking happens on the scheduler, not in the caller.
Therefore, per the bible's layer rule: **peripherals are `resource`s owned by
the Program layer; only genuinely-async drivers (Wi-Fi, sockets — IDF-event-loop
based) become processes talking over session channels.** GPIO interrupts arrive
as messages regardless of anyone's wishes; the Program is simply their listener,
declared via `accepts`.

### 8.1 The drivers already run this discipline dynamically

- GPIO: one interrupt listener per pin, second registration rejected
  (`gpio_driver.c:521`)
- UART: single outstanding read, second gets `{error, ealready}`
  (`uart_driver.c:578`)
- I²C: `transmitting_pid` transaction lock, interleaving rejected
  (`i2c_driver.c:92,196`)

Linear capabilities move each of these to compile time — same guarantee,
build-time.

### 8.2 Resource types with protocol states

```cure
resource I2c
  fn new(1 sda: Gpio(p1), 1 scl: Gpio(p2), freq: Freq) -> Effect(I2c@Idle)
  state Idle
    @blocking(budget: 40.us)   begin : (addr: Addr) -> Effect(Txn@Open)
  state Open (of Txn)
    @blocking(budget: 25.us)   write : (b: Byte)    -> Effect(Txn@Open)
    @blocking(budget: 1200.us) read  : (n: Int)     -> Effect(%[Bytes, Txn@Open])
    @blocking(budget: 40.us)   end   : Effect(I2c@Idle)
```

Note `I2c.new` **consumes the pin capabilities**. After construction,
`Gpio(4)` no longer exists to be `digital_write`-n: pin-mux corruption (writing
a pin that is currently I²C SDA — which no runtime check anywhere prevents,
and which `set_int`'s silent `gpio_set_direction(..., INPUT)` makes easy) is a
type error. This is the strongest peripheral-safety property in the design and
is invisible to the VM.

Long operations are spread across ticks as resource protocol states (the
"continuation is reactor state" pattern): a DS18B20 conversion is
`convert : Idle → Converting` + `poll : Converting → Pending(Converting) |
Done(Float, Idle)`, each tick paying only its budget; the graph runs freely for
the 750 ms. Blocking-before-reading-back is unrepresentable
(`Converting` has no `read`).

### 8.3 Timing as checked arithmetic

Two independent, statically-checkable constraints (both require declared
interrupt-rate bounds per pin, which the `resources` block collects):

1. **Tick budget:** Σ `@blocking` budgets reachable in a reactor's drain phase
   < the reactor's clock period.
2. **Event-queue budget:** max single `@blocking` budget < 16 / Σ declared
   interrupt rates — because the shared ISR event queue is 16 deep
   (`sys.c:70`), shared by all drivers, and the GPIO ISR ignores
   `xQueueSendFromISR`'s result (`gpio_driver.c:650`): a long blocking call
   doesn't just stall the loop, it silently discards interrupt edges.

Budgets are declarations about foreign IDF code — trusted at the boundary like
message contracts, not proven. §10.1 upgrades them from promise to mechanism.

### 8.4 GPIO interrupt honesty

The interrupt message is `{gpio_interrupt, Pin}` — no level, no direction, no
timestamp (`gpio_driver.c:368-385`). Consequences, encoded in the types:

- `Rising` / `Falling` are distinct event sources; `both` is advanced-only
  (its message is genuinely ambiguous; reading the level races the next edge).
- Level triggers (`low`/`high`, `GPIO_INTR_LOW_LEVEL`) are not exposed outside
  `unsafe` — with no mask/ack in AtomVM's path they are an interrupt storm
  aimed at a 16-slot queue.
- The event type promises **soundness, not completeness**: every delivered
  event corresponds to a real edge; not every edge is delivered (queue
  overflow drops silently). Signal-graph code must not assume exact edge
  counts.

## 9. Backend contract (the trusted lowering)

If the elaborator accepts a program, the emitted BEAM code implements the
protocol transitions. Narrow obligations, enumerated:

### 9.1 Wire format: the header token

Every process-to-process session message is
`{'$cure', SessionRef, Seq?, Tag?, Payload...}`:

- **`SessionRef`** — a fresh `make_ref()` minted at session creation (12 bytes
  on ESP32, `term.h:154`). Provenance: a foreign message cannot be confused
  with protocol traffic. Unforgeable by construction (no API constructs a
  chosen ref); **not** unguessable and **not** a security boundary — the
  guarantee is "no accidental confusion," never "no malicious peer" (a
  malicious peer already has untrappable `exit/2`). AtomVM refs are a per-boot
  counter (`globalcontext.h:570-580`): unique per boot, NOT across reboots —
  sessions must never be persisted or assumed stable across restart.
- **`Seq`** — per-session sequence number, **type-directed**: emitted only for
  protocols marked reliable or (later) delegable. Purpose on AtomVM: silent
  message drop under memory pressure is real
  (`mailbox_message_create_from_term` returns NULL on malloc failure and the
  message vanishes, `mailbox.c:243-245`); a sequence gap is the only way a
  receiver can detect it, surfacing as `PeerDown`-shaped failure instead of an
  infinite hang.
- **`Tag`** — elided when the protocol state admits exactly one message
  (session typing pays for its ref: add a ref, delete a tag, ≈wash on the
  wire).

Resources are local capabilities, not sessions: **no token, no refs, no
overhead** — the drain phase emits plain driver calls.

### 9.2 Receive lowering: never scan

AtomVM has no receive-marker optimization (`recv_mark`/`recv_set` removed,
`opcodes.def:228-229`; OTP-24 marker opcodes are no-ops,
`opcodesswitch.h:5486-5516`) and `mailbox_reset` rewinds the cursor after every
match (`mailbox.c:481`) — accumulated junk makes every subsequent selective
receive O(N) from the front. Therefore:

- Single live session: unconditional **head-take** with a catch-all clause —
  O(1); the protocol determines what must be next.
- Multiple live sessions: explicit per-session queues in process state, one
  drain loop — O(1) amortized.
- **The catch-all quarantine clause is mandatory in every emitted receive**:
  it is simultaneously the O(1) guarantee (mailbox never accumulates), the
  foreign-boundary decode (§9.3), and junk hygiene (the property mailbox-type
  systems get as a theorem, delivered here by construction).
- VM selective receive is reserved for the trusted runtime library, never
  emitted for user protocols.

### 9.3 Foreign boundary

- Messages carrying a valid live `SessionRef`: trusted (both ends were
  compiled), no runtime check.
- No token, matches a declared `accepts` contract (`(tag, arity) → payload`
  shapes; flat, no ordering — ordering cannot be enforced on peers we didn't
  compile): **decoded at the door**, O(payload), enters the typed world.
  The AtomVM runtime's own injections (`{gpio_interrupt, P}`,
  `{Ref, sta_disconnected}`, `{'DOWN', ...}`, `{timeout, TRef, M}`) are just
  another foreign peer with a known contract — one mechanism, not two.
- Matches nothing: **drop and count** (quarantine counter readable for
  diagnostics). Junk must not be saved — a chatty foreign neighbour must not
  degrade receives (§9.2).

### 9.4 Failure and cancellation obligations

- Every `spawn` establishes a monitor; `DOWN` translates to the typed failure
  path (§7).
- **Cancellation terms are preallocated at session creation.** Building
  `{'EXIT'|'DOWN', ...}` during termination on an exhausted heap hits
  `AVM_ABORT()` and reboots the board (`context.c:761,794`); failure reasons
  in emitted cancellation messages are constrained to atoms so the term size
  is fixed. This design increases monitor pressure (every session is
  monitored) precisely on the device where the abort path lives — the
  preallocation is what makes that acceptable.
- **Delegation (sending a channel in a message) is excluded from v1** — not as
  a typing restriction but as a lowering gap: BEAM's ordering guarantee is
  per sender-receiver pair only, so even a *linear* transfer of an endpoint
  reorders in-flight messages across the handoff. Lifting it requires an
  explicit drain-and-handoff wire protocol plus mandatory `Seq`; ledgered.

### 9.5 No effect-interpreting emit

The lowering is a **syntax-directed walk over the bind-chain spine** (the
Effect spec's direct-style emit), never an evaluator over effect trees. The
moment emit interprets effect structure to decide what to code-generate, it
becomes the compile-time effect interpreter that sank effects-as-data (its own
§5.4: "the TCB doesn't shrink; it relocates and grows"). Validator backstops
from the Effect spec (`no_effect_in_erased_position`, `effect_ops_known`, …)
apply unchanged; `codes_erased` extends to protocol states, quantities, and
budgets — none may survive into emitted code.

## 10. AtomVM obligations (patches we own)

The clone already carries local patches as a matter of course; these join them.

1. **Bounded driver timeouts (highest-leverage item in this design).** I²C
   uses `portMAX_DELAY` on the scheduler thread (`i2c_driver.c:247,432,535`);
   SPI busy-polls (`spi_driver.c:359`, marked TODO upstream). Patch: the
   lowering passes each op's **declared `@blocking` budget as the driver
   timeout**. This converts the worst failure mode on the chip (wedged bus →
   frozen scheduler → overflowed event queue → eaten GPIO edges → watchdog
   reboot) into a typed, `rescue`-able error, and upgrades §8.3's budgets from
   promise to mechanism.
2. **Audit `i2c_resource`** (`i2c_resource.c:905`) — the newer NIF-collection
   I²C API — before committing the resource lowering to the port driver; its
   blocking behaviour was not audited.
3. (Optional, later) event-queue depth/overflow counter exposure, so §8.4's
   soundness-not-completeness caveat is at least observable.

## 11. Sequencing

Preconditions unchanged from the process-algebra spec: classic rip-out, macro
facility, inert `Effect(T)` (0.34), rungs 1–2 (externs, then sealed
`Std.Otp` + codes floor). Then this design, strictly ordered:

1. **Bind-once `let`** (§5.4) — prerequisite for any linear value; lands
   independently (already motivated by the join-point residual).
2. **{0,1,ω} in the E layer** (§5) — extend `relevance.ex`; kernel untouched.
3. **`Chan(p)` + `Std.Proc` over `Effect(T)`** (§4) + the `protocol`/`process`
   macros (§6) + EGV failure (§7) + backend contract (§9). Kernel untouched.
4. **Resources** (§8) — with the reactive roadmap's `resource` (0.35) /
   `program` (0.37) layers; AtomVM timeout patch (§10.1) lands here.
5. Ledger: dependent protocols (`Depends`), delegation (drain-and-handoff +
   `Seq`), linear-container ergonomics, distribution (out of scope; refs are
   per-boot, nodes unmodeled).

Deadlock freedom ships as an **out-of-TCB lint** (acyclicity/priority analysis
over the session-dependency graph), same trust shape as the Z3 guard lint —
alarms without kernel exposure. Mailbox types (de'Liguoro–Padovani; Pat) remain
the named future for whole-mailbox reasoning: rejected for now because the BEAM
mailbox is an open world (the theorem's premise fails), the checker is a second
type system outside the kernel, and it still needs quasi-linearity — but §9.2's
emitted demultiplexer implements their operational idea, and junk-freedom
arrives by construction.

## 12. Overturned decisions (explicit, per repo convention)

1. **Rung 3 indexed bind (`Effect(pre,post,T)`) — deleted** (§4.1). The
   parameterized monad simulated missing linearity; with `1` planned, the
   kernel-touching item disappears. Rungs 0–2 of that spec stand.
2. **"Indices, not linear types" — reversed** (§4.1), and its stated authority
   (`post-parity-teardown-batch`) never mentioned linear types; the citation
   was incorrect.
3. **`protocol` macro's affine handles — now linear + elaborator-inserted
   `cancel`** (§5.3); affine reserved for ownership transfer.
4. **Failure surfaced as per-op `Result` (this design's own earlier draft
   direction) — replaced by EGV exit + scoped `rescue`** (§7), matching BEAM
   idiom.

## 13. Non-negotiable invariants (checklist)

Safe Cure code cannot: spawn an unchecked process; send an unchecked message to
a typed process; receive an unchecked message as protocol traffic (token +
boundary decode); duplicate or reuse a consumed channel/resource (linearity);
silently drop a protocol obligation (linearity + inserted `cancel`); smuggle a
session through a message (first-order payload rule); bypass checking via
macros (re-elaboration); hide behaviour in an opaque effect the types don't
mention (the effect's type now names the protocol); write a pin owned by a bus
(consumed capability); assume delivery ordering BEAM doesn't provide (per-pair
only; delegation excluded until §9.4 lifts it); assume interrupt completeness
(§8.4).

## 14. Honest limits

- The raw mailbox stays dynamically typed; the quarantine boundary governs it,
  best-effort, with drop-and-count semantics.
- Foreign-boundary trust is irreducible: `accepts` contracts and `@blocking`
  budgets are declarations about code we didn't compile.
- The token is provenance, not security; refs are per-boot.
- Liveness is not proven: protocol *safety* is checked; *completion* holds
  only under fairness/termination assumptions (deadlock lint is advisory);
  `await` against an unfair peer can block until its timeout/monitor fires.
- Budget arithmetic trusts declared interrupt-rate bounds.
- Function colouring exists: a pure `fn` cannot send. The macro surface makes
  effectful code pleasant, not ambient. The sanctioned escape for foreign
  needs remains the user's own explicit `@extern` (sealed-raw-base
  convention), greppable and deliberate.
