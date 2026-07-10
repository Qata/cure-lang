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

### 5.4 Hard prerequisite: `let` must stop substituting

Cure's `let` inlines its rhs at every use site and drops it at zero uses
(`elaborate_let_block`, `lib/cure/elab/elaborator.ex:1141-1148` — the comment
says so outright; see the `bind-once β-redex` finding, already the recorded
root cause of three bugs, and the Effect spec §5.1, which special-cases
effectful `let` around it). A linear value routed through substituting `let` is
duplicated or discarded **below** the level where the linearity check runs: the
check counts one surface occurrence and passes, while the elaborator
manufactures the very aliasing it just certified impossible. Two processes get
spawned where the types proved one.

**The β-redex itself already exists** — `elaborator.ex:3983-3993` builds
`{:app, {:lam, dom, body}, rhs}` from existing Core formers, landed in 809823d.
It is gated on `Enum.any?(rest, &binds_any?(&1, [name]))`, i.e. it fires only
when substitution would capture. The work is the gate, not the construction.

Flipping the gate unconditionally regresses **dependent** `let`. Cure's
`Context` entries are types, never values (`core/context.ex:15`:
`defstruct types: [], length: 0, …`), and Core has no `let` former (six nodes).
A λ-bound `n` gives `n : Nat`, not `n ≡ 3`, so `let n = 3 ⏎ v : Vector(Int, n)`
gets stuck. Substitution keeps the *definition* and loses *sharing*; a β-redex
keeps *sharing* and loses the *definition*.

**This is a false dilemma created by the missing node.** Idris 2 has no such
choice: `Let` is a `Binder` carrying its value *and* a quantity
(`Core/TT/Binder.idr:93-98`, `Let : FC -> RigCount -> (val : type) -> (ty : type) -> Binder type`),
appearing under the single `Bind` term node (`Core/TT/Term.idr:97-104`).
ζ-reduction unfolds it on demand (`Core/Normalise/Eval.idr:124-130`, and
`:242-244`: a `Local` whose binder is a `Let` evaluates to its value), so the
value is reachable for conversion while occurring exactly once in the term.
Lean has the same node (`Expr.letE` + `LocalDecl.ldecl` + ζ/`zetaDelta`). Agda
takes the other road — no `Let` in internal syntax, let-bindings in the
checking environment, substituted into terms — which is what Cure does today,
and pays the same duplication cost. (The Idris claims were read from
`~/Develop/Idris2` this session; the Lean/Agda claims are from memory.)

Two consequences fix the plan:

**(a) Quantity-gated bind-once — sound, zero kernel change, sufficient for
linear channels.** Extend the `cond` from "shadowing" to "shadowing **or** the
binder is quantity `1` or effect-typed." This is not a heuristic: QTT's own
rule checks a binder's *type* at quantity `0` (Idris `LinearCheck.idr:374-377`
— `lcheck erased erase env ty`), so a `1` binder can never occur in a type or
index position, and a β-redex can never strand a dependent type. Every linear
binder is unconditionally safe to bind once.

**(b) A `Let` binder in Core is the real fix, and it is what (a) is a bridge
to.** (a) leaves `ω` dependent `let` substituting, so term duplication — and
with it the still-open join-point bug — survives. A value-carrying `Let` with a
`RigCount`, plus ζ, kills both and aligns Cure with Idris and Lean
simultaneously, satisfying the standing TCB-change condition. Cost is bounded
and enumerable: one Core node through `term?/1`, `subst/3`, `Eval`, `Conv`,
`Normalise.nf_struct`, `Quote`, `Serialize`, `Validator`, plus Antigen coverage
cells. Note Idris gets this cheaply because `Bind` is one node parameterized by
`Binder`; Cure has separate `:pi`/`:lam` tags, so `:let` is a third — price
that before committing.

Sobering note from the reference implementation: `LinearCheck.idr:227-232`
catches `LinearMisuse` and *retries the binder as linear*
(`setMultiplicity b linear`). Production linearity in a dependently-typed
language is not pristine; do not plan as though ours will be.

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

### 6.4 Containers: `fsm`, `actor`, `sup`, `app`

The classic containers are **three different kinds of thing**, indiscriminately
compiled to processes today (`Cure.FSM.Compiler`, `Cure.Actor.Compiler`, over an
ETS-backed runtime). Under the layer rule they separate:

**`fsm` reduces.** It is a protocol plus a total pure transition function, and
needs a process only to be *addressable*. `Red --timer--> Green` already *is* a
session protocol; the macro expands `*` into a clause per state and derives the
reducer. The payoff is on the caller:

```cure
process drive() -> Unit =
  light = spawn TrafficLight.serve   # light : TrafficLight@Red
  send light, timer()                # light : TrafficLight@Green
  send light, emergency()            # light : TrafficLight@Red
```

The handle's type *is* the machine's state; `Std.Fsm.state/1` (today a runtime
query returning a bare `Atom`) becomes a compile-time fact and is retired.

**Limit — this holds only while the handle is linear.** A registered, ω-shared
fsm cannot let any client know the state; its protocol degenerates to the flat
message-set floor ("legal in *some* state"). Sharing costs a runtime query
returning a dependent pair:

```cure
%[s, chan] = Fsm.reopen(light_pid)   # Σ s : State. Chan(TrafficLight@s)
```

This is the rung-2-floor / rung-3-ceiling distinction surfacing as an
ergonomics fact rather than a slogan.

**`actor` is a process.** `on_message` clauses become a `receive` loop over a
protocol; the untyped `notify(%[:tick_at, n])` firing at an implicit `:caller`
becomes `reply(n) : Int` read from the protocol. Reply-less messages cannot be
awaited; a missing clause is a totality error (today the message rots in the
mailbox). `Std.Actor.notify/1` and the implicit `:caller` capture are retired.

**`sup` owns addresses, not conversations.**
`Supervisor([clock: Pid(Clock), …])`; `Sup.child(sup, :clock) : Effect(Pid(Clock))`
yields an ω address, and `Session.open(pid) : Effect(Chan(Clock@Ready))` mints
the linear conversation. A crash-and-restart kills the session, not the address:
a `call` on the stale channel raises `PeerDown` rather than returning a stale
reply or hanging. Children are the **affine** case (§5.3) — the supervisor owns
them, so the spawner is relieved of the join obligation.

**`app`** owns the root supervisor capability, linearly, for the VM's lifetime.

### 6.5 Macro placement

`protocol`, `process`, `accepts`, `resource` are Tier-3/Tier-5 macros of the
planned facility: they derive codes, mint behaviour-shaped modules via
`lift module`, and emit against `Std.Proc`. **Macro output is re-elaborated and
kernel-checked exactly like hand-written code** — a macro cannot emit an
unchecked send any more than a user can. Hygiene, spans, and the no-raw-BEAM
rule come from the macro facility spec unchanged. The macro buys the surface;
the elaborator and kernel buy the guarantee.

### 6.6 Syntax rationale: arrows describe the protocol, statements drive it

Considered and rejected: an arrowised surface (`inbox -> message` for receive,
`outbox <- message` for send). Four reasons, ordered by weight.

**Infix invites nesting; typestate forbids it.** `send acct, Deposit(100)` is a
statement and cannot be nested. `acct <- Deposit(100)` is an expression, so
`f(acct <- Deposit(100), acct)` parses — and the second `acct` has no
principled meaning (pre- or post-transition?). Argument evaluation order would
become protocol-observable. Cure already demonstrates this failure: the
existing Melquiades operator `<-|` / `✉` (`lexer.ex:1075,1096`,
`types/checker.ex:1528-1534`) is documented as returning *the message's type*
"so `<-|` chains and binds naturally in `let`/block contexts" — i.e. a send
whose effect on the handle is invisible. That is exactly the shape typestate
must forbid. See §12.5.

**`receive` is not a binary operation.** A session receive is an n-way `offer`
over every message legal in the current state; there is no single "message" to
arrow into. `inbox -> message` can express only a one-message state — precisely
the case where tag elision already applies, i.e. the case needing syntax least.
Send is naturally infix; receive is naturally a block.

**`->` would collide at the site of use.** `->` (`:arrow`, `lexer.ex:1154`)
already means function types, match arms, fsm transitions, and protocol
transitions. Inside a `receive` block, arms already use `->`; a second meaning
on adjacent lines is collision, not overloading.

**`<-` reads backwards to the target audience.** In Haskell `do`, Elixir `with`,
and BEAM comprehensions, `x <- e` *binds a result* — it reads as receive. In Go,
`ch <- v` sends. Either convention misleads half the room, and the misled half
is the Elixir refugee this surface exists for. (Occam/CSP `!`/`?` avoids the
ambiguity but makes a checked, stateful send look identical to Erlang's
unchecked one.)

**The layer argument, which is decisive.** Per the bible's rule, flow computes
and only Program performs effects. The pure dataflow layer already owns the
arrow aesthetic (`|>` `:pipe`, `Signal.map`, `zip_with`, `fold`) — correctly,
because arrowised composition composes *stateless* signal functions. A session
handle is nothing but state. Keeping **pipes/arrows = pure dataflow, statements
= effects** makes the syntax carry the layer boundary the whole design rests on,
at zero cost. Spending that distinction on an operator would blur it.

**The rule, therefore:** arrows *describe* the protocol (`recv Deposit(Int) ->
Open`, the same arrow as `Red --timer--> Green`); statements *drive* it (`send`,
`call`, `receive`).

**Retained from the proposal — type-directed dispatch, but not type-directed
syntax.** The protocol already decides whether a message carries a reply, so a
`call` on a reply-less message (and a `send` on a replying one) is a type error.
`send` and `call` nonetheless stay distinct keywords, for a target-specific
reason: **`call` blocks and `send` does not.** On a single-scheduler C3 that is
the difference between a 10 µs statement and one that yields until a peer
replies — the same distinction as `gen_server:call` vs `cast`, and exactly what
`@blocking(budget:)` (§8.3) exists to make visible. Collapsing them into one
operator would hide the most latency-relevant fact in an MCU program at its call
site.

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

### 9.2 Receive lowering: never scan (when we own the mailbox)

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
  systems get as a theorem, delivered here by construction). For a process
  lowered to a behaviour (§9.6), **`handle_info` *is* this clause** — it is not
  an invention, it is the callback OTP already provides, now generated and
  counted rather than hand-written.
- VM selective receive is never emitted for a process that **owns its own
  mailbox**.

**Qualification (the O(1) claim is not unconditional).** A Cure process that is
itself supervised is a behaviour (§9.6), so OTP owns its mailbox and it cannot
run a head-take inside a callback. Its `call` lowers to `gen_server:call`,
inheriting OTP's ref-based **selective receive** — the O(N) path on AtomVM. This
is tolerable because `handle_info` keeps such a mailbox drained, so N is
normally zero; but the guarantee is conditional and must not be discovered on
hardware. **The O(1) head-take guarantee holds only for processes that own their
own mailbox.**

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

### 9.6 Behaviour lowering: session loops become `gen_server`s

A session-typed `receive` loop lowers naturally to a bare tail-recursive
Erlang loop, which would be smaller and faster than `gen_server` on AtomVM.
**This is wrong and must not be done.** A bare loop cannot be supervised: OTP
supervisors require children started via `proc_lib` that speak the `sys`
protocol. Emitting raw loops loses supervision, `sys:get_state`, and release
handling — for exactly the containers whose purpose is supervision.

Therefore a `process` that is a supervised container lowers **into** a
`gen_server`, with the protocol state as the server state: reply-carrying
clauses become `handle_call`, reply-less clauses become `handle_cast`, and
`handle_info` is the quarantine clause (§9.2).

```erlang
handle_call({'$cure', Sid, tick}, _From, N) -> {reply, {'$cure', Sid, N + 1}, N + 1}.
handle_cast({'$cure', _Sid, reset}, _N)     -> {noreply, 0};
handle_cast({'$cure', _Sid, stop},   N)     -> {stop, normal, N}.
handle_info(Other, N) -> 'Cure.Quarantine':drop(Other), {noreply, N}.
```

Three consequences, all in the design's favour:

- **`handle_info` *is* the quarantine clause** (§9.2) — inherited, not invented.
- **`gen_server:call`'s exit-on-peer-death *is* the EGV failure model** (§7).
  `PeerDown` is inherited from OTP, not implemented.
- **No defensive catch-all on typed clauses.** `handle_cast` gets no
  `handle_cast(_, S) -> {noreply, S}` fallback, because the type system proved
  no other tagged message can arrive on a valid `Sid`. The guarantee is visible
  as an *absence* in the emitted source; every equivalent handler written today
  needs that wildcard because nothing knows what may arrive.

Supervisors lower essentially as they do today (`supervisor` behaviour, child
specs, strategies) — unchanged, because supervision operates on **addresses**,
and addresses were never the thing that needed typing (§4.4, §6.4).

`fsm` containers with a linear owner need no process at all (§6.4); only the
addressable form lowers to a behaviour, with the protocol state as the server
state and the transition clauses checked total over (state × legal event).

Retired by this lowering: `Std.Actor.notify/1` and the implicit `:caller`
capture; `Std.Fsm.state/1` returning a bare `Atom`; the ETS-backed
`Cure.Actor.Runtime` (state lives in the behaviour); every defensive wildcard
clause on a typed channel; the Melquiades operator `<-|` / `✉` as currently
typed (§12.5); and the string-based `Cure.FSM.Compiler` / `Cure.Actor.Compiler`
codegen, replaced by macro expansion into ordinary checked Cure.

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

1. **Core `Let` binder with ζ and a quantity** (§5.4b) — the Idris/Lean node.
   Kills term duplication (and the open join-point bug) at the root, and makes
   dependent `let` and bind-once coexist rather than trade off. Pre-approved
   under the standing TCB-alignment condition. *If deferred*, the sound bridge
   is §5.4a: quantity-gated bind-once, zero kernel change, exact rather than
   heuristic (QTT checks binder types at quantity `0`). Either path unblocks
   step 2; only (b) also closes the join-point residual.
2. **{0,1,ω} in the E layer** (§5) — extend `relevance.ex`; kernel stays
   quantity-blind for *usage* (Idris keeps `LinearCheck` outside its core
   checker), though `Let`/`Pi`/`Lam` carry a quantity as data, as in Idris.
3. **`Chan(p)` + `Std.Proc` over `Effect(T)`** (§4) + the `protocol`/`process`
   macros (§6) + EGV failure (§7) + backend contract (§9). Kernel untouched.
4. **Resources** (§8) — with the reactive roadmap's `resource` (0.35) /
   `program` (0.37) layers; AtomVM timeout patch (§10.1) lands here.
5. Ledger: dependent protocols (`Depends`), delegation (drain-and-handoff +
   `Seq`), linear-container ergonomics, distribution (out of scope; refs are
   per-boot, nodes unmodeled).

Steps 1 and 2 partially invert the ordering asserted in the first draft of this
spec: the prerequisite is smaller than claimed (the β-redex is built), and the
gate that makes it exact is *derived from* the quantity lattice rather than
preceding it.

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
5. **The Melquiades send operator `<-|` / `✉` — retired, or retyped.** Its
   current semantics (`types/checker.ex:1528-1534`) return *the message's* type
   so it "chains and binds naturally in `let`/block contexts." Under typestate a
   send must yield the **next-state channel**; an operator that yields the
   message makes the handle's transition invisible and permits nesting a
   protocol transition inside an expression (§6.6). Its reserved error codes
   E044 (Not A Pid), E045 (Untyped Send) and E046 (Inbox Mismatch) are subsumed
   by the protocol check, which is total rather than `@strict_inbox`-gated.
   If the spelling is kept, `<-|` must be statement-position-only and typed
   `(1 c : Chan(Send(m, next))) -> El(m) -> Effect(Chan(next))`.

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
- **The O(1) receive guarantee is conditional** (§9.2): it holds for processes
  that own their own mailbox. A supervised process is a behaviour, so its
  `call` lowers to `gen_server:call` and inherits OTP's ref-based selective
  receive — O(N) on AtomVM, with N normally zero because `handle_info` drains.
- **Static fsm typestate requires a linear owner** (§6.4). An ω-shared fsm
  degrades to the flat message-set floor; recovering its state needs a runtime
  query returning a dependent pair.
- Function colouring exists: a pure `fn` cannot send. The macro surface makes
  effectful code pleasant, not ambient. The sanctioned escape for foreign
  needs remains the user's own explicit `@extern` (sealed-raw-base
  convention), greppable and deliberate.
