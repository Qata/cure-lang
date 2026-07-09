# Typed BEAM Process Algebra — Correct-by-Typing OTP Access

**Date:** 2026-07-09
**Status:** design (operator-directed). Consumes the `Effect` inert type former
([`2026-07-09-effect-type-former-design.md`](2026-07-09-effect-type-former-design.md));
supplies the typed surface the macro facility's fsm/actor/sup/app reimplementations
([`macros/2026-07-08-macro-facility-design.md`](macros/2026-07-08-macro-facility-design.md)
§14) emit against.

**Decision (operator, 2026-07-09):** the BEAM process/OTP model is exposed to
Cure programs as a **typed algebra** — precise, dependent, indexed operation
signatures that make *incorrect use of the BEAM ops a compile error* — rather
than as a thin layer of `@extern` declarations with asserted signatures. The
typed algebra is the **only sanctioned surface**; the raw foreign base it is
built over is sealed (`unsafe`, internal).

---

## 1. Purpose and locked decisions

Concurrency is where dependent types pay off most: the dominant real bug class
on BEAM is *sending a process a message it does not handle* and *using a reply
at the wrong type*, both invisible on the dynamically-typed substrate. Cure can
turn them into type errors. The operator locked:

1. **Type the whole process/OTP surface as an algebra**, not a set of loosely
   typed externs. Misuse is caught by the kernel checking the algebra, not by
   trusting a table.
2. **Rich types, inert values.** This composes with — does not fight — the inert
   `Effect` former: `send` still *computes* nothing at type-check time; only its
   *type* becomes precise. Inertness (Effect spec §3.2) is untouched.
3. **Minimal trust, maximal checking.** The algebra is ordinary kernel-checked
   Cure over a tiny raw base typed at honest BEAM signatures. The TCB does **not**
   grow; it shrinks relative to "one asserted extern per operation."
4. **The typed algebra is the only sanctioned surface.** The raw base is
   `unsafe` and internal to `Std.Otp`; deliberate raw access means the user
   writes their own `@extern`.
5. **Floor now, ceiling deferred.** v1 delivers *typed channels* (typed pids,
   dependent call/reply, behaviour conformance) over the existing non-indexed
   `Effect(T)`. *Session/state discipline* (indexed effects) is designed-in as an
   extension point and landed later (§8).

## 2. Architecture — two layers over `Effect`

```
  user / macro-emitted code
        │  programs only against …
        ▼
  ┌─────────────────────────────────────────────┐
  │  Typed process algebra   (Std.Otp)           │  ← ordinary CHECKED Cure
  │  Pid(M), GenServer(C,K,I), send, call, …     │    (kernel verifies it)
  └─────────────────────────────────────────────┘
        │  narrows / is defined in terms of …
        ▼
  ┌─────────────────────────────────────────────┐
  │  Raw foreign base  (Std.Otp.Raw, unsafe)     │  ← the ONLY trust boundary
  │  raw_send : RawPid -> Any -> Effect(Unit) …  │    (honest permissive types)
  └─────────────────────────────────────────────┘
        │  lowers to …
        ▼
  stock erlang:/gen_server:/gen_statem: BIFs  +  the inert Effect former
```

The kernel checks that (a) the algebra is internally consistent and (b) user
code uses it correctly. The *only* asserted-not-proven facts are the raw base's
base signatures — irreducible, because you cannot prove properties of a foreign
runtime, only state its interface honestly.

## 3. The trust boundary

### 3.1 Raw base — sealed, `unsafe`, honest

A private module `Std.Otp.Raw`, every function an effect-typed `@extern` at its
**most permissive honest** BEAM type. It is the sole consumer of the
process/OTP BIFs and the sole thing tagged `unsafe` in this design.

| raw op | honest type | BEAM |
|---|---|---|
| `raw_send` | `RawPid -> Any -> Effect(Unit)` | `erlang:send/2` |
| `raw_self` | `Effect(RawPid)` | `erlang:self/0` |
| `raw_call` | `RawPid -> Any -> Effect(Any)` | `gen_server:call/2` / `gen_statem:call/2` |
| `raw_cast` | `RawPid -> Any -> Effect(Unit)` | `gen_server:cast/2` / `gen_statem:cast/2` |
| `raw_start` | `Module -> Any -> Effect(RawPid)` | `gen_server:start_link` / `gen_statem:start_link` |
| `raw_stop` | `RawPid -> Effect(Unit)` | `gen_server:stop` / `gen_statem:stop` |
| `raw_send_after` | `Int -> RawPid -> Any -> Effect(TRef)` | `erlang:send_after/3` |
| `raw_cancel_timer` | `TRef -> Effect(Unit)` | `erlang:cancel_timer/1` |
| `raw_spawn` / `raw_spawn_link` | `(Effect(Unit)) -> Effect(RawPid)` | `erlang:spawn` / `spawn_link` |
| `raw_exit` | `RawPid -> Any -> Effect(Unit)` | `erlang:exit/2` |
| `raw_link` / `raw_unlink` | `RawPid -> Effect(Unit)` | `erlang:link/1` / `unlink/1` |
| `raw_monitor` / `raw_demonitor` | `RawPid -> Effect(MRef)` / `MRef -> Effect(Unit)` | `erlang:monitor/2` / `demonitor/1` |
| `raw_process_flag` | `Atom -> Any -> Effect(Any)` | `erlang:process_flag/2` |
| `raw_is_alive` | `RawPid -> Effect(Bool)` | `erlang:is_process_alive/1` |
| `raw_register` / `raw_unregister` / `raw_whereis` | `Atom -> RawPid -> Effect(Unit)` / `Atom -> Effect(Unit)` / `Atom -> Effect(RawPid)` | `erlang:register/2` / `unregister/1` / `whereis/1` (raw registry, **not** Elixir `Registry`) |

`RawPid`, `TRef`, `MRef`, `Module` are opaque foreign-handle types declared
here. Device/user FFI (`gpio`, `uart`, …) is *not* part of this base — it stays
ordinary user `@extern`, unrelated to the process algebra.

### 3.2 Sealing mechanism

`Std.Otp.Raw` is not re-exported by `Std.Otp`. Its `@extern`s carry the
`unsafe` tag (holes/`unsafe` taxonomy). The only module that imports it is
`Std.Otp` itself, whose typed wrappers (§4) narrow the honest permissive types
to the precise ones. Consequences:

- User and macro-emitted code cannot reach `raw_*` — the typed algebra is the
  path of least (and only casual) resistance.
- A genuine raw need is met by the user's **own** `@extern`: explicit in their
  source, their asserted signature, greppable, deliberate — strictly better
  than a shared casual bypass. This directly answers the classic-ripout's
  "wayward agent wires to the unsound path because it exists" concern: there is
  no ambient untyped `send` to grab.

## 4. The floor — typed channels (v1)

Built entirely as checked Cure in `Std.Otp` over §3.1. No new monad structure;
`Effect(T)` is used exactly as the Effect spec locks it.

### 4.1 Typed pids

A pid carries the protocol of the messages it accepts:

```cure
type Pid(m)          # opaque; wraps a RawPid, phantom-indexed by protocol m
```

`send` may only deliver a message the target actually handles:

```cure
fn send(p: Pid(m), msg: m) -> Effect(Unit) =
  raw_send(unwrap(p), msg)          # narrowing: m ≤ Any is sound by construction
```

Sending the wrong shape is now a **type error**, not a silently-dropped message.

### 4.2 `self` — typed by the ambient protocol

`self` must yield a pid typed by *this* process's own mailbox protocol, which is
known only inside a behaviour that declares it (§4.4). Therefore:

- Inside a behaviour whose protocol is `M`, `self : Effect(Pid(M))`.
- Outside any behaviour context, `self` is unavailable at a typed protocol; a
  program that needs a bare handle there uses `self_raw : Effect(Pid(Unknown))`
  (a pid at the empty/unknown protocol — you may pass it, not `send` to it).
  Whether `Pid(Unknown)` is the right encoding or bare `self` should simply be a
  type error outside a declared context is ledgered (§11.3); §4.2 states the
  tentative choice, not a locked one.

The ambient protocol is threaded by `lift module`'s behaviour elaboration (§6),
not inferred globally.

### 4.3 Dependent call / reply

The reply type is a function of the request. `ReplyOf` is a type-level map from
request constructor to reply type, declared alongside the server:

```cure
type ReplyOf(req)                    # type family: request → reply type

fn call(s: GenServer(c, k, i), req: c) -> Effect(ReplyOf(req)) =
  narrow(raw_call(unwrap(s), req))

fn cast(s: GenServer(c, k, i), msg: k) -> Effect(Unit) =
  raw_cast(unwrap(s), msg)
```

`call` returning `ReplyOf(req)` is where dependent typing earns its keep: the
`GenServer.call`-returns-`Any` hole is closed. `GenServer(c, k, i)` indexes a
server handle by its call / cast / info channels.

### 4.4 Behaviour conformance

`start_link` for a behaviour yields a handle typed by that behaviour's declared
channels, so the handle and the callbacks provably agree:

```cure
fn start_link(spec: ServerSpec(c, k, i), arg: a) -> Effect(GenServer(c, k, i)) =
  narrow(raw_start(module_of(spec), arg))
```

The `§14.3` callback ADTs supply `(c, k, i)`: `handle_call` handles `c` and
produces `ReplyOf`, `handle_cast` handles `k`, `handle_info` handles `i`. A
callback whose handled type disagrees with the channel index fails checking —
the conformance is structural, not convention.

## 5. What lives where (reconciles the earlier two-list question)

- **Kernel / `Effect` former:** the four structural nodes + `extern_call`
  (Effect spec §3). No process ops. No stock BIFs.
- **`Std.Otp.Raw` (sealed, `unsafe`):** the raw base (§3.1) — the honest foreign
  interface, the one trust boundary.
- **`Std.Otp` (checked, sanctioned):** the typed algebra (§4) — what everything
  else programs against.

The provenance rule from the prior turn still holds and is now sharper: a stock
BIF is *never* a kernel/vocab entry — it is a raw-base extern, wrapped by the
typed algebra. The named-op vocabulary in the effect table is reserved for BIFs
*we* implement natively, of which the process algebra needs **none**.

## 6. Macro-facility integration

fsm/actor/sup/app macros emit against the typed algebra, never the raw base:

- Callback bodies (`on_message`, `on_transition`, …) are checked Cure using
  `send`/`call`/`cast` at typed channels — misuse in a handler is a compile
  error like any other.
- Convenience-export wrappers (`start_link`, `send_event`, `get_state`) — today
  templated `GenServer.call`/`cast` bodies — become thin typed-algebra calls
  with `Effect(...)` returns, generated by the macro.
- `lift module`'s `behaviour` declaration is what establishes the ambient
  protocol `M` (§4.2) and the channel indices `(c, k, i)` (§4.4) for the minted
  module, threading them to the callbacks and to `self`.

The macro output is re-elaborated like hand-written code (facility §9), so it is
held to the same typed-algebra discipline — the macro cannot emit an untyped
send any more than a user can.

## 7. Honest limits (state up front; do not over-promise)

1. **The mailbox is dynamically typed.** A BEAM process can receive *anything*,
   and the runtime injects `{'EXIT', …}`, monitor `DOWN`, and system messages
   the type does not describe. The algebra governs **what you send through typed
   channels**, not the raw mailbox — the same opt-in boundary Akka Typed draws.
   `handle_info`'s `i` channel is therefore a best-effort declared subset, not a
   totality claim over the mailbox.
2. **Foreign-boundary trust is irreducible.** That `erlang:send` truly delivers
   an `m`-shaped term, that `gen_server:call` truly returns `ReplyOf(req)`, is
   asserted by the raw base's honest signatures — provable only about Cure code,
   never about the VM.
3. **Narrowing soundness rests on `m ≤ Any`.** Every typed wrapper narrows a
   permissive raw type to a precise one; this is sound because the precise type
   is a subtype of `Any` — but it is a *coercion the algebra author writes*, and
   the release validator (§10) checks no wrapper widens in the wrong direction.

## 8. The ceiling — session / state discipline (deferred, designed-in)

The high-value extension: encode protocol *ordering* and *lifecycle* — "no
`send` after `stop`", per-state legal operations, request/response session
shape. This is the FRP index-algebra generalization
([`frp`](2026-07-04-identity-type-as-inductive.md) lineage) applied to
concurrency, and it needs an **indexed effect**:

```
Effect(pre, post, T)          # a computation legal from protocol-state `pre`,
                              #   leaving state `post`, producing T
```

- Operations gain pre/post indices: `stop` moves to a `Stopped` index at which
  `send`'s precondition is unavailable → post-stop send is a type error.
- The discipline rides on **indices**, matching FRP's `Dec`/`Init` — **not**
  linear types (out per the post-parity teardown). No linearity machinery
  required.
- This is a parameterized monad, strictly more than the inert non-dependent
  `Effect(T)` v1 locks. It is real elaborator + kernel surface (indexed bind)
  and a research-grade area (session types on BEAM: Links, Idris `ST`, typed
  protocols). Landed once the floor is proven, not before.

v1 must not foreclose it: the floor's `Pid(m)` / `GenServer(c,k,i)` indices are
the same handles the ceiling refines with state indices, so the ceiling is an
*enrichment* of the floor's types, not a rewrite.

## 9. Relationship to the `Effect` spec

This spec **consumes** `Effect`; it does not extend the former. One edit lands
on the Effect spec as a consequence (§3.3 there):

- The stock BIFs currently listed in the trusted signature table (`send`,
  `self_pid`, `sleep`, `print`) move **out** of the table into `Std.Otp.Raw`
  (as raw externs) and `Std.Otp` (as typed wrappers). The table's residual role
  is precisely "BIFs we implement natively" + the generic `extern_call`.
- `TRef` (and now `MRef`) are declared in `Std.Otp.Raw`, not fixed by the table.

## 10. Validator / release backstops (trusted)

At the single emission gate (Effect spec §8 style):

1. `otp_raw_sealed` — no module other than `Std.Otp` references `Std.Otp.Raw`
   (the seal is enforced, not merely conventional).
2. `no_widening_narrow` — a typed wrapper's result type must be a subtype of the
   raw op's result (narrowing only); a wrapper that widens is rejected.
3. `unsafe_confined` — every `unsafe` process extern is inside `Std.Otp.Raw`.

## 11. Ledger (open decisions)

1. **`Pid(m)` variance / subtyping** — is `Pid` covariant, contravariant, or
   invariant in `m`? (Contravariant is the Akka-Typed-correct answer — a pid
   accepting a wider protocol is usable where a narrower is wanted — but Cure's
   subtyping story for indexed types must be pinned first.)
2. **`ReplyOf` as type family vs. per-request GADT** — mechanism for the
   request→reply map; interacts with how dependent `call` elaborates.
3. **`self` outside a behaviour** — is `Pid(Unknown)` an empty protocol, or is
   `self` simply a type error outside a declared context? Ergonomics call.
4. **`handle_info` / system messages** — how much of `{'EXIT',…}`/`DOWN` to
   surface in the `i` channel vs. leave as an acknowledged untyped remainder.
5. **Registry typing** — `whereis` returns a `RawPid`; recovering a typed
   `Pid(m)` from a name needs a name→protocol association (a typed registry
   facade) or an explicit user-asserted cast. Design when named-process use
   returns.
6. **Ceiling scheduling** (§8) — the indexed-effect monad is its own spec; queue
   after the floor ships and the fsm/actor macros are proven against it.
7. **`unsafe` tag surface** — reuse the holes/`unsafe` taxonomy's keyword
   verbatim for the raw base, or a dedicated `@extern(..., unsafe: true)` form.

## 12. Non-goals

- **Not** the indexed-effect ceiling (§8) — designed-in, deferred.
- **Not** typing the raw mailbox or system messages beyond the declared channels
  (§7.1).
- **Not** linear/affine resource tracking for timer/monitor refs — indices, not
  linearity.
- **Not** touching the inert-`Effect` kernel contract — rich types, inert values.
- **Not** device/user FFI — `gpio`/`uart`/etc. stay ordinary typed `@extern`,
  outside this algebra.
