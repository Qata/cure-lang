# `Std.Otp` conformance fixes — design

**Date:** 2026-07-14
**Status:** approved (design gate); implementation pending
**Source:** `docs/research/process-types/raw-algebra-conformance-checklist.md` (executed audit, 2026-07-14)
**Design being repaired:** `docs/superpowers/specs/2026-07-09-typed-beam-process-algebra-design.md`
**TCB delta:** zero — every change is elaborator + stdlib. The kernel is untouched.

---

## 1. Problem

The executed conformance audit compared `lib/std/otp_raw.cure` (the sealed raw base)
and `lib/std/otp.cure` (the typed surface) against a machine-checked reference
semantics of Core Erlang, against the AtomVM source, and against probes of both the
real BEAM BIFs and the Cure elaborator. It found the typed layer **claiming things
the BEAM does not deliver**:

- **F-2c** `raw_whereis : Atom -> Effect(RawPid(m,m))` **asserts the lookup succeeds.**
  The BEAM returns the bare atom `undefined` for an unknown name (probed on OTP;
  `globalcontext.c:641` on AtomVM). A well-typed `Pid(m)` can therefore *be* the atom
  `undefined`, and the next `tell` emits `erlang:send(undefined, …)` → `badarg`.
- **F-2a** `Pid(m)` and `GenServer(q,r)` are **typealiases of the same constructor**,
  so `Pid(m)` *is* `GenServer(m,m)`. `call`/`cast`/`stop` on a plain spawned process
  typecheck; at runtime the caller blocks 5 s and then exits `timeout`.
- **F-4** Ten raw ops declare `Effect(Unit)` for BIFs that return real terms
  (`send` → the message, `link`/`exit`/`register`/… → `true`, `cast`/`stop` → `ok`,
  **`cancel_timer` → an `Int`**). `emit.ex` performs no result coercion, so the value
  inhabiting `Unit` (runtime atom `unit`) is in fact an integer or a boolean. This
  violates the parent spec §3.1 ("every extern at its most permissive **honest** BEAM
  type").
- **F-3** `raw_exit`'s `reason` is fully polymorphic, erasing the
  `normal`/`kill`/other distinction that all three of the semantics' exit rules turn on.
- **F-5** `MonitorRef` and `TimerRef` are aliases of one `Ref` type, so
  `cancel_timer(monitor_ref)` typechecks; `demonitor` omits `flush`, so a stale `DOWN`
  can outlive it; and the module docstrings imply a delivery/ordering guarantee the
  BEAM does not give.

## 2. Scope

### In scope

F-2c, F-2a, F-4 (except the `start_link` return — see below), F-3, F-5, plus the
documentation of the two platform hazards the audit surfaced (AtomVM's broken
`send_after`/`cancel_timer` pairing, and `call`'s partiality).

### Explicitly out of scope — and why

- **F-1 — the pid index is founded on nothing.** Every pid-producing op returns
  `Pid(m)` at a *free* implicit `m`; `spawn`'s thunk is `() -> Unit` and says nothing
  about messages. Grounding `m` is the parent spec's §4.2 code derivation, which is
  **Rung 2** and gated on the macro facility. Out of scope by the operator's own
  sequencing.
- **Honest `start_link` return (F-4b).** `gen_server:start_link` returns
  `{ok,Pid} | {error,Reason} | ignore`. Typing it honestly means producing a *typed*
  `GenServer(q,r)` from an untyped BEAM tuple — which is precisely the unfounded
  assertion F-1 describes. It is the same problem, and it is deferred with F-1 as one
  bundle. `raw_start_link` keeps `Effect(Tuple)` and gains a docstring stating the
  `ignore` lie on OTP.
- **F-2b — `call` typed as total.** `gen_server:call` does not *return* an error; on
  timeout or server death it **exits the caller**. A crash produces no value, so
  `Effect(r)` is *partial*, not unsound — no wrongly-typed value is ever produced. The
  honest repair is an **additive** `try_call` over a `cure_std_otp` try/catch runtime
  shim (precedent: `cure_std_gen`, `cure_std_time`). That needs its own design and its
  own AtomVM verification, is additive, and blocks nothing. Deferred; `call`'s
  partiality is **documented at the op** in this batch.

## 3. Design

### 3.1 `@erases(<class>)` — a declared runtime shape for opaque FFI carriers

`Cure.Elab.Union` decides whether an anonymous union is discriminable by asking each
member for its **runtime class** — the Erlang guard that recognises its erasure
(`is_integer`, `is_atom`, `is_list`, …). `Union.class_of_data_name/1` currently answers
by *name*, for a fixed set (`Bool`, `Nat`, `Bounded`, `List`), and returns
`:unsupported` for everything else. `discriminable/1` **rejects** a union containing an
`:unsupported` member.

An `opaque type` has **zero constructors**. It has no Cure-side erasure to infer: its
values arrive only across an `@extern`. So its runtime shape must be **declared**.

Introduce an item-level decorator on opaque type declarations:

```cure
@erases(:pid)
opaque type RawPid(m, r, k)

@erases(:reference)
opaque type MonitorRef
```

- **Admissible classes:** `:pid`, `:reference`, plus the existing
  `:integer`, `:float`, `:binary`, `:atom`, `:boolean`, `:list`. Each maps to exactly
  one total Erlang guard (`is_pid`, `is_reference`, …). An unrecognised class is a
  compile error at the declaration, naming the admissible set.
- **Where it is stored:** on the opaque family record (`Inductive.opaque_family/3`
  gains an `erasure` field, default `nil`).
- **Who reads it:** `Union` resolves `{:data, name, _, _}` → the family's declared
  `erasure`, falling back to today's name-based table and then to `:unsupported`.
- **Overlap rules:** `:pid` and `:reference` overlap **nothing** — not each other, not
  `:atom`, not `:unsupported` (a user ADT erases to a bare atom or a tagged tuple,
  never a pid or a reference). This makes `RawPid(...) | :undefined` a true `Union<…>`
  (disjoint erased value sets), not a `Disjoint<…>`.
- **Non-goal:** `@erases` is *not* a safety proof. It is an assertion by the author of
  a sealed `unsafe` FFI module that the foreign value has that shape — exactly the kind
  of claim the raw base exists to concentrate. Applying it to a *non-opaque* type is a
  compile error (a type with constructors already has an inferable erasure; a second,
  possibly contradictory, answer must not exist).

**Env threading.** `Union.runtime_class/1` is today pure on the member map, but members
are rebuilt from their family key by `Union.members_of/2` (`explode/2`), so the class
cannot simply be cached on the member at canonicalisation — it must be resolvable from
the key at every use. `runtime_class`, `disjoint_only?`, `family_key`, `discriminable`
and `discrimination_order` therefore all take `env`. Every call site
(`canonicalise/3`, `declare/3`, `emit.ex`'s `extern_union_members/2` and `type_clause`)
already has one; this is a mechanical widening.

### 3.2 F-2c — `whereis` returns an `Option`

```cure
# Std.Otp.Raw — honest and permissive
@extern(:erlang, :whereis, 1)
fn raw_whereis({m: Type}, {r: Type}, {k: PidKind}, name: Atom)
  -> Effect(RawPid(m, r, k) | :undefined)

# Std.Otp — the typed facade reintroduces the failure case
fn whereis({m: Type}, name: Atom) -> Effect(Option(Pid(m)))
```

`emit.ex` already re-tags an extern's union return at the FFI boundary
(`union_dispatch/2`): the literal member `:undefined` is matched by exact value and
comes first; the type member `RawPid(...)` is matched by `is_pid`. There is
deliberately no catch-all — a shape outside the declared union is a `CaseClauseError`
naming the offending value, which is the honest outcome. The typed `whereis` matches
the union and returns `Some(pid)` / `None()`.

### 3.3 F-2a — an erased kind index separates `Pid` from `GenServer`

```cure
type PidKind = Plain | Server           # erased; a phantom index

opaque type RawPid(m, r, k)             # k : PidKind

typealias Pid(m)          = RawPid(m, m, Plain)
typealias GenServer(q, r) = RawPid(q, r, Server)
```

`Pid(m)` and `GenServer(q,r)` are now **distinct types**. The op signatures split
accordingly:

- **`Server`-only:** `call`, `cast`, `stop` — the OTP-behaviour ops. Calling a plain
  spawned process is now a compile error, which is what F-2 asked for.
- **Kind-polymorphic** (`{k: PidKind}`): `tell`, `send_after`, `link`, `unlink`,
  `monitor`, `exit`, `is_alive`, `register`, `whereis`. Raw-sending to a gen_server is
  legitimate BEAM practice — it lands in `handle_info` — so `tell` must accept both
  kinds.
- `spawn`/`spawn_link`/`self` produce `Plain`.

The index is erased (0-quantity, phantom): **zero runtime cost, zero ESP32 footprint.**

This does *not* fix F-1 — a `GenServer(q,r)` value still has to come from somewhere,
and today it can only be a function parameter. What it does fix is the *collapse*: the
two handles can no longer be silently interchanged.

### 3.4 F-4 — honest raw result types

| raw op | was | becomes |
|---|---|---|
| `raw_send` | `Effect(Unit)` | `Effect(m)` — the BIF returns the message |
| `raw_link`, `raw_unlink`, `raw_exit`, `raw_register`, `raw_unregister`, `raw_demonitor` | `Effect(Unit)` | `Effect(Bool)` — returns `true` |
| `raw_cast`, `raw_stop` | `Effect(Unit)` | `Effect(Atom)` — returns `ok` |
| `raw_cancel_timer` | `Effect(Unit)` | `Effect(Int \| Bool)` — remaining ms, or `false` |
| `raw_start_link` family | `Effect(Tuple)` | unchanged; docstring records the `ignore` lie (deferred, §2) |

The typed wrappers keep their existing result types by **discarding** the raw result:

```cure
fn tell({m: Type}, {r: Type}, {k: PidKind}, dest: RawPid(m, r, k), msg: m) -> Effect(Unit) =
  let _sent = raw_send(dest, msg)
  unit()
```

The effect elaborator already supports this — a `let` sequences the effect, and a pure
value in an `Effect`-expected tail position is injected as `{:effect_pure, …}`
(`elaborator.ex`), which `emit.ex` lowers away entirely (`lower(env, {:effect_pure, a})
= lower(env, a)`). No new machinery, no runtime cost.

`cancel_timer` is the one whose typed result genuinely changes, because the information
is real and worth surfacing:

```cure
fn cancel_timer(ref: TimerRef) -> Effect(Option(Int))   # Some(ms_remaining) | None
```

### 3.5 F-3 — a precise exit reason

The three exit rules of the reference semantics case on `reason ∈ {normal, kill, other}`
crossed with the target's `trap_exit` flag and the signal's link flag. A polymorphic
`reason` cannot express which of the three outcomes an `exit` can have.

The **raw** op stays permissive (spec §3.1 — the raw base is the *most permissive
honest* type), but the **typed** layer narrows to a real sum:

```cure
type ExitReason = Normal | Kill | Because(Atom)

fn exit({m: Type}, {r: Type}, {k: PidKind}, pid: RawPid(m, r, k), reason: ExitReason) -> Effect(Unit)
```

`exit` still — correctly — makes **no** type-level claim that the target dies. That was
already conformant and stays that way. What changes is that the reason is now legible.

`process_flag(trap_exit, _)` remains **absent** from the raw base. That omission is
intentional and currently sound (behaviours own the mailbox; raw `receive` is rejected
at elaboration with E043), and it is already on the parent spec's ledger. It is not
reopened here.

### 3.6 F-5 — the small honest things

- **Distinct reference types.** `opaque type MonitorRef` and `opaque type TimerRef`,
  both `@erases(:reference)`, replacing the single `Ref` aliased twice. `demonitor`
  takes a `MonitorRef`; `cancel_timer` takes a `TimerRef`; `monitor` and `send_after`
  produce the respective one. `cancel_timer(monitor_ref)` becomes a compile error.
- **`demonitor` gains `flush`.** `raw_demonitor_flush` → `erlang:demonitor/2` with
  `[flush]`, and the typed `demonitor` uses it, so a stale `DOWN` cannot outlive the
  call. AtomVM supports `flush` natively (`nifs.c:5022-5061`), so this is universal.
- **Docstrings stop implying guarantees the BEAM does not give.** The `Std.Otp.Raw`
  header currently says the effect discipline "forbids duplicating, dropping, or
  reordering a `send`/`call`". That is about the *program's effect sequence*, not
  mailbox arrival, and a reader can easily mistake it for a delivery guarantee. It is
  reworded to state what the BEAM actually promises: **pairwise sender→target ordering
  only, and no delivery at all** (a send to a dead process silently succeeds).
- **The two platform hazards are documented at the ops**, not only in a research doc:
  - `send_after`: on AtomVM the returned ref is **not cancellable** — `send_after/3`
    registers the timer under a different ref than the one it hands back
    (`timer_manager.erl:87-91`), so `cancel_timer` returns `false` and the message
    fires anyway. Retargeting at `erlang:start_timer/3` would fix cancellability but
    changes the delivered message shape to `{timeout, Ref, Msg}`, which changes the
    receiver's accepted message set — so it is a *typed* change, deferred with the
    Rung-2 work, not a silent substitution.
  - `call`: partial. On timeout (default 5000 ms) or server death, **the caller
    exits**. No value is returned at the wrong type; there is simply no continuation.

## 4. Testing

Red-test-first throughout. The existing `test/cure/stdlib/otp_test.exs` is the model:
programs are put through `Program.elaborate/1` and asserted `{:ok, _}` or `{:error, _}`.

**Elaborator (`@erases` + Union):**
1. An opaque type with `@erases(:pid)` is a legal union member; without it the same
   union is rejected with `{:unsupported_member_shape, …}`.
2. `@erases` with an unrecognised class is a compile error naming the admissible set.
3. `@erases` on a **non-opaque** type is a compile error.
4. `RawPid(...) | :undefined` canonicalises to a `Union<…>` (disjoint erasures), not a
   `Disjoint<…>`.
5. Emission: the extern wrapper for a `pid | :undefined` return dispatches on
   `R =:= undefined` first, then `is_pid(R)`, and injects the matching constructor.

**Typed surface (`otp.cure`):**
6. `whereis` returns `Option(Pid(m))`; a program that `tell`s the result **without
   matching** is a compile error (this is the F-2c red test — it typechecks today).
7. `call` on a `Pid(m)` is a compile error; `call` on a `GenServer(q,r)` succeeds
   (F-2a red test — the former typechecks today).
8. `cast`/`stop` on a `Pid(m)` are compile errors.
9. `tell` on a `GenServer(q,r)` **succeeds** (kind-polymorphic — guards against
   over-narrowing).
10. `exit(pid, Normal)` succeeds; `exit(pid, 5)` is a compile error.
11. `cancel_timer(monitor_ref)` is a compile error; `demonitor(timer_ref)` is a compile
    error.
12. `cancel_timer` returns `Effect(Option(Int))`.

**Regression pin (the concrete `no_widening_narrow`):**
13. A test that asserts the **declared return type of every op in `Std.Otp.Raw`**
    against an explicit table. The parent spec's §12 `no_widening_narrow` validator
    cannot be automated in general — it would need an oracle for every BIF's return
    type — but pinning the audited table makes any future widening a failing test
    rather than a silent lie. This test carries a comment pointing at the audit as its
    source of truth.

The existing OTP tests that assert `start_link` returns `Effect(Tuple)` and that
exercise `beam_ops` continue to pass unchanged; the ones that `call` a `Pid` must be
updated to use a `GenServer` (they were asserting the bug).

## 5. Consequences

- `Std.Supervisor` uses `Std.Otp.Raw` only for `RawTerm`/`raw_term` — unaffected.
- `Std.Fsm`, `Std.Actor`, `Std.Process`, `Std.App` reference `Std.Otp` only in
  docstrings — unaffected.
- `Cure.Stdlib.Preload` lists the modules; no change.
- **No kernel change. No TCB delta.** `Union` and `emit` are elaborator; the rest is
  stdlib.

## 6. Deferred, as one bundle

F-1 (code derivation grounding the pid index), the honest `start_link` return, `try_call`
over a `cure_std_otp` shim, and retargeting `send_after` at `start_timer/3`. All four
need either Rung 2 or a runtime shim with its own AtomVM verification. They are recorded
in §6 of the audit and remain there.
