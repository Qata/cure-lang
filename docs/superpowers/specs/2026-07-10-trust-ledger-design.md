# Trust Ledger — design

**Date:** 2026-07-10
**Status:** designed, not implemented
**Command:** `cure audit trust <Module>`

## 1. Problem

Cure's claim is that the kernel checks everything: if it typechecks, it is
proved. That claim has holes, and nothing enumerates them.

The largest is `@extern`. A bodyless `@extern` is a typed FFI postulate —
`lib/cure/elab/declarations.ex:234` says so in as many words: *"the signature IS
the type; there is no term to elaborate/check."* It asserts, without evidence,
that a BEAM function inhabits the declared Π type, is total, and is pure. The
stdlib carries 156 of them across 22 modules.

There is today no command that answers **"what does this program assume without
proof?"** That is the whole of what this feature adds.

A fact that only became visible while designing this, and which argues for
building it: **92 of those 156 axioms — 59% — point at cure-lang's own Elixir
code, not at OTP.** They are assumptions about software in this repository, which
could be tested, or replaced by Cure, rather than assumed. Nobody knew that,
because nobody could count.

The secondary effect is the one that matters: once the answer is a deterministic
line-per-axiom report, a CI job can diff it, and adding an axiom to the stdlib
becomes something a reviewer sees instead of something that happens silently.

## 2. Non-goals

- **No lockfile, no committed artifact, no `.cure/` tree.** The tool prints to
  stdout. CI may capture and diff its output; that is CI's business, not a file
  every Cure library is forced to carry.
- **No effect classification.** `Cure.Types.Effects` belongs to the classic
  pipeline slated for deletion, and the locked decision routes effects into Core
  via an inert `Effect` former. v1 reports the raw target MFA and nothing more.
- **No graph rendering, no lowering artifacts, no proof replay.** Those are
  separate features that may later consume this one's output.
- **Not in the TCB.** `Cure.Audit.*` reads a kernel-checked environment. It
  cannot influence checking. Its own bugs produce a wrong report, never an
  unsound program.

## 3. Why the collector reads `Core.Env`, not source

The cheap design — scan `.cure` files for `@extern` — is unsound in the
near future, and unsoundness in the *under-reporting* direction is the one
failure a trust ledger cannot survive.

Macros are intended to be expressive enough to contain arbitrary code, including
other macros, and therefore to emit arbitrary declarations. A macro can emit an
`@extern`. The macro facility design
(`docs/superpowers/specs/macros/2026-07-08-macro-facility-design.md` §9) places
expansion "entirely in the untrusted frontend, upstream of the elaborator," with
macro output "re-elaborated and kernel-checked exactly like hand-written code."

Therefore the elaborated `Core.Env` is the only vantage point that observes every
axiom, today and after macros land. A macro-generated extern arrives in `env.defs`
as an `{:extern, {m, f, a}}` body, indistinguishable from a hand-written one.

**Cost, stated plainly.** A `Core.Env` ledger can only audit code that
dependent-elaborates. Measured on 2026-07-10, `io.cure` fails on `<>`/Semigroup,
and roughly 19 of 42 stdlib modules elaborate. v1 therefore cannot audit a
program importing `Std.Io`. This is not hidden: §7's `UNAUDITED` section names
every module that failed, and `--strict` turns a non-empty section into a
non-zero exit. Coverage grows as #23/#18 land, and the unaudited list doubles as
a debt counter for that work.

## 4. Trust classes

Nine things live in `Core.Env` (`lib/cure/core/inductive.ex:12`). Five are
trust-relevant. Each is one pattern-match.

| Class | Detection | Meaning |
|---|---|---|
| `ffi_postulate` | `%{body: {:extern, {m,f,a}}}` | You assert BEAM's `m:f/a` inhabits this Π type, totally and purely. Nothing checks it. |
| `builtin_op` | `%{builtin_op: op}` when non-nil | You assert BEAM's operator implements Core's semantics. |
| `opaque_family` | `Inductive.opaque?/2` | An Agda-style `postulate` type. Sound only because `kernel.ex:211` refuses to eliminate it. |
| `hole` | `{:hole, _}` in a body | Incompleteness, not trust. Already blocks codegen. |
| `absurd` | `{:absurd}` in a body | Admitted only under an inconsistent context. Reported because it is the shape a soundness bug would exploit. |

### 4.1 `builtin_op` is a fixed baseline, not a per-module contribution

`Env.register_builtin_op/3` (`inductive.ex:154`) is called from exactly three
sites, all in `lib/cure/core/builtins.ex` (196, 207, 217). No user code, and no
macro, can grow the set. Every module probed reports exactly 31.

The report therefore prints a **count and a summary line**, not 31 rows. A change
to `builtins.ex` is a TCB change and shows up as a changed count.

### 4.2 `uncertified` is reported, but it is not an assumption

`maybe_certify/2` (`declarations.ex:203`) runs `Kernel.validate_certificate/2`
opportunistically and swallows failure, so `env.certified` means "passed
size-change termination." A def absent from it does not δ-unfold.

That is a **completeness** limitation, not a soundness one:

- Type-level functions *must* certify or compilation fails —
  `TotalityClosure.certify_type_level/1` returns `{:error, {:totality_required, _}}`
  (`totality_closure.ex:34`).
- Value-level functions that fail simply never δ-reduce, so the kernel cannot use
  them to inhabit a type.

Empirically it is also small: 4 of 82 defs in `Std.List` (`reverse`, `last`,
`drop`, `take`), and 0 in `math`, `string`, `bool`, `option`.

So it gets its own report heading — *"cannot be used in proofs; not
assumptions"* — and is never conflated with the axioms. Externs and builtin ops
are excluded from this class (they have no body to certify;
`certify_type_level/1` already rejects externs at `totality_closure.ex:43`).

### 4.3 Origin tagging

Externs split three ways by target-module prefix, and the three are qualitatively
different kinds of trust. Measured 2026-07-10 over `lib/std/*.cure` (156
declarations; a 157th `@extern` occurrence is prose in a `process.cure` comment):

| Bucket | Count | Targets |
|---|---:|---|
| `OTP` | 64 | `erlang` (31), `maps` (11), `math` (8), `string` (5), `unicode` (3), `rand` (2), `lists` (2), `os` (1), `io` (1) |
| `CURE RUNTIME` | 49 | `cure_std_crdt` (22), `cure_std_time` (9), `cure_std_regex` (7), `cure_std_http` (4), `cure_std_json` (3), `cure_std_gen` (3), `cure_std_test` (1) |
| `CURE BRIDGE` | 43 | `Elixir.Cure.FSM.Builtins` (17), `App` (9), `Actor` (8), `Sup` (7), `Process` (2) |

Trusting `erlang:length/1` is trusting OTP — reasonable, and not going to change.
Trusting `cure_std_crdt:merge/2` is trusting Elixir in this repository:
`Std.Crdt` is a 22-axiom facade over code that could be tested, or rewritten in
Cure. Trusting `Elixir.Cure.FSM.Builtins` is trusting the bespoke fsm/actor/sup
machinery that the classic-pipeline-deletion plan intends to remove — so those 43
axioms have a scheduled expiry, and the ledger will show it happening.

The report prints the three buckets separately. This split is the single most
useful thing the tool produces, and it is invisible today.

## 5. Identity: key on the target, not the name

Def names in a freshly elaborated env are **bare atoms** (`:abs`, `:pi`); only
imported modules are rekeyed to `Mod#name` by `Resolution.rekey_module_env`. Names
are therefore an unreliable identity.

An axiom's identity is **`(target MFA, elaborated type)`**. `erlang:length/1` at
`∀{a}. List(a) -> Int` is the same assumption however the Cure wrapper is spelled,
and two wrappers of one MFA at two types are two assumptions.

This sidesteps the anonymous-instance provenance gap entirely: module attribution
becomes a best-effort *display* field, never part of an axiom's identity.

## 6. Components

### 6.1 `Cure.Audit.Refs` — a fail-closed walker

`Program.global_refs/1` (`program.ex:473`) ends in `defp global_refs(_leaf), do: []`.
For codegen that is benign. For a ledger it is fatal in the future tense: the day
the Core grammar grows a node, reachability silently under-reports and the ledger
quietly stops finding axioms.

`Audit.Refs.refs/1` enumerates every node in `Core.Term.term?/1` (`term.ex:57–90`)
explicitly and **raises** on anything else. It also has one clause for the
non-Core `{:extern, {m,f,a}}` sentinel that occupies a def's `body` slot.

### 6.2 `Cure.Audit.Ledger` — classification and reachability

Reachability is *not* `Program.reachable_def_names/2`. Its `collect_reachable/4`
deliberately excludes two classes:

- `builtin_op` defs — "never emitted as a function form"
- type-level defs (`%{type: {:type, _}}`) — "never emitted as a runtime function"

Both exclusions are correct for codegen and catastrophic for a ledger: the first
drops arithmetic, which is an axiom. The ledger shares the *shape* of that walk
and none of its filters.

An unresolved global is a **raise**, not a finding. `Kernel.infer/2`
(`kernel.ex:127`) already returns `{:error, :unknown_global}` for a dangling
reference, so on a kernel-checked env the condition is unreachable. If it fires,
the ledger's caller skipped `check_def`.

### 6.3 `Cure.Core.Printer` — new, untrusted

Nothing in the tree renders a `Core.Term` to text. `Quote.reify/2` returns a term;
call sites such as `{:typealias_not_a_type, name, Quote.reify(other, 0)}` hand it
to `inspect`. Every kernel and elaborator error that mentions a type today prints
a raw Elixir tuple.

The report needs readable types, so this spec adds a small (~100 line) printer:
de Bruijn indices back to names, Π-chains to arrows, applications to spines. It
is untrusted output, outside the TCB, and it independently improves every
dependent-pipeline error message. That second benefit is why it belongs here
rather than being faked.

### 6.4 CLI

```
cure audit trust <Module> [--format text|json] [--strict]
```

Always exits 0 when a report was produced. `--strict` exits non-zero if
`UNAUDITED` is non-empty. Never wired into `cure build` — a compiler that refuses
to build over an audit trains people to hate the audit.

## 7. Output

Deterministic: sorted, no timestamps, no absolute paths, no map-iteration order.
Determinism is load-bearing, because `cure audit trust Std.List | diff -` is the
ratchet.

Every section is printed even when empty, so that a section going from `(0)` to
`(1)` is a diff rather than a new line appearing from nowhere.

```
$ cure audit trust Std.List

AXIOMS — OTP (3)
  erlang:length/1          ∀{a}. List(a) -> Int
  erlang:hd/1              ∀{a}. List(a) -> a
  erlang:tl/1              ∀{a}. List(a) -> List(a)

AXIOMS — CURE RUNTIME (0)

AXIOMS — CURE BRIDGE (0)

OPAQUE TYPES (0)

KERNEL BUILTINS
  31 builtin operators (Cure.Core.Builtins)

HOLES (0)
ABSURD (0)

NOT PROVEN TOTAL (4)   — cannot be used in proofs; not assumptions
  reverse, last, drop, take

UNAUDITED (0)
```

`--format json` emits the same content with a `schema` version field, for CI.

## 8. Testing

Red-green, one failing test before each fix.

1. A fixture with one `@extern` yields exactly one `ffi_postulate` with the
   correct MFA and rendered type. Widen the extern's declared type; assert the
   rendered line changes.
2. **The divergence test.** A fixture using `+` yields a `builtin_op` entry, and
   `Program.reachable_def_names/2` on the same env does *not* mention it. This
   pins why the ledger owns its reachability, so nobody later "helpfully"
   deduplicates them.
3. `Audit.Refs.refs({:bogus})` raises. Then the real guard: every term Antigen's
   generator produces passes through `refs/1` without raising. Antigen already
   generates well-formed Core terms; this defends the fail-closed invariant and
   upgrades automatically as the grammar grows.
4. `opaque type` yields `opaque_family`; a genuinely-empty inductive does not
   (`opaque_family?/1` keys on the marker, not the constructor count —
   `inductive.ex:324`).
5. `Std.List` reports exactly `reverse, last, drop, take` as not-proven-total, and
   reports them under that heading, not among the axioms.
6. A module that fails to elaborate lands in `UNAUDITED`; `--strict` exits
   non-zero; the default exits 0.
7. Two runs over the same input produce byte-identical output.

## 9. Known limitations

- **Coverage is bounded by dependent-elaboration.** ~19/42 stdlib modules today.
  Surfaced, never hidden (§3).
- **Module attribution is best-effort.** Bare-atom def names and
  `__impl_<I>_<H>_<m>` instance globals carry no module identity. Fixing that is
  the same change as the anonymous-instance provenance gap — thread the module
  through `Implementation.register/2`. The ledger does not block on it, because
  identity keys on the MFA (§5).
- **Purity and totality of an extern are assumed, not stated.** An `@extern`
  carries no justification field, by decision. The ledger counts assumptions; it
  does not make you defend them.

## 10. Scope

Four modules — `Cure.Audit.Refs`, `Cure.Audit.Ledger`, `Cure.Core.Printer`, and a
CLI verb — plus the fixture corpus. No lockfile, no artifact directory, no file
writing.
