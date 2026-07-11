# Macro Facility — Program Decomposition

> Not an executable task plan. This is the **program roadmap**: the ordered
> sub-projects the "base macro facility + self-proving extension" decomposes into.
> Each sub-project (SP) ships working, testable software on its own and gets its
> OWN task-by-task plan (`docs/superpowers/plans/YYYY-MM-DD-<sp-name>.md`) written
> and executed before the next. Derived from the bootstrap order of
> `macros/2026-07-08-macro-facility-design.md` §10 + §14 and the enforced
> obligations of `2026-07-11-self-proving-macros-design.md`.

**Why decomposed:** the writing-plans scope check — the facility spans several
independent subsystems (parsing, hygiene/expansion, compile-time evaluation,
generative testing, reflection, OTP container minting). A single plan cannot carry
complete code for all of them without becoming placeholders. Each SP below is a
standalone plan.

**Invariant across every SP (from base §9):** the facility lives entirely in the
untrusted frontend, upstream of the elaborator. Macro output is **re-elaborated and
kernel-checked exactly like hand-written code**. **TCB delta = zero** — no SP changes
`lib/cure/core/*`. Any SP that thinks it needs to is mis-scoped; stop and re-plan.

---

## The sub-projects, in build order

### SP1 — Minimal facility: container + grammar + Tiers 1–2
**Ships:** a `macro` container that parses `syntax`/`literal` rules
(examples-with-holes), scoped by `use`, expanding via Tier-1 literal rules and Tier-2
hygienic `becomes` templates; a `units`-style and an `every`-style macro work
end-to-end and their output kernel-checks. **No** Tier-3 elab, reflection, or
generative proof yet.
**Includes:** the quoted-AST model (§3), hygiene + `<fresh Name>` (§5), two-pass
name resolution (§6), import scoping + same-keyword conflict error (§7), the
*default* error machinery floor (§2 typed-hole errors) — NOT yet the type-enforced
exhaustiveness (that is SP2).
**Gate:** a Tier-1 and a Tier-2 macro compile, expand, and their expansions pass the
existing kernel; wrong-arity/unknown-category uses produce a (default-machinery)
diagnostic, not a raw parser error. Full `mix test` green.
**Depends on:** nothing new (existing parser/lexer/elaborator).
**The hard part:** designing how examples-with-holes rules hook into the existing
`lib/cure/compiler/parser.ex`/`lexer.ex` — needs a parser-internals exploration pass
before its plan is written.

### SP2 — Tier 3 + self-proving Mechanisms 1 & 3
**Ships:** `syntax … computed by f` (total compile-time Cure over quoted decls,
`check … else fail`), size-change-certified pure elabs (§5); PLUS the type-enforced
obligations that need no generation: **derived + author-extensible `Diagnosis`**
(`fail C(args)` §3.4), **exhaustive `explain`** checked like case-coverage
(self-proving §3), and **required per-rule worked examples** (self-proving §5). A
Tier-3 macro (e.g. a `schema`/`config`-style one) works, and a macro with an
undescribed failure point or an unpinned rule FAILS TO COMPILE.
**Gate:** the three new macro-compile errors (`missing_diagnosis`, `rule_unpinned`,
plus example-mismatch) fire on red fixtures and are absent on green ones; example
expansions kernel-check. Full suite green.
**Depends on:** SP1.

### SP3 — Self-proving Mechanism 2: generative expansion proof
**Ships:** the Antigen-for-DSLs engine (self-proving §4) — **full fuzz on every macro
compile**: generate valid parses by type-directed filling of typed holes (extends the
Antigen generator with "term of a required type"), expand, kernel-check; a valid parse
expanding to ill-typed Core fails the macro's compile (shrunk counterexample). Caching
by macro definition. Per-macro coverage manifest.
**Gate:** a macro whose `becomes`/elab drops a hole's type is REJECTED at macro-compile
with a shrunk counterexample; a correct macro passes; the manifest reports coverage.
Full suite green; Antigen campaign green.
**Depends on:** SP2 (needs Tier-3 elabs + the grammar to fuzz) + the Antigen generator.
**The one new engine:** type-directed term generation.

### SP4 — Tier 4 reflection API
**Ships:** the read-only advisory API (§8) — `resolve`, `constructors`, `infer`,
`expand`, `lift` (the append-only write member) — enough for `reducer`/`flow`/`view`.
Dogfood Gate 2: the `reducer` spec compiles as a library and elaborates the Door
program.
**Gate:** a `reducer`-style macro builds GADT match arms via `constructors`/`resolve`
and its output kernel-checks; `lift` hoists a declaration; nothing returned by the API
is trusted (a lie from it still yields a rejected-not-unsound program). Full suite green.
**Depends on:** SP2 (Tier-3 elab host). Independent of SP3.

### SP5 — §14 BEAM/OTP container ownership: `behaviour`/`callback` + `lift module`
**Ships:** the closed callback vocabulary as Cure ADTs (§14.3), `lift module`
minting a compiled unit as a VALUE (§14.4–.5, pure — no compile-and-load), and the
first OTP container fully owned by a macro (Gate 1b: `sup` under a fresh name,
simplest correctness bar, no user callback bodies). This is what gives **`Std.Otp`
its ceiling** — `spawn`/`start_link` minting typed handles + gen_server behaviours
compiled from a Cure `process`/`actor` macro.
**Gate:** a `sup`-style macro emits a gen_server/supervisor behaviour that runs on
generic-unix AtomVM (observable), all through `lift module`, no bespoke Elixir backing
it. Then `actor`/`fsm` re-expressed (Gate 1) and their bespoke compilers deletable.
**Depends on:** SP2 (+ SP4 for callback-body elaboration). Ties back to the effect
stack (already landed) — callback bodies are `Effect`-typed.

### SP6 — Tier 5 + the concrete DSL libraries
**Ships:** module rules + raw holes (§13.1–.2), then the sibling DSL specs
(`packet`, `board`, `driver`, `protocol`, `parse`, …) as libraries on the finished
facility. Each DSL is its own small plan.
**Depends on:** SP1–SP5 as each DSL requires.

---

## Sequencing summary

```
SP1 (facility + Tiers 1–2) ──> SP2 (Tier 3 + typed errors + examples) ──┬─> SP3 (generative proof)
                                                                        ├─> SP4 (reflection API)
                                                                        └─> SP5 (behaviour/lift module ──> Std.Otp ceiling)
                                                                              └─> SP6 (Tier 5 + DSL libraries)
```

SP1→SP2 is the spine. SP3/SP4/SP5 fan out from SP2 and can be ordered by priority
(SP5 unblocks the `Std.Otp` ceiling; SP3 delivers the self-proving guarantee's
headline; SP4 unblocks the flagship reducers). Write and execute one SP's detailed
plan fully — red-green, gated, committed — before starting the next.

## Immediate next step

Write **SP1's** task-by-task plan
(`docs/superpowers/plans/2026-07-12-macro-facility-sp1-<name>.md`). Prerequisite: a
focused exploration of `lib/cure/compiler/parser.ex` + `lexer.ex` to fix exactly how
an examples-with-holes `syntax` rule is lexed, parsed into the quoted-AST model, and
matched at a use site — the one genuinely new parsing subsystem. That exploration is
the first thing SP1's plan is written against.
