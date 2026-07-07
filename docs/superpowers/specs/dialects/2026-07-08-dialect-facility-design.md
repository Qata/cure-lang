# The `dialect` Facility — Cure's One Frontend Feature

**Date:** 2026-07-08
**Status:** design (operator-decided architecture). Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
§5, consolidating it and its §9 items 1–8 into the facility's own home. Every
other 2026-07-08 dialect spec (`board`, `driver`, `packet`/`codec`, tasks,
units, `config`/`secret`, `check`, web trio, `schema`, `parse`, `cli`/`job`,
`workflow`/`bot`, `sim`/`pattern`, `reducer`, `protocol`, `fleet`) is a
*library* built on this.

**The decision (operator, 2026-07-08):** the compiler grows exactly ONE new
frontend feature — this facility. No per-DSL special treatment, ever. This is
also what de-specializes Cure: not an MCU language, but a BEAM language where
libraries are languages.

Reference models: Lean 4's `syntax`/`macro_rules`/`elab_rules` tower
(hygienic, in-language, layered by power); Idris elaborator reflection as the
top-tier shape; Racket for the ecosystem thesis — when extending the language
is library work, the ecosystem writes the languages.

---

## 1. The container

A `dialect` is a container in the `fsm`/`actor`/`sup` family with four kinds
of members — grammar (`category`/`syntax`), rewriting (`expand`), computation
(`elab`), and diagnostics (`explain`):

```cure
dialect Every
  ## `every <duration>: <block>` — run a block periodically, supervised.

  syntax every $period:Duration $body:Block

  expand
    every $period $body ~>
      fsm $fresh(Tick) with Unit
        Idle --tick--> Idle
        @timer $period
        on_timer
          (:idle, s) -> { $body; %[:ok, s] }

  explain
    {:no_instance, Duration, t} ->
      "every expects a duration — write every 500ms or every 2s (got " <> show(t) <> ")"
```

A dialect is an ordinary module member; it exports its keywords the way a
module exports functions.

## 2. Grammar — `category` and `syntax`

- `syntax <production>` declares a rule for either a **top-level form** (a new
  container keyword like `every`, `reducer`, `packet`) or a **named category**
  declared with `category Name` (e.g. `reducer`'s `Edge`, `Schema`, `Clause`).
- Productions mix literal tokens with **typed non-terminals** `$name:Kind`.
  The initial kind inventory (extensible by category declarations):
  `Expr`, `Block`, `Pattern`, `TypeExpr`, `Ident`, `UpperIdent`, `Atom`,
  `RecordLit`, `RecordTypeBlock`, `ParamTuple`, `Duration`-class *typed
  literal* kinds, plus combinators `Many(K)`, `Indented(K)`, `(…)?` optional,
  and alternation written as multiple `|` productions.
- **Literal rules** (Tier 3) extend the lexer in the one narrow way units
  need: `literal $n ms ~> Duration.ms($n)` — a numeric token juxtaposed with
  a registered suffix. No other lexer extension exists.
- Grammar rules are **declarative data**. Two structural dividends, stated as
  requirements: the LSP consumes the same rule set (per-dialect highlighting/
  completion with zero per-dialect work), and `cure <dialect> report`-style
  tools can render any dialect's grammar as documentation.

## 3. The quoted-AST model

Every `category` **auto-derives a record/ADT type** for its parse result
(`Syntax(Edge)` ≈ `rec` with one field per non-terminal, alternation as an
ADT). `elab` functions are ordinary Cure functions over these types. `quote`
builds syntax values; `$( )` splices them; both are *typed against the
category being built* — a `quote` producing a malformed production is a
compile error in the dialect itself, not in its user's program.

This is the parent's assumption in the `reducer` worked example
(`schemas.map(fn(s) -> s.state)` — quoted decls as plain records) — adopted
here as the design: **derived typed ASTs, not a universal `Syntax` blob.**
(A generic traversal API over any syntax value exists underneath for tooling;
dialect authors normally never need it.)

## 4. Power tiers

| Tier | Mechanism | Who uses it |
|---|---|---|
| 1 | `syntax` + `elab` over quoted decls (declarative data) | `boarddef`, `driver`, `packet`, `config`, `schema`, `parse` |
| 2 | `syntax` + `expand` (hygienic templates) | `every`/`on`, `secret`, module-level `let` |
| 3 | `literal` rules | units |
| 4 | `elab` + reflection API (§8) | `flow`, `reducer`, `view` |

A dialect declares nothing about its tier — it simply uses what it needs;
the tiers are a design/teaching taxonomy and a build-order (§10).

## 5. Hygiene, expansion, termination

- `expand` templates are **hygienic**: names introduced by the template
  cannot capture or be captured by user identifiers; `$fresh(Name)` mints a
  readable unique name (for generated containers that need stable-ish module
  atoms, e.g. `fsm $fresh(Tick)` → `Cure.FSM.Tick$3`).
- `elab` functions are **total Cure**, checked by the same size-change
  termination certificate as user code. Combined with a bounded expansion
  depth (a dialect's output containing dialect forms re-enters expansion;
  the fuel bound is a backstop, the totality check is the real guarantee),
  **Cure compilation provably terminates even with user-defined syntax** —
  a property Lean does not have, and worth a docs headline.
- `elab` runs **staged on the host** at compile time: full stdlib available,
  no AtomVM constraints, but **no ambient effects** — elab functions are pure
  (they may read only what the facility hands them: the quoted input and the
  reflection API). Determinism of builds is non-negotiable.

## 6. Staging & name resolution

User code may reference dialect-*derived* names before the dialect block
elaborates (the operator's Door example: `type DoorReject =
InvalidTransition(source: Door.State, msg: Door.Msg)` textually precedes the
`reducer` that derives `Door.State`/`Door.Msg`). Resolution is therefore
**two-pass within a module**:

1. **Signature pass** — every dialect instance runs a cheap `declares` phase
   (derived from its `elab`'s emitted declaration heads; for Tier-1/2 this is
   syntactic) publishing the names it will define.
2. **Elaboration pass** — bodies elaborate against the full name environment.

Cycles between two dialect instances' *derived types* are an error with an
explainer (name the two instances and the cycle). This is ledgered detail
work (§11.3) but the two-pass shape is decided.

## 7. Scoping & composition

- Dialect syntax is **scoped by import**: `use Hardware.Every` brings the
  `every` keyword into the module. No global grammar.
- Two imported dialects exporting the **same top-level keyword** is an error
  at the `use` site (explainer offers qualified activation:
  `use Hardware.Every only [every]` / renaming ledgered §11.4).
- Category names are namespaced by dialect; cross-dialect category reuse is
  explicit (`$f:Packet.FieldDecl`) — this is how `protocol` embeds `packet`
  payload declarations without owning them.

## 8. The Tier-4 reflection API — smallest thing that passes the dogfood

The one genuinely hard design. `reducer`'s `clause_to_arm` must build GADT
match arms and record literals *against types the same elab derived*; `flow`
must infer indices. The API is deliberately minimal, read-only toward the
elaborator, and **advisory** — nothing it returns is trusted (§9):

- `resolve(name) -> Sig | NotFound` — a global's/type's elaborated signature.
- `constructors(type_name) -> [CtorSig]` — for building matches.
- `infer(quoted_expr, env) -> Type | Error` — ask the elaborator to type a
  quoted term in a given quoted context (the expensive one; needed by `flow`).
- `fresh_name`, `fresh_meta`-free — no metavariable access; dialects never
  see or create holes (the K3 firewall applies to elab output).

Explicitly absent: solving, unification hooks, environment mutation,
reduction control. If the dogfood (§10) proves something more is needed, it
is added by amending THIS spec, never ad hoc.

## 9. Soundness — why this is safe to hand to strangers

Dialect output is **re-elaborated and kernel-checked exactly like
hand-written code**. The facility sits entirely in the untrusted frontend,
upstream of the elaborator; the Final-Core validator and kernel are
unchanged and unaware of it. Therefore:

- A buggy dialect yields a confusing error or a rejected program — **never an
  unsound one**. UX bugs are possible; soundness bugs are not. **TCB delta:
  zero.** (Same layering argument as the elaborator itself.)
- The `explain`/provenance machinery (see the error-explainer spec,
  `2026-07-08-error-explainer-design.md`) exists precisely to turn that
  "confusing error" caveat into a bounded, reportable defect class.
- Elab purity (§5) means a malicious dialect cannot exfiltrate or vary builds
  — the worst it can do is generate rejected or weird-but-checked code.

## 10. Dogfood gates & bootstrap order

**Gate 1 (facility "done"):** `fsm` could be re-expressed as a dialect
(whether or not it migrates — parent §9.7).
**Gate 2 (Tier 4 "done"):** the `reducer` spec's dialect definition compiles
as a library and elaborates the operator's Door program.

Bootstrap order (parent §9.1, resolution proposed here): **facility first,
Tiers 1–3 only**, shipping `board`/`driver`/`packet`/units/tasks as libraries
immediately (none need Tier 4); Tier 4 lands second, unlocking
`reducer`/`flow`/`view` as libraries. This avoids the second permanent
implementation path entirely at the cost of gating the flagship reducers on
Tier 4 — acceptable because `fsm`/`flow` exist built-in today and keep
working throughout.

## 11. Open decisions (consolidated ledger — parent §9 items 1–8 live here now)

1. ~~Bootstrap order~~ — resolution proposed in §10; confirm at
   implementation.
2. **Meta-grammar finalization** — the exact non-terminal inventory (§2),
   `Indented`/layout interaction with the indentation-sensitive lexer, and
   ambiguity policy (recommend: LL-style committed choice per leading token;
   a dialect whose productions are ambiguous against *imported* dialects is
   an error at import, computed from FIRST sets).
3. **Two-pass details** (§6) — what exactly Tier-4 `declares` may compute
   (must not need the reflection API, or staging cycles return).
4. **Keyword conflict ergonomics** (§7) — `only`/rename surface.
5. **Reflection API completeness** (§8) — frozen until Gate 2 forces
   amendments.
6. **Quoted-AST versioning** — a dialect compiled against category shapes
   that later change (compiler upgrades): derive-and-recompile is the answer
   for source packages; binary dialect distribution is a non-goal (§12).
7. **Migration of built-ins** — whether `fsm`/`actor`/`sup` actually move
   (Gate 1 only requires *could*); recommend: leave built-in until the
   facility is boring, then migrate one as a proof, keep the rest.
8. **`explain` registration mechanics** — deferred wholesale to the
   error-explainer spec.

## 12. Non-goals

- No arbitrary compile-time effects in `elab` (no IO, no network, no
  filesystem) — purity is load-bearing (§5, §9).
- No binary/opaque dialect distribution — dialects ship as source packages.
- No reader-level lexer extensibility beyond `literal` suffix rules — Cure's
  token grammar is otherwise fixed (indentation structure stays sacred).
- No proof-producing macros / tactic framework — dialects generate programs,
  not proofs; obligations discharge by computation or become domain errors
  (hiding principle 3), and `check`'s certificate elevation is the sanctioned
  proof-automation path.
