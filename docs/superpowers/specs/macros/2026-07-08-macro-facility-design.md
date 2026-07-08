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

**Power target (operator, 2026-07-08): beginner-friendly at the floor,
Racket-complete at the ceiling** — the facility must be able to do, more or
less, anything Racket's languages-as-libraries machinery can do. §13 is the
capability-by-capability audit against the Racket docs and the additions it
forced; §2 is the meta-grammar that keeps the floor at copy-one-example.

---

## 1. The container

A `dialect` is a container in the `fsm`/`actor`/`sup` family with three kinds
of members — grammar rules closed by a tier verb (`syntax … becomes …` /
`syntax … computed by f`), literal rules, and diagnostics (`explain`):

```cure
dialect Every
  ## every <period>: run the block that often, supervised.

  syntax
    every <period: Duration>
      <body: Block>
  becomes
    fsm <fresh Tick> with Unit
      Idle --tick--> Idle
      @timer <period>
      on_timer
        (:idle, s) -> { <body>; %[:ok, s] }

  explain
    {:no_instance, Duration, t} ->
      "every needs a duration — write every 500ms or every 2s (got " <> show(t) <> ")"
```

A dialect is an ordinary module member; it exports its keywords the way a
module exports functions.

## 2. Grammar — rules are examples with holes

(Notation adopted 2026-07-08, the meta-grammar pass of the Racket audit —
resolution of ledger §11.2's notation half. The sibling dialect specs predate
it and use the earlier `category`/`$name:Kind`/`expand ~>` sketch; the
mapping table below reads them 1:1 — update each opportunistically when it
is implemented.)

Design constraint: a driver author defines a dialect by copying one example,
without ever learning what a grammar formalism is. The move that buys this:
**a syntax rule looks exactly like what the user will type**, with
placeholders punched into it, read the way every developer already reads CLI
usage strings (`git checkout <branch>`). The full metasymbol inventory is
three items, all pre-known:

| Symbol | Meaning | Already known from |
|---|---|---|
| `<name: Kind>` | a hole | CLI docs: `<branch>`, `<file>` |
| `...` | more of the same | how humans write examples: `f(x, ...)` |
| `( … )?` | optional group | regex-lite |

No `::=`, no alternation bars, no combinators — `category`, `Many(K)`, and
`Indented(K)` from the earlier sketch are retired.

- **Rules.** `syntax <example-with-holes>`, optionally suffixed `is Category`,
  closed by a tier verb: `becomes` (hygienic template) or `computed by f`
  (elab function — "elab" remains the name for the computation tier
  throughout these specs; `computed by` is its surface spelling). A rule
  declares either a top-level form (`every`, `reducer`) or a category
  member. The same `<name>` bracket is the hole in the rule *and* the splice
  in the template — one notation, symmetric.
- **Alternation = clauses.** Alternatives are separate `syntax` lines, like
  function clauses:

  ```cure
  syntax emit <| <model: Code> <| <emission: Code>   is Action
  syntax update <| <model: Code>                     is Action
  syntax reject <err: Code>                          is Action
  ```

- **Categories are created by use.** `is Action` names the rule's category
  and creates it — no forward declaration. Guardrail: a hole kind that no
  rule declares is a compile error with near-miss suggestions (`is Actoin`
  cannot silently mint an empty category).
- **Repetition.** Line-oriented: `<edges: Edge>...` — "this line, repeated."
  Inline: the separator is written before the dots, as in documentation:
  `f(<args: Code>, ...)`. Deliberate simplification: `...` always means
  *zero or more*; "at least one" is not a grammar distinction but a
  `check … else fail` in the elab with a proper explainer — a parse error
  saying `expected Edge` is strictly worse UX than "reducer Door declares no
  transitions — add a `Closed --Msg--> State` line."
- **Bare-name rules** are legal (`syntax now becomes Clock.now()`) — the
  identifier-macro tier, no special casing.
- **Literal rules** (Tier 1) extend the lexer in the one narrow way units
  need: `literal <n: Number> ms becomes Duration.ms(<n>)` — a numeric token
  juxtaposed with a registered suffix. Together with raw holes (§13.2), the
  only lexer extension that exists.

**Hole kinds** (plain-English; closed for built-ins, open via `is` categories
and `literal` rules):

| Kind | Matches | Was (earlier sketch) |
|---|---|---|
| `Name` / `name` | capitalized / lowercase identifier — the kind is written the way the match must be written (self-teaching; call it out in docs, it is subtle) | `UpperIdent` / `Ident` |
| `Number`, `Text`, `Atom` | literals | — |
| `Code` | any expression | `Expr` |
| `Block` | indented code block | `Block` |
| `Type` | type expression | `TypeExpr` |
| `Pattern` | match pattern | `Pattern` |
| `Record` / `RecordBlock` | record literal / indented `field: Type` lines | `RecordLit` / `RecordTypeBlock` |
| `Params` | parenthesized parameter tuple | `ParamTuple` |
| `Duration`, `Percent`, … | whatever `literal` rules target | typed-literal kinds |
| `Edge`, `Clause`, … | whatever `is` creates | `category` declarations |
| `raw until <delim>` | verbatim text with srcloc (§13.2) | — (was a non-goal) |

**Refinement-typed holes**: `<port: Number where 1 <= port and port <= 65535>`
— Racket's parameterized syntax classes, expressed in machinery Cure already
has; the refinement failure feeds the default error.

**Default error machinery** (adopted from syntax-parse, which sets Racket's
error-quality ceiling; this sets the floor *before* any `explain` is
written):

- Every typed hole yields an automatic error: kind name + offending term +
  span (`every needs a Duration here, got "fast"`).
- Categories carry an optional `describe "transition edge"`; defaults name
  the category.
- When several rules could apply, the reported failure comes from the rule
  that parsed **furthest** (progress-ordered selection), with a parsing
  context trace: `while parsing transition edge … in reducer Door`.

**The rule is the documentation.** Strip the hole types and every `syntax`
rule *is* its usage line. Grammar rules are **declarative data**; three
structural dividends, stated as requirements: the LSP consumes the rule set
(per-dialect highlighting/completion with zero per-dialect work),
`cure <dialect> report`-style tools render any dialect's grammar as
documentation, and docs/completion snippets cannot drift from the grammar.

**Honest costs.** (a) `<` also appears in comparisons and `<|`: the lexing
rule is that `<` opens a hole iff immediately followed by an identifier (or
`fresh`/`capture`) closing with `: Kind>` or `>` on the same line —
`--<msg: Name>-->` lexes; `<|` is safe (next char `|`); escape hatch `\<`.
If implementation finds pathological cases, the severable fallback is the
`$name:Kind` sigil (Lean/Rust family) — everything else in this section
survives that swap. (b) Implicit categories trade a declaration for a typo
risk; the unknown-kind error above is the mitigation. (c) `becomes` merges
grammar and expansion, so context-dependent expansion has nowhere to live in
Tier 2 — deliberately: that *is* Tier 3, and forcing the escalation keeps
Tier 2 honestly simple.

## 3. The quoted-AST model

Every category (created by `is`, §2) **auto-derives a record/ADT type** for
its parse result (`Syntax(Edge)` ≈ `rec` with one field per hole, each
`is`-clause an ADT alternative). Elab functions (the targets of
`computed by`) are ordinary Cure functions over these types. `quote` builds
syntax values; `$( )` splices them *inside elab code* (the `<name>` form is
the rule/template notation of §2; inside `computed by` bodies, quoting keeps
`$()`); both are *typed against the category being built* — a `quote`
producing a malformed production is a compile error in the dialect itself,
not in its user's program.

This is the parent's assumption in the `reducer` worked example
(`schemas.map(fn(s) -> s.state)` — quoted decls as plain records) — adopted
here as the design: **derived typed ASTs, not a universal `Syntax` blob.**
(A generic traversal API over any syntax value exists underneath for tooling;
dialect authors normally never need it.)

## 4. Power tiers

One new keyword per rung, ordered as a learning ladder — nobody meets quoted
syntax before Tier 3. (Renumbered 2026-07-08 with the meta-grammar pass;
sibling specs citing the old numbering map 1→3, 2→2, 3→1, 4→4.)

| Tier | Mechanism | Who uses it |
|---|---|---|
| 1 | `literal` rules (`literal <n: Number> ms becomes Duration.ms(<n>)`) | units |
| 2 | `syntax … becomes …` (hygienic templates) | `every`/`on`, `secret` |
| 3 | `syntax … computed by f` (total compile-time Cure over quoted decls, `check … else fail`) | `boarddef`, `driver`, `packet`, `config`, `schema`, `parse` |
| 4 | Tier 3 + reflection API (§8) | `flow`, `reducer`, `view` |
| 5 | module rules + raw holes (§13.1–.2) | `board` module shaping (module-level `let`, auto `start/0`), `parse`-embedded surfaces |

A dialect declares nothing about its tier — it simply uses what it needs;
the tiers are a design/teaching taxonomy and a build-order (§10; Tier 5
lands with its consumers, not before).

## 5. Hygiene, expansion, termination

- `becomes` templates are **hygienic**: names introduced by the template
  cannot capture or be captured by user identifiers; `<fresh Name>` mints a
  readable unique name, identical at every mention within one rule (for
  generated containers that need stable-ish module atoms, e.g.
  `fsm <fresh Tick>` → `Cure.FSM.Tick$3`). Deliberate capture (anaphora —
  Racket's syntax-parameter use case) is a marked, greppable escape,
  `<capture it>`: ledgered §11.12 and classified under the holes/`unsafe`
  taxonomy, never silent.
- Templates may be **recursive** (a `becomes` expanding into its own or
  another dialect's syntax) provided a decreasing-input check passes — even
  recursive sugar provably terminates; the fuel bound below stays a
  backstop, not the guarantee.
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
  explicit (`<f: Packet.FieldDecl>`) — this is how `protocol` embeds `packet`
  payload declarations without owning them.
- **Open categories** (Racket's match-expander pattern, §13.3): a dialect may
  mark a category `open`; any other dialect then *extends* it with an
  ordinary rule — `syntax within <d: Duration> is Reducer.ClauseModifier`.
  Embedding (above) uses a category; extension grows one. Governance is
  ledgered §11.11.

**Composition is a full mechanism of its own** — theorem signatures
(`provides`/`requires` facts on the check-ladder trust rule), parameterized
categories (outer-dialect values as inner-dialect indices), seam explainers,
and composition templates — specified in
[`2026-07-08-dialect-composition-design.md`](2026-07-08-dialect-composition-design.md)
(operator-directed: stacked DSLs keep dependent types invisible while the
proofs still compose).

## 8. The Tier-4 reflection API — smallest thing that passes the dogfood

The one genuinely hard design. `reducer`'s `clause_to_arm` must build GADT
match arms and record literals *against types the same elab derived*; `flow`
must infer indices. The API is deliberately minimal, read-only toward the
elaborator, and **advisory** — nothing it returns is trusted (§9):

- `resolve(name) -> Sig | NotFound` — a global's/type's elaborated signature.
- `constructors(type_name) -> [CtorSig]` — for building matches.
- `infer(quoted_expr, env) -> Type | Error` — ask the elaborator to type a
  quoted term in a given quoted context (the expensive one; needed by `flow`).
- `expand(quoted, env) -> quoted | Error` — expand nested dialect syntax and
  inspect the result (Racket's `local-expand`; how whole-language dialects
  are layered — added by the §13 audit through this section's amendment
  rule).
- `lift(quoted_decl)` — emit a declaration at module top from a nested
  expansion (register-once tables, hoisted compiled grammars; §13.5).
  Template form: `<at module top>`. The one write-shaped member: it appends
  declarations, never mutates existing ones, so the read-only-toward-the-
  elaborator discipline survives.
- `fresh_name`, `fresh_meta`-free — no metavariable access; dialects never
  see or create holes (the K3 firewall applies to elab output).

Binding introspection (Racket's `free-identifier=?`-class questions —
keywords matched by *binding*, not spelling, immune to renaming/shadowing)
is `resolve`'s job and needs no separate member.

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
2. **Meta-grammar finalization** — notation adopted in §2 (2026-07-08
   Racket-audit pass: examples-with-holes, `is` categories, `...`/`?`,
   `becomes`/`computed by`). Remaining: layout-repetition interaction with
   the indentation-sensitive lexer, ambiguity policy (recommend: LL-style
   committed choice per leading token; a dialect whose rules are ambiguous
   against *imported* dialects is an error at import, computed from FIRST
   sets), and `<`-hole lexing edge cases (severable fallback: the
   `$name:Kind` sigil — §2's cost note).
3. **Two-pass details** (§6) — what exactly Tier-4 `declares` may compute
   (must not need the reflection API, or staging cycles return).
4. **Keyword conflict ergonomics** (§7) — `only`/rename surface.
5. **Reflection API completeness** (§8) — frozen until Gate 2 forces
   amendments (the §13 Racket audit already added `expand`/`lift` through
   the sanctioned route).
6. **Quoted-AST versioning** — a dialect compiled against category shapes
   that later change (compiler upgrades): derive-and-recompile is the answer
   for source packages; binary dialect distribution is a non-goal (§12).
7. **Migration of built-ins** — whether `fsm`/`actor`/`sup` actually move
   (Gate 1 only requires *could*); recommend: leave built-in until the
   facility is boring, then migrate one as a proof, keep the rest.
8. **`explain` registration mechanics** — deferred wholesale to the
   error-explainer spec.
9. **Module-rule mechanics** (§13.1) — trigger (board decl? explicit tag?),
   at-most-one module rule per module vs. composition when two imported
   dialects both declare one, and interaction with a hand-written `start/0`.
   Absorbs parent §9.14/§9.15 (module-level `let`, auto-`start/0`) — both
   are the `board` dialect's module rule, not compiler features.
10. **Raw holes** (§13.2) — delimiter inventory (`until dedent` /
    `until )` / `line`), srcloc threading tokenizer→parser→quoted AST, and
    the embedded-grammar coloring interface (a `parse` grammar exporting its
    own LSP token classes).
11. **Open-category governance** (§13.3, §7) — opt-in marker, extension
    ordering/ambiguity across extenders, whether extensions may shadow.
12. **`<capture>` escape** (§5) — exact semantics and its classification in
    the holes/`unsafe` taxonomy.

## 12. Non-goals

- No arbitrary compile-time effects in `elab` (no IO, no network, no
  filesystem) — purity is load-bearing (§5, §9).
- No binary/opaque dialect distribution — dialects ship as source packages.
- No reader-level lexer extensibility beyond `literal` suffix rules and
  **delimited raw holes** (§13.2 — carve-out forced by the operator's
  Racket-complete direction) — Cure's token grammar is otherwise fixed; a
  raw hole opts a delimited block's *content* out, never the file, and
  indentation structure stays sacred.
- No unbounded (Turing-complete) expansion — totality is the trade (§5,
  §13.6); a genuinely non-total metaprogram is holes/`unsafe`-taxonomy
  territory, a marked exception, never the default.
- No proof-producing macros / tactic framework — dialects generate programs,
  not proofs; obligations discharge by computation or become domain errors
  (hiding principle 3), and `check`'s certificate elevation is the sanctioned
  proof-automation path.

---

## 13. Racket-parity audit (operator direction, 2026-07-08)

Appended after the §1–§12 consolidation to keep cross-spec references
stable. Method: the facility as specified above, audited
capability-by-capability against the Racket Guide/Reference — the macro
tower including syntax-parse; the `#lang`/languages-as-libraries machinery
(`#%module-begin`, interposition points, readtables/readers, brag); and the
advanced tier (phases, compile-time state, `local-expand`, syntax
parameters, lifting, the macro stepper). Racket's power reduces to five
load-bearing mechanisms; the facility already covered three.

**Already equivalent or better:**

- `syntax-rules` / ellipses / hygiene → Tier 2 (`becomes`, `...`,
  `<fresh>`).
- syntax-parse (syntax classes, `#:description`, side conditions, auto
  errors) → typed holes, `is` categories, refinement-typed holes,
  progress-ordered default errors (§2), `check … else fail`.
- Procedural transformers (arbitrary code at compile time) → `computed by`,
  bounded to total (§13.6).
- Syntax parameters ("`break` legal only inside `loop`"; anaphora) → mostly
  free: block-scoped grammar makes "keyword legal only inside form X" a
  parse-level fact (`emit … is Action` exists only inside `reducer`) —
  Racket needs syntax parameters because its grammar is flat. True anaphora:
  the marked `<capture>` escape (§5, ledger §11.12).
- Phases (`for-syntax`, `for-meta n`, `for-template`) → sidestepped: elab
  code is ordinary total Cure staged at compile time, and
  dialects-defining-dialects works because the compile-time language
  includes the facility itself. Racket's per-module fresh compile-time
  instantiation — its mechanism for deterministic separate compilation — is
  subsumed by elab purity + totality (§5, §9).
- Compile-time data bus (`define-syntax`-to-a-value + `syntax-local-value`;
  struct-info records consumed by `match`/`struct-copy`/Typed Racket) →
  **the type system is the bus**: dialects emit types and globals; later
  code and other dialects read them through elaboration and §8 — checked,
  and nothing to teach. No mutable compile-time tables (none wanted: Racket
  itself bans them cross-module for exactly our determinism reasons).
- Syntax properties / `'origin` / `'disappeared-use` / srcloc → provenance
  is mandatory here (error-explainer spec), not per-macro diligence; and
  tooling derives from the declarative grammar, where Racket's `get-info`
  keys (color lexer, indentation, submit predicate, …) are each
  hand-written — a documented pain point of the `#lang` ecosystem (the
  color lexer is a second lexer kept in sync by hand).

**The five gaps, resolved below:** module dialects (§13.1), raw holes
(§13.2), open categories (§13.3), two reflection members (§13.4), lifting
(§13.5).

### 13.1 Module dialects (`#%module-begin` equivalence)

Racket's deepest hook: a language sees and transforms the **entire module
body** at once. It is where languages stop being sugar — auto-provides, run
loops, whole-program checks, and *subtracting* capabilities (a language
that simply doesn't admit `set!` or general recursion). The catalog already
needs it without naming it: `board :esp32c3` + module-level `let` +
auto-generated `start/0` *is* a whole-module transformation. A dialect may
declare one module-level rule:

```cure
dialect Board
  syntax module
    board <b: BoardName>
    <decls: Decl>...
  computed by board_module_elab   # sees ALL declarations; emits start/0 +
                                  # runtime boot + pin namespace; may reject
                                  # decls that don't belong on a board module
```

The user's file does not change by a character — `board :esp32c3` is the
trigger. Subtraction (a module admitting only a restricted surface —
Racket's whitelist-by-omission) falls out at the grammar level: the module
rule decides what the body admits. Absorbs parent §9.14/§9.15. Mechanics
ledgered §11.9.

### 13.2 Raw holes — the reader tier, bootstrapped through `parse`

Typed holes ride Cure's lexer; Racket custom readers parse anything
(`#lang datalog`, Scribble prose). Racket's canonical non-S-exp pipeline is
telling: lexer → brag grammar → parse tree whose node heads *are macro
names* — and brag is itself a `#lang`. Cure pulls the same bootstrap with
the `parse` dialect (total typed PEG parsers): one hole kind captures
verbatim text with source positions and hands it to a compile-time total
parser:

```cure
syntax datalog
    <rules: raw until dedent>
  computed by fn(rules) -> DatalogGrammar.parse(rules) |> compile_rules
```

Because the embedded grammar is declarative, syntax coloring derives for it
exactly as for dialect rules. Totality means a user's grammar cannot
catastrophically backtrack or hang the compiler — brag guarantees neither.
Deliberate scoping: raw holes are delimited blocks, never whole-file or
mid-expression reader replacement — composable, and the file stays
parseable by tools that don't know the dialect. (Amends non-goal §12;
delimiters/coloring ledgered §11.10.)

### 13.3 Open categories (match-expander equivalence)

Racket's deepest ecosystem pattern: `racket/match`'s pattern grammar is an
open namespace third parties extend (`define-match-expander`) — a DSL whose
grammar other DSLs grow, keyed by ordinary module bindings (imported,
renamed, hygienic). The composition spec covers *embedding* a category;
this covers *extending* one: `open` categories, extended with the syntax
that already exists (§7). One line, no new concept. Governance ledgered
§11.11.

### 13.4 Reflection API — two members added (through §8's amendment rule)

The audit pins what Tier 4 must offer: everything Racket's ecosystem builds
reduces to §8's queries plus two members, now added there —

- `expand` — Racket's `local-expand`: expand nested dialect syntax and
  inspect the result; how whole-language dialects (Typed-Racket-shaped) are
  layered as libraries.
- `lift` — §13.5.

Binding introspection needs no new member (`resolve`, per §8).

### 13.5 Lifting

A deeply nested expansion sometimes must emit module-level code —
register-once tables, hoisting a compiled grammar out of a function.
Racket: `syntax-local-lift-expression` and friends, among its most-used
advanced APIs. Here: `lift` in elab code (§8) and one readable template
marker:

```cure
becomes
  <at module top>
    let <fresh table> = Timer.registry()
  Timer.register(<fresh table>, <period>)
```

### 13.6 Where the facility exceeds Racket

The two things Racket's documentation concedes it cannot do are native
here:

- **Termination.** Racket expansion is Turing-complete with no totality
  claim — a self-expanding macro diverges. Elab functions are size-change
  total; recursive `becomes` templates pass a decreasing-input check (§5).
  User-defined syntax can never hang the compiler.
- **Type-directed expansion.** A Racket macro cannot ask what type a
  subexpression has; Typed Racket exists only via the whole-module
  `local-expand` trick, and a research literature (Turnstile, "Type Systems
  as Macros") exists precisely because the base system lacks it. Elab runs
  inside elaboration; `infer` is a query (§8).

Plus: deterministic builds from elab purity (Racket approximates this with
per-module compile-time re-instantiation), derived tooling (vs hand-written
`get-info` keys), mandatory provenance (vs per-macro `'origin` diligence),
and typed-hole default errors (vs opt-in syntax-parse discipline — Racket's
own docs are scathing about the floor without it: macros that "blithely
accept illegal syntax and pass it along to lambda, with strange
consequences").

### 13.7 Deliberately unmatched

- **Unbounded Turing-complete expansion** — traded for totality (§12).
- **`set!`-transformers / identifier assignment virtualization** — no
  mutation to virtualize.
- **Mid-expression reader replacement** (`#reader` splicing arbitrary
  syntax anywhere) — alien syntax is scoped to delimited raw holes
  (§13.2); a composability win, not a loss.
- **Macro-stepper parity is tooling, not facility** — declarative rules
  make an expansion stepper with dialect-hiding (show only *your*
  dialect's rewrites) nearly free; belongs to the toolchain spec.

None of these subtracts from any catalog entry or Racket showcase worth
replicating: Typed Racket ≈ module dialect + `expand` + `infer`; Scribble ≈
raw holes; datalog/brag ≈ `parse` + raw holes; match expanders ≈ open
categories.
