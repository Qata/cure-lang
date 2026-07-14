# Compile-Time Reflective BEAM Macros

**Status:** authoritative design for the remaining macro work

**Date:** 2026-07-14

**Applies to:** the macro facility, source-defined BEAM algebra, `actor`,
`fsm`, `sup`, `app`, and the final AtomVM integration work

## 1. Purpose

Cure is moving from compiler-owned OTP object classes to source-defined,
transparent macros. The final system must let a user define an actor-like
abstraction using the same language facilities used by the standard library.
The compiler may provide generic parsing, expansion, elaboration, reflection,
and code emission, but it must not contain an OTP object model or an OTP-
specific lowering case.

Macro interpretation is a compile-time computation. Its result is ordinary
Cure source syntax and declarations, which are parsed, elaborated,
kernel-checked, erased, and compiled into direct BEAM code. This document is
the design authority for resolving the remaining gaps. The autopilot plan
remains the chronological execution ledger and must be updated as each phase
lands.

## 2. Non-negotiable invariants

### 2.1 Compile-time only

Macro reflection and syntax values exist only while compiling. They must not
introduce any of the following into generated runtime code:

- a `Syntax` value or syntax interpreter;
- a dynamic macro dispatcher;
- a runtime type or tag test used to emulate macro expansion;
- an `EffectM` or free-monad interpreter for BEAM operations;
- an opaque container helper such as `__otp_container`;
- a second runtime object layer around processes;
- a runtime indirection solely because a construct was produced by a macro.

The output of a macro must be observationally equivalent to the code a user
would write by hand. Any runtime value that remains must be demanded by the
user's program or by the explicit BEAM operation itself, never by the macro
implementation.

### 2.2 Normal compilation after expansion

Every expansion follows the same path as handwritten code:

1. recursively expand nested macros from the inside out;
2. parse the resulting syntax and declarations;
3. resolve names and imports;
4. elaborate to Core;
5. normalize and kernel-check where required;
6. erase compile-time-only indices and evidence;
7. emit direct runtime code.

No macro-specific runtime path may bypass these stages.

### 2.3 User-definable vocabulary

The compiler owns generic mechanisms only. BEAM vocabulary, callback names,
behavior declarations, message-code derivation, state transitions, child
specifications, and application startup structure belong in Cure source files.
The standard library may define these as ordinary functions, syntax macros,
computed macros, data types, and explicit FFI declarations. Moving an
OTP-specific helper from the compiler into an Elixir helper is not sufficient.

### 2.4 No avoidable workarounds

An implementation must extend the generic language mechanism when the current
mechanism is insufficient. It must not preserve a bespoke compiler case,
require users to write declarations that the macro can derive, or hide a
missing normalization rule behind aliases, opaque helper calls, or runtime
dispatch.

## 3. What is already useful and remains

The following work is foundation and must be preserved:

- local syntax macro parsing and use-site expansion;
- recursive inside-out computed expansion;
- active-stack cycle detection with an infinite production budget;
- expansion provenance and callback context plumbing;
- hygienic fresh names and metadata-aware substitution;
- typed repeated syntax fields represented as `List(Syntax)`;
- `Std.Syntax` as a real reflected Cure ADT;
- source-level syntax builders and `lift_module` construction;
- declaration-position computed expansion before `LiftModule.collect`;
- compile-time totality closure for ordinary helper functions;
- the expansion soundness firewall and generative macro checks;
- generic, qualified import resolution in ordinary elaboration;
- the checked BEAM process algebra and raw foreign boundary;
- the transparent source-level actor prototype and its end-to-end tests.

Some current standard-library macro bodies are exploratory implementations.
They may be replaced by more general source-level analyzers, but the parser,
reflection bridge, expansion engine, declaration ordering, and proof gates are
not throwaway work.

## 4. Research conclusions

### 4.1 Racket: bindings are not names

Racket syntax objects combine datum with lexical scopes, source information,
and properties. Expansion recursively processes syntax objects at phase levels;
binding identity is determined by scope sets and phase, not by comparing the
printed symbol. This is the relevant lesson from the local Racket checkout at
`/Users/ch/Develop/racket`, especially its syntax model and expander sources.

Cure does not need to reproduce Racket's complete scope-set implementation in
this phase. It does need the same separation of concerns:

- syntax inspection is structural and staged;
- name resolution produces binding identity before evaluation;
- generated identifiers carry hygiene information;
- macro expansion is recursive parsing, not string substitution followed by a
  special OTP compiler.

### 4.2 Dependent type reflection and normalization

The local research corpus contains the most relevant implementation-oriented
papers:

- de Moura et al., *Elaboration in Dependent Type Theory*
  (`1505.04324`): elaboration turns incomplete surface input into explicit
  terms and uses computational reduction while solving constraints.
- Vivekanandan, *Code Generation for Higher Inductive Types: A Study in Agda
  Metaprogramming* (`1808.08330`): Agda elaborator reflection exposes typed
  quote/unquote and declaration construction rather than asking a runtime
  interpreter to inspect code.
- Ullrich and de Moura, *Beyond Notations: Hygienic Macro Expansion for
  Theorem Proving Languages* (`2001.10490`): hygiene is applied at the
  elaborator boundary so later phases do not need to know how it was achieved.
- Jang et al., *Moebius: Metaprogramming using Contextual Types*
  (`2111.08099`): contextual types describe open code together with the
  context in which it is valid, and typed pattern matching can inspect code.
- Kovacs, *Staged Compilation with Two-Level Type Theory* (`2209.09729`):
  staging-by-evaluation gives code generation through a semantic domain and
  preserves conversion rather than manipulating arbitrary ASTs.
- Hu and Pientka, *DeLaM: A Dependent Layered Modal Type Theory for
  Meta-programming* (`2404.17065`): typed, layered code inspection and
  recursive code manipulation can coexist with decidable conversion.
- Christiansen and Brady, *Elaborator Reflection: Extending Idris in Idris*
  (ICFP 2016): a metaprogram inspects reflected clauses (`lookupFunDefnExact`
  returns a function's defining clauses) and emits top-level declarations
  (`declareDatatype`, `defineFunction`) through the same elaborator that
  checks handwritten code. The representation is typed core syntax (`Raw`
  elaborated to `TT`), not a semantic domain. This is the closest living
  precedent for `derive_actor`, and — since Cure targets Idris parity — the
  primary model to follow.
- Altenkirch and Kaposi, *Normalisation by Evaluation for Type Theory, in
  Type Theory* (`1612.02462`): normalisation-by-evaluation yields decidability
  of definitional equality for dependent type theory. This is the
  conversion-decidability foundation the reflection layer must respect, and an
  exemplar of the tradition beneath Kovacs's staging-by-evaluation. Its theory
  has no primitive-literal layer, so it does not by itself license reducing
  `atom == atom` — that is a separate primitive-reduction completeness fix
  (§5).

These papers do not agree; the corpus splits into two camps. The
*semantic/staging* route (Kovacs; Altenkirch-Kaposi underneath) buys decidable
conversion precisely by **forbidding** intensional inspection of object code.
The *typed-syntactic/modal* route (Christiansen-Brady's Idris reflection,
DeLaM, Moebius; and pragmatically Lean 4 macros) keeps decidable conversion
**while** inspecting code, by working over typed modal or contextual *syntax*
rather than a semantic domain.

Cure's design inspects code: `derive_actor` traverses a `Std.Syntax` ADT,
classifies handler arms, and emits declarations. It therefore belongs to the
typed-syntactic camp, not the semantic one. The correct consequence is that
the next reflection work is a typed, **compile-time syntactic** reflection
interface (Idris-elaborator-reflection-shaped), never a *runtime* `Syntax`
evaluator, and it must preserve decidable conversion in the Altenkirch-Kaposi /
Kovacs sense. The existing `Std.Syntax` ADT and `MacroSyntax` bridge are the
beginning of this interface.

## 5. Atom equality normalization

### 5.1 The gap

Reflected syntax tags are atoms. A generic source-level helper such as:

```cure
fn has_tag(syntax: Syntax, expected: Atom) -> Bool = tag(syntax) == expected
```

is valid Cure, but the compile-time evaluator currently does not normalize
equality between atom literals. This makes generic structural analyzers
artificially unable to branch on a reflected tag. Avoiding the comparison in
one macro is not a complete language solution.

### 5.2 Correct solution

Atom equality must be implemented as a normal compile-time computation in the
primitive-reduction layer, subject to the same termination and conversion rules
as existing primitive literal reductions. Concretely: `==`/`!=` on non-numeric
operands already elaborate to the polymorphic `struct_eq`/`struct_ne` global,
whose reduction fold currently fires only for numeric literals (`{:vint,_}` /
`{:vfloat,_}`). The fix is to extend that existing fold with an `{:vatom,_}`
clause, mirroring the numeric case — not to introduce a new atom-specific
reduction rule. (Atom *values* are already compared in the conversion layer;
this closes the parallel gap in `==`/`struct_eq` reduction.) The reduction
must:

- reduce equality of two known equal atom literals to `true`;
- reduce equality of two known distinct atom literals to `false`;
- leave equality involving a neutral or unknown atom unreduced;
- preserve symmetry and congruence;
- avoid equating atoms with any other primitive or syntax constructor;
- have no special knowledge of OTP, macros, or `Std.Syntax`.

This is a completeness fix to primitive reduction, not a runtime feature and
not a macro-specific escape hatch. It may touch the trusted reduction layer
only under the full TCB bar already recorded in the autopilot state:
red-green tests, termination coverage, no-new-equations coverage, the complete
Antigen gate, and the complete ExUnit gate. No runtime atom-discrimination
helper may be added as a substitute.

### 5.3 Required proof cases

The implementation must cover at least:

1. `:node == :node` normalizes to `true`;
2. `:node == :leaf` normalizes to `false`;
3. `tag(Node(...)) == :node` reduces through the reflected syntax builder;
4. an open atom variable remains neutral;
5. atom equality is not convertible with integer, boolean, or string equality;
6. nested equality computations terminate by structural descent;
7. generated macro code contains no runtime tag comparison introduced by this
   feature.

## 6. Qualified names in staged elaboration

Every global reference in a computed callback must resolve to the same stable
registry key used by ordinary module elaboration. For example, unqualified
`map` imported from `Std.List` must become `:"Std.List#map"` in callback Core
when that is the binding selected by the importing environment.

The fix must be in generic name resolution, not in `actor.cure` and not in a
fully qualified spelling forced on macro authors. Ordinary expressions,
callback bodies, generated helper functions, and nested macro callbacks must
share this resolution path. The totality checker must receive qualified Core
globals and reject only genuinely unknown or non-total definitions.

Required tests include an imported helper used unqualified in a callback, a
local definition shadowing an imported helper, a qualified callback call, a
nested callback using a transitive import, ambiguous imports, and a proof that
no bare dangling global remains before compile-time certification.

## 7. Typed staged reflection

### 7.1 Reflection object

`Std.Syntax` remains a compile-time data type. It is not emitted into runtime
modules. Its constructors and builders must be sufficient to inspect and
construct ordinary Cure syntax, declarations, blocks, and lifted modules.

Reflection must carry a typed expansion context when a delayed callback is
interpreted. The context is compile-time metadata and may include the enclosing
declaration kind, callback name and arity, parameter names and syntax,
declared return type syntax, state and message/event type syntax when
available, and source provenance for diagnostics.

The context must be explicit in the reflected input, not recovered by an
OTP-specific compiler branch. If a callback needs more context, extend the
generic staged input record so the context is supplied as typed input.

Note on `contextual`: in the current implementation `contextual` is a
macro-*rule* flag, not a callback marker. Its only operational effect is to
exempt the rule from the standalone expansion-soundness proof — the MacroFuzz
generative firewall records such rules as `deferred` rather than proving them
in isolation — because the rule's template contains free type holes that are
only resolvable once a use site supplies the enclosing types. It does not defer
elaboration and does not leave a metavariable unsolved. The goal is to retire
the *need* for this proof exemption by deriving message/callback types (§9), so
that the transparent rules either disappear or become provable standalone — not
to "unmark" a callback. Retiring `contextual` therefore depends on the
derivation work and cannot precede it (see §11).

### 7.2 Structural analysis

Generic syntax operations may include structural traversal, constructor views,
attribute lookup, list traversal, literal inspection, and declaration
construction. They must not encode actor, FSM, supervisor, or application
semantics in `Std.Syntax`.

Actor-specific interpretation belongs in `actor.cure`; FSM-specific
interpretation belongs in `fsm.cure`; shared generic syntax mechanics belong in
`Std.Syntax`. This preserves user extensibility while allowing lexical reuse of
ordinary Cure functions.

### 7.3 Hygiene and scopes

Generated bindings must remain hygienic. Existing `<fresh Name>` support is a
valid foundation, but declaration-producing reflection must also ensure that
generated nominal type names do not collide with user declarations, generated
callback helpers cannot capture use-site variables, user syntax retains its
intended bindings, and generated declarations resolve in their insertion
environment.

The implementation may use Cure's deterministic gensym mechanism while richer
scope representation is developed. It must not use runtime names or string
post-processing as a substitute for compile-time binding tracking.

## 8. Declaration-producing expansion

A computed declaration can produce more than one compile-time artifact. The
required result model is a syntax block containing ordinary declarations and a
lifted module, or an equivalent typed declaration bundle. The generic pipeline
must:

1. expand nested computed uses inside the declaration;
2. splice every produced declaration into the surrounding declaration stream;
3. register generated nominal types before generated functions refer to them;
4. collect `lift module` requests only after expansion;
5. elaborate the lifted module in an environment containing generated
   declarations, imports, macros, and ordinary helpers;
6. preserve enclosing source provenance and hygiene.

The generated message type must be one nominal declaration shared by the
handler module and external callers. Reconstructing an equivalent anonymous
union at each use site is not acceptable.

## 9. Source-level derivation of process codes

### 9.1 Actor and FSM message types

`actor` and `fsm` should infer their message/event code from handler clauses
when the input is derivable. An explicit `messages <Type>` or `events <Type>`
annotation remains a supported override, but is no longer the required normal
path.

Derivation must inspect handler syntax at compile time and produce a nominal
message/event type declaration, any aliases needed by generated callbacks, the
callback declarations and behavior metadata, and the lifted module containing
direct BEAM code.

The derived type must be the same type used by `Pid(m)`, `send`, `call`, and
external constructors. Type indices and message codes are erased from runtime
values; they exist to check the program before emission.

### 9.2 Soundness policy

Derivation must reject, with a source diagnostic, handlers that cannot yield a
closed and correct code set. In particular, reject or require an explicit
override for catch-all or variable-only arms, guards whose accepted set cannot
be represented, duplicate or overlapping constructor heads with incompatible
payload views, non-exhaustive handlers when totality is required, reply types
that cannot be inferred from `handle_call`, and malformed callbacks.

The macro must never guess a narrower message type and thereby manufacture an
unsound `Pid(m)`.

### 9.3 Shared construction

Common syntax traversal and declaration construction may be ordinary reusable
Cure functions. They are not actor-specific compiler helpers. A local macro or
shared builder may return a syntax block, but it must remain transparent and
must not hide an opaque container call.

### 9.4 Reply channels

`handle_call` induces a request-reply exchange, and its reply type is part of
the derived contract. The reply is not a bare value type; it is a one-shot
typed channel. Following the typed-actor idiom (mailbox types,
`docs/research/process-types/`), the caller allocates a fresh single-use
process reference typed to accept exactly one reply message `Reply(T)`, and
passes the *output* capability to the actor as a payload of the call message;
the caller retains the *input* capability and waits on it. The derived message
type for a `handle_call` clause therefore carries a `Pid(Reply(T))`-typed
field, where `T` is the reply type inferred from the clause body. This typing
yields forgotten-reply and caller self-deadlock detection, and erases to an
ordinary BEAM reference at runtime.

### 9.5 Scope of the message discipline

`Pid(m)` for v1 is a nominal message type — the closed set of message
constructors an actor accepts — plus the one-shot reply channels of §9.4. This
is a legitimate "typed channels v1": it delivers **send-conformance** (a
`send`/`call` cannot carry a constructor the actor does not handle), which is
the primary safety property, and it is exactly what the derivation produces. A
constructor set is therefore not under-powered for v1.

The following richer mailbox-type disciplines are explicitly **out of scope for
v1** and belong on the roadmap, in priority order:

- *typestate / protocol state* — a message type that evolves as messages are
  consumed (e.g. "handle `Init` before any `Request`"), expressible as the
  residual of a commutative-regex mailbox pattern. This is the only discipline
  that structurally exceeds a constructor set, and the primary future target;
  it is also the most inference-hungry (Special Delivery names inference as the
  open usability problem).
- *multiplicity* — bounds on how many of each message may be pending (e.g. "at
  most one `Config`").
- *junk-freedom* — a static guarantee that no message is left unconsumed.

Adopting any of these must not weaken the v1 send-conformance guarantee or
introduce a runtime mailbox interpreter.

## 10. BEAM algebra and direct lowering

The checked BEAM algebra remains a standard-library layer over honest raw
foreign operations. It describes typed operations such as process creation,
message send, receive, call/reply, links, monitors, and supervision. Its types
and evidence are checked at compile time and erased where appropriate.

`beam_ops` is a source-defined macro over that algebra. It must expand into
ordinary operation composition and direct FFI-facing code. There is no runtime
operation interpreter. The generated module must contain the calls and control
flow required by the requested operation sequence, just as handwritten code
would.

The four standard macros are thin adapters:

- `actor.cure` derives message code and emits actor callbacks;
- `fsm.cure` derives event code and emits transition callbacks;
- `supervisor.cure` validates child declarations and emits supervisor code;
- `app.cure` emits application startup and supervision wiring.

The compiler must not recognize these four names specially. A user-defined
macro that emits the same generic declaration vocabulary must use the same
pipeline.

## 11. Required implementation order

Implement in this order; do not use a later layer to paper over an earlier gap:

1. **Core primitive reduction:** add and prove compile-time Atom equality.
2. **Staged name resolution:** ensure callback globals are fully qualified.
3. **Typed callback context:** supply the enclosing declaration/callback
   context as explicit typed staged input, so no callback relies on context
   recovered by a bespoke compiler branch. (Retiring the `contextual`
   proof-exemption is *not* this step — it depends on derivation and lands in
   step 10; see §7.1.)
4. **Declaration bundles:** support generated nominal declarations plus lifted
   modules in one expansion.
5. **Generic syntax analysis:** add the structural traversal and declaration
   builders needed for derivation.
6. **Actor derivation:** remove the required explicit message type in the
   inferred path and test external `Pid(m)`/`send` calls.
7. **FSM derivation:** derive events and transition contracts.
8. **BEAM algebra integration:** make `beam_ops` use derived codes and direct
   operation expansion.
9. **Supervisor and application parity:** complete `sup` and `app` using the
   same source vocabulary.
10. **Compiler cleanup:** remove every bespoke OTP object path and forbidden
    opaque helper, and retire the `contextual` proof-exemption once the derived
    rules (steps 6–7) have replaced the transparent templates that required it —
    every remaining rule must then pass the standalone expansion-soundness
    proof rather than being recorded `deferred`.
11. **Branch integration:** merge `kernel-parity-batch` into `idris-parity`,
    then merge `idris-parity` into `core-let-binder`, resolving in favor of
    source-defined macros and the generic pipeline.
12. **Runtime gates:** run Unix and generic-unix AtomVM proofs, then focused,
    full-suite, Antigen, formatting, and warnings-as-errors gates.

Every item is a phase with a descriptive commit. Run `mix format` after each
phase commit and commit formatter changes separately when they occur.

## 12. Verification requirements

Each phase must include focused tests and preserve the full existing suite. The
final gate must prove that transparent macros expand recursively and terminate;
callback helpers normalize and resolve through imports; Atom equality is
compile-time reduction only; generated declarations are nominally shared and
type-correct; no reflection or syntax values remain in runtime code; emitted
actor/FSM/supervisor/application code has no macro interpreter; direct BEAM
operation calls match handwritten behavior; all four standard macros work on
Unix and AtomVM; the compiler has no OTP-specific object cases or opaque
container helper; the required merge order is complete; and all test, Antigen,
formatting, and warnings-as-errors gates pass.

Useful negative tests must assert that generated runtime code does **not** call
any syntax interpreter, macro dispatcher, or opaque OTP container helper.

## 13. Design references

Repository references:

- `docs/superpowers/specs/2026-07-09-typed-beam-process-algebra-design.md`
- `docs/superpowers/specs/2026-07-12-tier3-computed-by-execution-design.md`
- `docs/superpowers/specs/2026-07-13-transparent-beam-algebra-otp-macros-design.md`
- `docs/superpowers/plans/2026-07-12-macro-facility-autopilot-state.md`
- `docs/research/metaprogramming/`
- `docs/research/process-types/`

External research:

- https://arxiv.org/abs/1505.04324
- https://arxiv.org/abs/1808.08330
- https://arxiv.org/abs/2001.10490
- https://arxiv.org/abs/2111.08099
- https://arxiv.org/abs/2209.09729
- https://arxiv.org/abs/2404.17065
- https://arxiv.org/abs/1612.02462
- Christiansen and Brady, *Elaborator Reflection: Extending Idris in Idris*,
  ICFP 2016
- https://arxiv.org/abs/1801.04167 (Mailbox Types for Unordered Interactions)
- https://arxiv.org/abs/2306.12935 (Special Delivery: Programming with Mailbox
  Types)
