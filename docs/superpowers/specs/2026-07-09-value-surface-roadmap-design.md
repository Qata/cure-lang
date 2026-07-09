# Value-Surface Parity Roadmap — Design (task #23)

**Date:** 2026-07-09. **Operator order:** "bringing string literals, lists, tuples, records, lambdas, matches, pickup, and whatever else into our dependent pathway." This program teaches the dependent pipeline (`lib/cure/elab/*` + `lib/cure/core/*` + `elab/emit.ex`) the value surface that classic `Codegen` compiles today, so the classic rip-out (#18) can re-run without amputating the language.

**Backing artifact:** `2026-07-09-value-surface-gap-matrix.md` (scout inventory — parser forms × dependent coverage × Core targets × std ratchet; anchors verified 2026-07-09). This roadmap SEQUENCES that matrix; each wave gets its own detailed spec+plan when picked up.

## 0. Program invariants

- **Firewall (already landed, 8d7a5eb):** no `lib/cure/elab/*` or `lib/cure/core/*` file may reference `Cure.Types`/`Codegen`/`PatternCompiler`/FSM/Actor/Sup/App/Optimizer/PGO/ProtocolRegistry. Every wave stays green under it. Classic files are the SEMANTICS reference (read them), never a runtime dependency.
- **Ratchet:** the stdlib-disposition count (modules that `Cure.Elab.Program.elaborate/1` accepts) starts at **8/39** (bool, bounded, decision, equivalent, nat, proof, sigma, vector) and must climb MONOTONICALLY. Each wave's spec names the modules it is expected to move from FAILS→KEEP; the wave's gate re-runs the disposition script and asserts the named modules flipped and NONE regressed. This is the program's objective progress metric.
- **Oracle:** where a form's runtime semantics are subtle (pickup terminator, list cons cells, string encoding, extern remote-call shape), the classic test file named in the gap matrix §4 is the behavioral oracle — the ported form must produce equivalent BEAM behavior, verified by a directed test that mirrors the classic pin.
- **TCB discipline:** waves that add a Core node or builtin family (String, List, Map) touch `lib/cure/core/*` — HARD-STOP-and-review each, with an Antigen antibody proving the new former/eliminator adds no unsound conversion. Waves that only add elaborator clauses + emit lowering (pickup, lambda-inference, extern-call) stay out of the kernel.
- Standard constraints: ghost commits, explicit pathspecs, ONE mix at a time, strict red-green, tests immutable. Each wave = full mini-chain (spec → Sonnet review → plan → review → Opus execute).

## 1. The two cross-cutting decisions (locked here)

### D1 — List is a builtin inductive family with native-cons emit (NOT plain Std.List, NOT native-only)
The kernel already has the precedent: `Bool` erases to BEAM atoms, `Nat` to integers, `Sigma` to a bare 2-tuple (emit.ex:162-174) — inductive families in the kernel, native representation at runtime. List follows exactly: seed a builtin family `List(a: Type)` with `Nil`/`Cons`, and give emit a special lowering `Nil → []`, `Cons(h,t) → [h | t]` (native cons cells), overriding the generic tagged-tuple ctor lowering. This keeps list programs kernel-checkable (real inductive, real eliminator, dependent `length`-style indexing available later) AND interoperable with `:lists` BIFs and the extern surface (which pass native lists). List patterns `[h|t]`/`[]` desugar to `Cons`/`Nil` constructor patterns — the dependent matcher already handles constructor patterns. Rejected: plain `Std.List` inductive (tagged tuples break FFI + oracle); native-only lists (unkernelable, no dependent indexing, reintroduces an untyped value class).

### D2 — @extern reuses the #15 builtin-op registry mechanism
`@extern(:mod, :fun, arity)` becomes a body-less global carrying an `extern: {mod, fun, arity}` marker on its def record — structurally identical to #15's `builtin_op` marker (a body-less def the emitter recognizes). Elaborator registers the typed head with the marker and NO body (the type is declared, so type-checking is unaffected; there is nothing to reduce, so normalization treats it as neutral — same as a builtin-op global used below saturation). Emit lowers a saturated application of an extern global to a remote call `{:call, {:remote, line, {:atom,mod}, {:atom,fun}}, args}`; unsaturated uses curry through a wrapper (same shape as the builtin-op wrapper). This is the cleanest reuse of an already-proven registry pattern and keeps extern OUT of the kernel entirely (no Core node; the kernel never sees a body). **Sequencing consequence:** the extern *mechanism* is cheap and independent, but the 100%-extern modules (crdt/string/regex/http) stay FAILS until their signature TYPES (String, Map, List) are representable — so extern lands AFTER the core types, not first, despite being the highest raw unlock.

## 2. Wave ordering (by dependency + cost, not raw unlock)

Full module closure needs ALL a module's gaps; the ratchet advances when a module's LAST gap closes. Ordering builds capability bottom-up and front-loads the cheapest de-risking wave.

- **Wave 1 — pickup (G2).** Pure value surface, direct existing Core target (desugar to nested `{:case}` on Bool, exactly like `if`). No new primitive, no kernel change, no representation decision. Warm-up that de-risks the elaborator-clause + oracle harness. Oracle: `pickup_test.exs` (terminator mandatory, Bool guards, branch-type join). Ratchet: enables the pickup capability; fully closes nothing alone but unblocks the pickup half of 10 modules.
- **Wave 2 — List (G3, D1).** Builtin family + literals `[…]` + cons `[h|t]` + list patterns + native-cons emit. Kernel change (new seeded family) → antibody. Fully closes **match, non_empty**. Biggest structural unlock. Oracle: `codegen_test.exs` lists, `pattern_compiler_test.exs`, `multi_head_cons_test.exs`.
- **Wave 3 — lambda-in-inference + HOF expected-type propagation (G6).** Elaborator-only (checked-mode lambda already works; add inference-position + thread expected Π into HOF args). Fully closes **option, result**; enables iter/set/list HOFs. Oracle: `lambda_block_test.exs`.
- **Wave 4 — String (G4).** New `{:string_type}`/`{:string_lit}` Core nodes + `str_*` builtin ops + `<>` binop + emit→`{:bin}` + string patterns. Kernel change → antibody. Locks the "String as builtin primitive vs List Char" question toward builtin primitive (parallels Int/Float; matches the locked never-candidate stance in kernel-primitive-endgame). Oracle: `codegen_test.exs` strings.
- **Wave 5 — @extern (G1, D2).** Registry-marker global + remote-call emit. No kernel change. Now the signature types from Waves 2/4 exist, so this lights up crdt/string/regex/http/io/time/system/gen/json and the extern halves of others. Oracle: E056/E057 head/no-body rules, remote-call shape.
- **Wave 6 — Map (G8) + tuples≥3 (G7) + interpolation (G9) + comprehensions/ranges (G10).** Map is a new builtin (or extern-backed opaque — decide in the wave spec); tuples≥3 via nested Sigma sugar or new builtin; interpolation rides String; comprehensions/ranges desugar to List+recursion (ride Wave 2). Closes map/json/http/pair and the long tail.
- **Deferred (own tracks, NOT this program):** binary/bitstring (G11 — new builtin, low unlock); effect forms send/throw/early_return/try/async (G12 — belong to the Effect-in-Core and typed-BEAM-process-algebra tracks, see those memories). Atoms (G5) fold into ADT ctors + extern; a residual dynamic-atom need, if any surfaces, gets its own small wave.

## 3. Per-wave gate (uniform)

1. Red-first tests for each ported form (directed, mirroring the classic oracle).
2. Scoped `mix test` on the touched dirs green; then full suite ONCE, 0 failures, arithmetic reconciled.
3. Firewall test green (no classic reference leaked in).
4. Disposition script re-run: named modules FAILS→KEEP, none regressed, count strictly up.
5. Kernel-touching waves (2, 4, 6-Map): Antigen antibody + full Antigen suite + the TCB review bar.
6. Oracle equivalence: the directed test matches the classic behavioral pin.

## 4. Completion → #18 re-run

When the ratchet reaches the target (all value-surface std modules KEEP; the deferred G11/G12 modules are the only permitted residual FAILS, explicitly listed), the classic rip-out re-runs: the hardened `2026-07-09-classic-ripout-design.md` spec + `2026-07-09-classic-ripout-plan.md` re-execute with §3 revised (the value surface no longer hard-fails), and the STOPped executor's stashed 257-file deletion WIP is the starting point. #21 typeclasses follows, restoring Equatable/Ord/Show/Functor as real interfaces.

## 5. Out of scope

fsm/actor/sup/app/proto/impl (die in the rip-out, not ported); parser grammar changes (the forms already parse); the #22 canonical-spelling kernel batch (disjoint K-layer, runs in parallel); performance of the ported forms (correctness-first; optimize later if measured).
