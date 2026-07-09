# Value-Surface Wave 2 — `List` builtin family — Design (task #23, Wave 2)

**Date:** 2026-07-09. Second wave of the value-surface parity program (roadmap `2026-07-09-value-surface-roadmap-design.md` D1, hardened fcc768d; program memory `value-surface-parity-program`). Brings `List` and its surface sugar (`[]`, `[h | t]`, `[a, b, c]`) into the DEPENDENT pipeline as a **builtin inductive family with native BEAM-list emit**, following the exact precedent by which `Bool`→atom, `Nat`→integer, and `Sigma`→bare-2-tuple are handled. Runs after Wave 1 `pickup` (landed `f3c0b46`) and after the #22 canonical-spelling kernel batch (landed `7b7f071`+`ea5abbd`).

## 0. Premise (proven by the Wave-2 scout; do not relearn)

- **`List` is a plain 2-ctor `data` inductive — NO Core/TCB change.** `lib/cure/core/term.ex:11-26` enumerates the entire Core grammar (`type/var/pi/lam/app/data/ctor/case/global/int_type/int_lit/float_type/float_lit`); there is no list, cons, or string node, and none is needed. `List` is `{:data, :List, [elemT], []}` with `{:ctor, :Nil, []}` / `{:ctor, :Cons, [h, t]}`. "Nativeness" is an **emit-layer** concern only, exactly as Sigma stays a plain `data` family yet emits as a bare 2-tuple. The kernel (`lib/cure/core/*`) is untouched — the firewall and the #22 gains are preserved.
- **The classic pipeline is a decoy.** `lib/cure/compiler/{codegen,pattern_compiler}.ex` and `lib/cure/types/*` handle lists too, but they are the non-dependent pipeline being deleted. Every change here lands in `lib/cure/elab/*`, `lib/cure/elab/emit.ex`, `lib/cure/core/builtins.ex` (schema only), and `lib/std/list.cure`. Read classic only as a behavioral oracle.

## 1. The four moving parts

### 1.1 Seed the `:list` family (so `[…]` sugar resolves in every module)

`Bool`/`Nat`/`Sigma` are each **seeded programmatically** into every module's base env AND **declared** in their `std/*.cure` with a `@builtin(:key)` decorator. List follows the same dual pattern.

- **Schema:** add `list: [{:Nil, 0}, {:Cons, 2}]` to `@schemas` in `lib/cure/core/builtins.ex:14-19`. Ctor **names and arities are load-bearing** — erasure and emit key off `:Nil`/`:Cons` nominally (via the registry, not bare atoms).
- **Seed:** extend `Builtins.seed/2` (`builtins.ex:103-111`) with a `maybe_seed(:list, …)` link in the chain, using `declare_and_register/4` (`builtins.ex:177-182` → `Inductive.declare` → `validate!` → `Inductive.register_builtin(env, :list, fid)`). This makes the `List` family + `Nil`/`Cons` ctors resolvable in **every** module's base env, so the list literal sugar works without `use Std.List` — the same reason Sigma is seeded (its `%[a,b]` and `.1`/`.2` sugar must resolve everywhere).
- **Rationale (decided, lower-risk):** List is seeded, **NOT** added to `@auto_prelude` (`program.ex:234`). `@auto_prelude` imports a module's function *globals* into every module (e.g. `sigma_first`); List needs only its *family + ctors* available everywhere (for the literal sugar), which the seed provides. `Std.List`'s functions (`map`, `filter`, …) continue to require an explicit `use Std.List`. This avoids the auto-prelude qualifier's "must fully dependent-elaborate" coupling (`program.ex:218-233`) and any bootstrap-cycle risk.

### 1.2 Declare `List` in `std/list.cure`

`lib/std/list.cure` currently **references** `List(T)` as a bare magic type name but never declares it (scout item 3). Add, near the top of `mod Std.List`, the canonical declaration with the builtin decorator:

```
@builtin(:list)
type List(a) = Nil | Cons(a, List(a))
```

`Std.List` is a prelude-source key (`prelude_source?/1` at `program.ex:215-216` consults `Cure.Stdlib.Preload.module_groups()`, which walks `lib/std/*.cure` — so any declared `mod Std.X` qualifies). Thus `maybe_register_builtin` (`program.ex:742-753`) schema-validates and registers this declaration when `Std.List` elaborates. **Idempotency:** the family is already seeded (§1.1), so the source registration must reconcile to the SAME family id (`Inductive.register_builtin` is idempotent to the same fid, hard-errors on a different fid — `inductive.ex:178-192`). Follow the Bool/Nat/Sigma precedent exactly (the "builtin-seed skip" reconciliation referenced at `program.ex:239`): the source `@builtin` declaration of an already-seeded family must NOT mint a second fid. The executor verifies Bool/Nat/Sigma's mechanism and mirrors it; if the seed and the source declaration cannot be reconciled to one fid via the existing precedent, that is a STOP-and-report (do not invent a new reconciliation path).

### 1.3 Desugar `:list` surface nodes → `Nil`/`Cons` ctor form (LOCKED: option i, one early pass)

The parser emits a single tag `:list` for every list form (`parser.ex:759-843`, scout item 4):
- `[]` → `{:list, [line, col], []}`
- `[h | t]` → `{:list, [cons: true, line, col], [head, tail]}` (the `cons: true` meta flag marks a cons cell)
- `[a, b, c]` → `{:list, [line], [a, b, c]}` (literal, N heads, no `cons` flag)
- `[a, b | rest]` → right-nested `{:list, [cons: true], [head, nested]}` chains (`build_multi_head_cons/3`, `parser.ex:837-843`)

**Design fork resolved (scout item 5c; prose-fork guidance → lower-risk):** rather than adding parallel `:list` clauses at every elaboration + pattern + exhaustiveness site, **desugar `:list` nodes to the existing constructor form** (`{:function_call, [name: "Cons"/"Nil", …], args}` — the same shape `Vector`'s `prepend()`/`empty()` use) in **one early normalization pass**, so all downstream ctor/pattern/exhaustiveness/refinement machinery is reused verbatim. The desugaring:
- `{:list, _, []}` → `Nil` nullary ctor call.
- `{:list, [cons: true, …], [h, t]}` → `Cons(desugar(h), desugar(t))`.
- `{:list, _, [e1, …, eN]}` (literal, no `cons`) → right fold: `Cons(e1, Cons(…, Cons(eN, Nil)))`.
- Recursive: sub-elements/sub-patterns are themselves desugared (a list of lists, a cons whose tail is a literal).

This must cover **both expression position and pattern position** (a `:list` node appears identically in a `match` arm's `:pattern` meta — scout item 4). The executor decides the exact insertion point (a dedicated normalization over the surface AST before elaboration, OR a `:list` clause in each of `elaborate_expr_typed`/`elaborate_expr_checked`/`elaborate_expr` + the pattern path that immediately rewrites-and-delegates). The **normalization-pass** shape is preferred because it guarantees uniform coverage of all four parser shapes in every position with no site left behind; if the executor finds a pre-elaboration surface-rewrite hook already exists (e.g. where other sugar like `.1`/`%[..]` is desugared), reuse it. Either way the observable contract is: after this pass, no `:list` node survives to reach an elaborator dispatcher.

### 1.4 Native BEAM-list emit

`lib/cure/elab/emit.ex` special-cases builtin ctors in `lower(env, {:ctor, name, args}, ctx)` (`emit.ex:162-182`) and in branch lowering (`branch_clause/3`, `emit.ex:401-407`), each gated by a registry-keyed predicate (`bool_ctor?` :500, `nat_ctor?` :505, `sigma_ctor?` :513). Add the List analog:
- **Predicate:** `list_ctor?(env, name)` mirroring `sigma_ctor?/2` (`Inductive.builtin(env, :list) == Inductive.ctor_family(env, name)`).
- **Value lowering** (new arm in the `emit.ex:162` cond, placed with the other builtin arms): `Nil` → `{nil, @line}` (the empty-list BEAM literal); `Cons(h, t)` → `{:cons, @line, lower(h), lower(t)}` (a real BEAM cons cell). Directly parallels `sigma_ctor?` → bare tuple.
- **Branch lowering:** add `list_branch_clause` to the `branch_clause/3` dispatch (`emit.ex:401`) matching `{nil, @line}` (Nil arm) and `{:cons, @line, Hpat, Tpat}` (Cons arm), parallel to `sigma_branch_clause` (`emit.ex:413-421`).

Result: `[1, 2, 3]` compiles to the BEAM term `[1, 2, 3]` (real cons cells), and `match xs [] -> … [h|t] -> …` compiles to a BEAM `case` on `[]`/`[H|T]` — interoperable with Erlang/AtomVM list NIFs, not an opaque tagged tuple.

**emit.ex:60 filter is irrelevant** (scout item 8): it drops body-less `builtin_op` defs (K2 arithmetic globals); List ctors are constructor applications inside function bodies, never `builtin_op` entries in `env.defs`.

## 2. Scope cut (decided — one-deep patterns this wave)

`constructor_pattern/1` (`elaborator.ex:3777-3805`) requires every positional sub-pattern of a ctor pattern to be a **bare `{:variable, …}`**; a nested constructor sub-pattern returns `{:error, {:unsupported_pattern, :nested_constructor_arg}}` (`elaborator.ex:3803`). The general nested decision-tree lift does not exist.

- **In scope (works this wave):** `[]` and `[h | t]` patterns — after desugaring these are `Nil` and `Cons(h, t)` with **bare-variable** sub-patterns, satisfying the rule. All **expression-position** list literals of any shape (`[1,2,3]`, `[a,b|rest]`) — nesting in expression position is just nested `Cons` *calls*, fully supported.
- **Out of scope (later increment, ledgered):** genuinely **nested list-literal patterns** — `match xs [1, 2, 3] -> …`, `[a, b] -> …`, `[a, b | rest] -> …` — because after desugaring these are `Cons(1, Cons(2, …))` / `Cons(a, Cons(b, rest))`, i.e. nested ctor patterns that hit the `nested_constructor_arg` gap. This gap is shared with `Nat`'s `S(S(m))` and is a general elaborator lift, not List-specific; it gets its own increment.
- **`Std.List` dependent-cleanness is bounded by this cut.** The executor MUST audit `lib/std/list.cure`'s actual patterns: functions using only `[]` / `[h | t]` (one-deep, bare-var) will dependent-elaborate; any function using a deeper list pattern will NOT this wave. The ratchet (§4) records how many `Std.List` functions/modules flip, not an assumption that all of `Std.List` becomes clean. Do NOT rewrite `std/list.cure`'s deeper patterns to dodge the gap — leave them and ledger; the nested lift is the honest fix.

## 3. Antibodies / tests

New test file `test/cure/elab/list_test.exs`, harness mirroring `conditional_test.exs`/`pickup_test.exs` (`Program.elaborate` → `Emit.compile_and_load` → `apply`, compare to the BEAM value). Directed tests (behavioral, not implementation-coupled):

1. **Native representation:** a function returning `[1, 2, 3]` (dependent pipeline) evaluates to the BEAM list `[1, 2, 3]` — assert `apply(...) == [1, 2, 3]`, proving native cons (not a tagged tuple). Include an `is_list/1` assertion to nail nativeness.
2. **Empty list:** `[]` evaluates to `[]` (`== []`).
3. **Cons sugar:** `[h | t]` with `h`/`t` params builds the expected BEAM list.
4. **One-deep pattern match:** a `match xs [] -> … [h | t] -> …` function (e.g. a `head`-or-default, or `is_empty`) selects the right arm at runtime for `[]` and a non-empty list.
5. **Element typing:** a list whose elements' types disagree in a checked position is rejected (e.g. `[1, true]` against `List(Int)`), surfacing the ctor/kernel type error — assert error, any shape (not a specific classic E-code).
6. **`Std.List` smoke:** at least one real `Std.List` function that uses only one-deep patterns elaborates + runs through the dependent pipeline (pick one the audit confirms is one-deep, e.g. `cons`/`is_empty`/`head`-like).
7. **Nested-pattern is rejected cleanly (ledger guard):** a `match xs [a, b] -> …` (or `[1] ->`) currently returns an error (the `nested_constructor_arg` gap), NOT a crash — assert `{:error, _}`. This pins the scope boundary so a future nested-lift increment flips it deliberately.

Red-first: each test written and shown failing before the change (list literals fail with `{:error, {:unsupported_expression, {:list, …}}}` pre-change).

## 4. Ratchet + firewall gate

- **Firewall:** `test/cure/dependent_pipeline_firewall_test.exs` MUST stay green — no `lib/cure/elab/*` or `lib/cure/core/*` reference to any classic module. (List touches elab/emit + a schema line in `core/builtins.ex` + a `.cure` source; none reference classic.)
- **Core untouched:** `git diff` must show `lib/cure/core/` limited to the single `@schemas` line in `builtins.ex` (the kernel proper — `eval/normalise/conv/quote/kernel/term/erase` — EMPTY). State this explicitly at the gate.
- **Ratchet:** re-run the stdlib disposition script (roadmap §0). Wave 2 is expected to flip `Std.List` (fully or partially) and any module whose only remaining blocker was List toward KEEP. **State before/after counts.** A regression in the existing KEEP set (bool/bounded/decision/equivalent/nat/proof/sigma/vector) = STOP. Report which modules moved and which remain blocked (and on what — e.g. lambda/String/extern).
- **Oracle replay:** `mix test test/oracle_replay_test.exs` — 65/65, no verdict flipped (List is additive; no existing dependent program should change verdict).

## 5. Gate

1. Red-first: every directed test shown failing before the change.
2. Scoped `mix test test/cure/elab/list_test.exs test/cure/elab/` green; then the full suite ONCE (build lock held; #22/Wave-1 already landed), 0 failures, total = baseline + new tests.
3. Firewall green; `core/` diff = schema line only; disposition not regressed and reported; oracle replay 65/65.
4. Commit(s), ghost author, explicit pathspecs. Suggested split: (C1) seed + schema + `std/list.cure` declaration + registration reconciliation; (C2) elaborator `:list` desugaring; (C3) emit native cons + branch. Or a single coherent commit if the executor prefers — each commit must be independently suite-green (per the #22 Part-A precedent).

## 6. Out of scope

- Genuinely nested list-literal **patterns** (`[1,2,3] ->`, `[a,b] ->`, `[a,b|rest] ->`) — needs the general `nested_constructor_arg` decision-tree lift (`elaborator.ex:3803`), shared with `Nat`'s `S(S(m))`; its own increment.
- List **comprehensions** (`[x | x <- xs, p(x)]`) if the parser produces them (`parse_list_or_comprehension` suggests a comprehension branch) — not part of the value-surface literal/cons work; separate feature.
- Adding `Std.List` to `@auto_prelude` (decided §1.1: seed only).
- Everything else in the program (lambda-inference, String, @extern, Map/tuples/tail) — later waves.
- Any change to the kernel proper (`core/{eval,normalise,conv,quote,kernel,term,erase}.ex`), to `pickup`/`conditional`/`match`/`bool_case` internals, or to `declarations.ex`'s dispatch whitelist (the third-dispatch-layer gotcha from Wave 1 — a bare top-level list body elaborates infer-only, acceptable here exactly as for pickup; ledger, do not extend without a red test that needs it).
