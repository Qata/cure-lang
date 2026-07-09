# Value-Surface Wave 3 — `@extern` / FFI in the dependent pipeline

**Goal:** Let a bodyless `@extern(:mod, :fn, arity)` function declaration elaborate through the DEPENDENT pipeline (as a typed opaque postulate) and emit to a direct Erlang remote call — the FFI path to AtomVM's NIFs and OTP. No kernel/TCB change.

**Status of the program:** Waves 1 (`pickup`) and 2 (`List`) landed on `autopilot/kernel-parity-batch` (unmerged). `@extern` is promoted ahead of lambda-inference on scout evidence (§0).

---

## 0. Why `@extern` is next (reorder rationale — decided from scout evidence)

The value-surface roadmap's original wave order put lambda-inference before `@extern`. A scout of both gaps (this session, dependent-pipeline-verified) reversed that for one decisive reason:

- **`@extern` is the *earlier* blocker in every one of the ~9 std modules that fail.** A bodyless `@extern` decl (e.g. `Std.List`'s `@extern(:erlang, :length, 1) fn length/1`) is at or near the top of each module and halts the whole-module body pass (`program.ex:760-766`, `Enum.reduce_while`/`{:halt, err}`) *before* any lambda body is ever reached. So **lambda-inference alone flips zero modules** — even `Std.List` needs `@extern` first. `@extern` alone plausibly flips ~2–4 modules (math, map firmly; pair, gen plausibly), and reduces the rest to two cheap literal-support follow-ons (atom-literals → system + test; string-literals + `<>` → io + string), leaving lambda-inference as the last mile for just `list`.
- **`@extern` is TCB-free and lambda-independent** (§4, §5). It is confined to the elaborator (accept the bodyless decl) + emit (remote-call wrapper); disjoint from the motive/inference machinery lambda-inference touches.

Revised remaining wave order: **`@extern` → atom-literals → string-literals+`<>` (the "String" wave) → lambda-inference (`list`) → Map/tuples/tail.** Atom-literals is flagged (§5) as the single highest-leverage follow-on (a ~1-clause addition to the literal handler that flips 2 modules) and should be the wave immediately after this one.

## 1. The gap (dependent-pipeline-verified)

The dependent pipeline has **zero** `@extern` handling today (`grep extern lib/cure/elab/` → nothing; the only `core/` hits are `to_external`/`from_external` false positives in `term.ex`). So this is net-new elaborator + emit code, not a tweak.

### 1.1 Surface shape

- `@extern(:mod, :fn, arity)` is a **decorator on a function decl**; the parser folds it into the function's `meta` as `[extern: {mod, fun, arity}]` (`lib/cure/compiler/parser.ex:4757-4774`, literal extraction `:4781-4798`). The node stays `{:function_def, meta, body}`.
- A bodyless `fn length(list: List(T)) -> Int` (no `=`) produces `body = []` — the "signature only" arm (`parser.ex:2398-2402`; the multi-clause arm `:2385-2395` also yields `[]` and additionally sets `meta[:clauses]`).

### 1.2 Exact failure site

`Declarations.elaborate/2` runs `register_signature` then `elaborate_function_body` (`lib/cure/elab/declarations.ex:26-29`):

- `register_signature` **succeeds** for an extern: it builds the Π from the signature and stores a placeholder def body `{:hole, "__pending__"}` (`declarations.ex:36-40`, via `function_signature/2` `:76-101`). **The type is fully derivable from the signature alone — no body needed.**
- `elaborate_function_body` calls `single_body([])` → fallthrough `single_body(expr), do: expr` (`declarations.ex:264-265`) → returns `[]` → `elaborate_body([], …)` → catch-all (`declarations.ex:383-387`) → `Elaborator.elaborate_expr_typed([], …)` → the catch-all `elaborate_expr_typed(other, …), do: {:error, {:unsupported_expression, other}}` at **`elaborator.ex:554`** with `other = []`.

Result: `{:unsupported_expression, []}`, halting the module at its first extern decl. (Line 554 is authoritative-current; this file drifts a few lines — the executor MUST re-verify the catch-all clause by identity, not line number.)

## 2. Design (decided)

`@extern` is a **typed opaque postulate with a runtime remote-call realization**: the declared Π is the trusted type (FFI signatures are always asserted, never proven), the kernel never unfolds it (bodyless globals are already opaque neutrals — §4), and emit gives it runtime meaning as a direct Erlang remote call. This is sound by construction — there is no term to check, normalize, convert, or erase.

Two changes, both below the typing judgement's trust boundary in the sense that the kernel is untouched:

### 2.1 Elaborator: accept the bodyless extern (E-layer)

In `elaborate_function_body` (`declarations.ex:45-71`): when `meta[:extern]` is present, **skip body elaboration entirely** — do NOT call `elaborate_body`, `Kernel.check`, or `Relevance.check` (there is no term). Keep the Π already computed by `function_signature/2`, and **replace the `{:hole, "__pending__"}` placeholder with an extern MARKER** carrying `{mod, fun, arity}`.

**Marker representation (contract, exact form is a plan decision):** the def must be marked such that (1) body-elaboration / `Kernel.check` / `Relevance.check` are skipped, (2) `emit`'s `reject_holes` (`emit.ex:104-116`) does NOT see a hole (a pending `{:hole, …}` would be rejected — so the marker must NOT be a hole), and (3) emit can route it to the remote-call wrapper. A dedicated `def` field (`extern: {mod, fun, arity}`) or a `body: {:extern, {mod, fun, arity}}` sentinel both satisfy the contract; the plan picks one and pins it with the "typechecks AND ships" test (§3 antibody 2).

### 2.2 Emit: lower to the remote call (C-layer, mirrors classic — does NOT call it)

Emit must recognize the extern marker and produce the wrapper form, MIRRORING (not calling) the classic oracle `codegen.ex:691-705`:

```elixir
remote_call =
  {:call, line, {:remote, line, {:atom, line, ext_mod}, {:atom, line, ext_fun}}, param_forms}
clause = {:clause, line, param_forms, [], [remote_call]}
{:function, line, fn_atom, arity, [clause]}
```

i.e. a wrapper `fn_atom/arity` whose single clause binds params `V0…Vn-1` (present-arity param naming already exists, `emit.ex:141-150, 361-366`) and issues `mod:fun(V0, …, Vn-1)`.

The **"emit.ex:60 filter widen"**: line 60 is `names = for {name, d} <- defs, is_nil(Map.get(d, :builtin_op)), do: name` (`emit.ex:55-63`) — it already skips body-less `:builtin_op` defs because `function_form` would crash on their nil Core body. Widen twofold: (1) the all-defs path must ALSO skip / specially-route extern-marked defs (same nil-body shape); (2) the live `/3` path (explicit `local_defs`, `emit.ex:71-80`) must route extern-marked names to the remote-call emitter instead of the generic `function_form` (`emit.ex:125-139`, which reads `%{body: body}` + `Erase.erase` and would misbehave on a bodyless extern). No classic module is called — the form is duplicated, so the firewall stays green.

### 2.3 What must NOT change

- The kernel proper — `lib/cure/core/{eval,normalise,conv,quote,kernel,term,erase,inductive}.ex` — stays EMPTY of changes (§4). `builtins.ex` need not change either this wave.
- No new Core term type. The extern marker lives in the E-layer def/emit only; the kernel sees only the already-opaque global.
- `declarations.ex`'s dispatch whitelist for real bodies is untouched (extern is handled by an EARLIER `meta[:extern]` branch in `elaborate_function_body`, before the body dispatch, not by adding a node to the whitelist).

## 3. Antibodies / tests

New test file `test/cure/elab/extern_test.exs` (harness like `list_test.exs`: `Program.elaborate` → `Emit.compile_and_load` → `apply`, compare to the BEAM value). Behavioral, not implementation-coupled:

1. **Elaboration accepts a bodyless extern.** `@extern(:erlang, :length, 1) fn length(xs: List(Int)) -> Int` (inside a `mod`) elaborates `{:ok, _}` (RED today: `{:unsupported_expression, []}`). Assert the registered global has the declared Π type (arrow `List(Int) -> Int`) — proving the signature is retained, not discarded.
2. **It typechecks AND ships (the marker contract).** The SAME extern compiles+loads via `Emit.compile_and_load` and, applied, issues the remote call: `apply(mod, :length, [[1, 2, 3]]) == 3` (real `:erlang.length/1`). This is the antibody that catches a marker which typechecks but is rejected/mis-emitted by `reject_holes`/`function_form` (§2.1 caveat).
3. **A 0-arity and a 2-arity extern both work** (arity generality): e.g. `@extern(:erlang, :system_time, 0) fn now() -> Int` elaborates and (loosely) runs; `@extern(:erlang, :max, 2) fn imax(a: Int, b: Int) -> Int` with `imax(3, 7) == 7`. Pins param-var wiring at 0 and >1.
4. **A module that mixes an extern with a normal dependent function elaborates end-to-end** — an `@extern` decl followed by a plain `fn` that the pipeline already supports (e.g. an `if`/arith body); proving the extern no longer halts the body pass and the rest of the module still elaborates + emits. (Directly models the real `Std.Math`/`Std.Map` unblock.)
5. **Firewall stays green** — the extern emit MIRRORS the classic form; `test/cure/dependent_pipeline_firewall_test.exs` must show no `lib/cure/elab/*` reference to any classic module.
6. **Oracle equivalence (READ-ONLY).** The classic behavioral pin is `codegen.ex`'s `compile_extern_function` and any existing extern codegen test — confirm those stay green (classic untouched); the dependent runtime result (a direct `mod:fun(...)` call) must match the classic-lowered form for the same decl.

Red-first: each test shown failing before the change (antibody 1 fails `{:unsupported_expression, []}`).

## 4. TCB / kernel: untouched (justification)

The kernel already treats every `:global` head as an opaque neutral `{:nglobal, name}` unless it is totality-certified; δ-unfolding is gated on certification (`eval.ex:11-12, 41-48`; `conv.ex:10-18, 117`; uncertified globals compared by-name only, `conv.ex:153`). A bodyless `@extern` def has **no Core body to certify**, so it stays opaque — indistinguishable to the kernel from any uncertified postulate. It is never evaluated, normalized, converted-by-unfolding, quoted, or erased-as-a-term. Therefore **no change to `eval/normalise/conv/quote/kernel/term/erase/inductive`.** The `git diff` gate (§5) enforces this: `core/` must be EMPTY of changes this wave (unlike Wave 2, `builtins.ex` is not touched either).

## 5. Ratchet + firewall gate

- **Firewall:** `test/cure/dependent_pipeline_firewall_test.exs` MUST stay green (extern emit duplicates the classic form, references no classic module).
- **Core untouched:** `git diff` shows NO change under `lib/cure/core/` at all. Diff limited to `lib/cure/elab/declarations.ex`, `lib/cure/elab/emit.ex` (and `elaborator.ex` only if the marker plumbing needs it), plus the new test file. (`lib/std/*.cure` is NOT edited — the std modules already carry their `@extern` decls; this wave makes them elaborate.)
- **Ratchet:** re-run the stdlib disposition script (roadmap §0). Record KEEP before/after. **Expected to flip `Std.Math` and `Std.Map`** (scout: their only blocker after extern is nothing / opaque-type resolution), plausibly `Std.Pair`/`Std.Gen`. `Std.System`/`Std.Test` will NOT flip (next blocker: atom literals — next wave); `Std.Io`/`Std.String` will NOT flip (string literals + `<>`); `Std.List` will NOT flip (lambda-inference). **State the actual before/after KEEP set and, for each of the 9 extern modules, whether it flipped and if not the NEXT blocker named concretely** (this per-module map is the deliverable that sequences the following waves). A regression in the existing KEEP set (bool/bounded/decision/equivalent/nat/proof/sigma/vector) = STOP. The scout's per-module estimates are *static* (compiler not executed) — the executor's run is authoritative; report honestly where a predicted flip did not happen and why.
- **Oracle replay:** `mix test test/oracle_replay_test.exs` — report the live `N/N`; no verdict may flip (extern is additive).

## 6. Gate

1. Red-first: every directed test shown failing before the change.
2. Scoped `mix test test/cure/elab/extern_test.exs` green; then the full suite ONCE (build lock free; #22/Wave-1/Wave-2 landed), 0 failures, total = live baseline + new tests. Capture the LIVE baseline on this branch before the change — do NOT hardcode a remembered count.
3. Firewall green; `core/` diff EMPTY; disposition reported (per-module map); oracle replay live `N/N`.
4. Commit(s), ghost author (`--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no trailers/signature), explicit pathspecs. Suggested split: (C1) elaborator accept bodyless extern + marker; (C2) emit remote-call wrapper + filter widen. Or one coherent commit. Each commit independently pre-existing-suite-green (the tests go green only once BOTH land — under a split, commit the new test file with C2; keep the red demonstration as an uncommitted local run, per the Wave-2 precedent).

## 7. Out of scope (do NOT build here)

- **Atom literals** (the next wave — flips system + test; ~1-clause add to the literal handler at `elaborator.ex:446`).
- **String literals + `<>`** (the "String" wave — flips io + string).
- **Lambda-inference / `:bad_motive`** curried-lambda folds (`list.cure` sum/product/count — flips list).
- `@extern` with a **non-trivial body** or clause guards, effect typing of FFI, or any dependently-typed refinement of the FFI signature (the Π is taken as an asserted postulate — that is the whole design).
- Any change to the kernel proper, or to `pickup`/`conditional`/`match`/`list`/`sigma`/`nat` emit internals.
- Adding externs to `@auto_prelude`.
