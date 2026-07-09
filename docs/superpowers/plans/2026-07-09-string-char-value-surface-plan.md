# String & Char Value-Surface (option b: bespoke Char primitive) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (autopilot Stage 4, inline, Opus). Steps use checkbox (`- [ ]`) syntax.

**Goal:** Make `Char` and `String` ordinary dependent-pipeline values — `Char` a bespoke kernel primitive erasing to a native integer, `String = List(Char)` a charlist — so `Std.String` (or a demo module) elaborates through the dependent pipeline.

**Architecture:** `Char` mirrors the existing `Int` base-type machinery across the kernel (`core/*`), then elaboration + emit + a `String↔Binary` `@extern` bridge sit on top. The bound `0 ≤ cp ≤ 0x10FFFF` is an elaborator integer check (NOT a `Nat` index — see spec §2.1: `Bounded` was measured out, ~370 MB bound tower). Design authority: `docs/superpowers/specs/2026-07-09-string-char-value-surface-design.md` (hardened at `b61b89c`, reconciled at `513d4e3`) — read it; this plan sequences it.

**Tech Stack:** Elixir, Cure dependent kernel (`lib/cure/core/*`) + elaborator (`lib/cure/elab/*`), Antigen (`test/antigen/*`), cure-porting differential oracle (`mix cure.oracle`).

## Global Constraints

- **Dependent pipeline ONLY.** `lib/cure/elab/*` + `lib/cure/core/*` + `lib/cure/elab/emit.ex`. IGNORE `lib/cure/compiler/*` (`codegen.ex`, `pattern_compiler.ex`) and `lib/cure/types/*` (`checker.ex`) — same-named functions there are decoys. (The lexer/parser at `lib/cure/compiler/{lexer,parser}.ex` ARE the shared AST source — that's fine.)
- **TCB discipline.** Task 1 touches the kernel. It is HARD-STOP-reviewed but Agda/Idris-aligned (both have primitive `Char`). It requires a new Antigen antibody + the full Antigen suite + full `mix test`, run **once, alone** — never concurrent with another `mix` run (a past concurrent full-suite run caused a kernel panic).
- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO `Co-Authored-By`, no Claude signature. **Explicit-pathspec staging only** (`git add -- <path>` / `git commit -- <path>`; NEVER `git add -A`/`git add .` — a concurrent agent (option a) may share the tree).
- **Branch:** stay on `autopilot/kernel-parity-batch` (operator preference — no new worktree).
- **Strict red-green TDD:** write the failing test, run it, watch it fail for the right reason, implement minimally, run it green, commit.
- **Coordination:** option (a) (compact Nat literals, another agent) also edits `conv.ex`/`kernel.ex`; keep Task 1's edits localized and clearly `char_*`-named to minimize the later merge.

---

### Task 1: `Char` kernel primitive (`{:char_type}`/`{:char_lit, cp}`)

**Files:**
- Modify: `lib/cure/core/term.ex` (5 fns: `term?/1`, `shift`, `subst`, `to_external/1`, `from_external/1` — int pairs at 61-62/86-87/149-150/215-216/249-250)
- Modify: `lib/cure/core/eval.ex:43-44` (`{:int_type}`→`{:vint_type}`, `{:int_lit,n}`→`{:vint,n}`)
- Modify: `lib/cure/core/value.ex:45-46` (`value?({:vint_type})`, `value?({:vint,n})`)
- Modify: `lib/cure/core/conv.ex` (type-id at 74/164, literal-eq at 75/165)
- Modify: `lib/cure/core/quote.ex:64` (`{:vint_type}`→`{:int_type}` reify; add `{:vchar,n}`→`{:char_lit,n}`)
- Modify: `lib/cure/core/kernel.ex:59` (and the `{:vint_type}` handling near 635)
- Test: `test/cure/core/char_prim_test.exs` (new), modeled on `test/cure/core/int_prim_test.exs`

**Interfaces:**
- Produces: Core terms `{:char_type}`, `{:char_lit, cp}` (cp a non-neg integer); values `{:vchar_type}`, `{:vchar, cp}`. `Kernel.infer(ctx, {:char_lit, cp})` → `{:ok, {:vchar_type}}`; `Kernel.infer(ctx, {:char_type})` → `{:ok, {:vtype, 0}}`. `Conv.conv?({:vchar,a},{:vchar,b},...)` ⇔ `a==b`.

- [ ] **Step 1: Write the failing test** — `test/cure/core/char_prim_test.exs`, mirroring `int_prim_test.exs`:

```elixir
defmodule Cure.Core.CharPrimTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Env, Kernel, Conv, Eval, Builtins}

  defp sig, do: Builtins.seed(Env.empty())
  defp ctx, do: Context.empty(sig())

  test "char_type is a type" do
    assert {:ok, {:vtype, 0}} = Kernel.infer(ctx(), {:char_type})
  end

  test "char_lit infers to char_type" do
    assert {:ok, {:vchar_type}} = Kernel.infer(ctx(), {:char_lit, 97})
  end

  test "char_lit evaluates to a vchar value" do
    assert {:vchar, 97} = Eval.eval({:char_lit, 97}, [])
  end

  test "equal char_lits are convertible, unequal are not" do
    a = Eval.eval({:char_lit, 97}, [])
    b = Eval.eval({:char_lit, 97}, [])
    c = Eval.eval({:char_lit, 98}, [])
    assert Conv.conv?(a, a, [], 0, sig())
    assert Conv.conv?(a, b, [], 0, sig())
    refute Conv.conv?(a, c, [], 0, sig())
  end
end
```

- [ ] **Step 2: Run it, watch it fail** — `mix test test/cure/core/char_prim_test.exs` → FAIL (no `{:char_type}` handling; likely `FunctionClauseError`/`infer` catch-all error).

- [ ] **Step 3: Implement** — add the `char_*` clause beside each `int_*` clause named in **Files** (spec §4.1 gives the exact per-file mirror). Each is one clause mirroring its `int` twin: `term?` true for both; `shift`/`subst` identity; `eval({:char_type},_)→{:vchar_type}`, `eval({:char_lit,cp},_)→{:vchar,cp}`; `value?({:vchar_type})→true`, `value?({:vchar,n})→is_integer(n)`; `conv_struct?`/`same_value_no_delta?` type-id (74/164) + literal-eq (75/165); `quote` reify both; `kernel.infer` both. Do NOT add a `normalise.ex` or `erase.ex` clause (generic catch-alls cover them — spec §4.1).

- [ ] **Step 4: Run it green** — `mix test test/cure/core/char_prim_test.exs` → PASS.

- [ ] **Step 5: Antigen antibody** — add `test/antigen/char_lit_conv_antibody_test.exs`, modeled on `test/antigen/eq_inductive_antibody_test.exs` (the closest existing iff-property antibody): pin "`{:char_lit,a}` and `{:char_lit,b}` are convertible via the independent oracle `Cure.Core.Conv.conv_within?` iff `a == b`", over a StreamData sample of codepoints. Run `mix test test/antigen/char_lit_conv_antibody_test.exs` → PASS.

- [ ] **Step 6: Full gate (once, alone)** — `mix test` (includes Antigen). Must be green with no regression. Do not run any other `mix` concurrently.

- [ ] **Step 7: Commit** — `git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -- lib/cure/core/term.ex lib/cure/core/eval.ex lib/cure/core/value.ex lib/cure/core/conv.ex lib/cure/core/quote.ex lib/cure/core/kernel.ex test/cure/core/char_prim_test.exs test/antigen/char_lit_conv_antibody_test.exs -m "feat(kernel): Char primitive ({:char_type}/{:char_lit}), mirror Int"`

---

### Task 2: Char literal *expression* elaboration + `Char` type name

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` — `elaborate_expr_typed/4` `:literal` clause (`:integer` arm at 452-453) AND `elaborate_expr/3` infer-mode copy (`:integer` arm at 4910)
- Modify: `lib/cure/elab/declarations.ex:1126-1128` (`primitive_type` resolver)
- Test: `test/cure/elab/char_literal_test.exs` (new)

**Interfaces:**
- Consumes: `{:char_type}`/`{:vchar_type}` from Task 1.
- Produces: `'a'` (a `:char` literal AST, value 97) elaborates to `{:char_lit, 97}` : `{:vchar_type}`. `Char` in a signature resolves to `{:char_type}`. Bound: reject `cp > 0x10FFFF` at elaboration.

- [ ] **Step 1: Write the failing test** — `test/cure/elab/char_literal_test.exs`: assert a program `fn f(c: Char) -> Char = c` + `fn g() -> Char = 'a'` elaborates (`{:ok, _}` from `Cure.Elab.Program.elaborate/1`), and that a probe exposing the core (via the existing test helper used by `list_test.exs`) yields `{:char_lit, 97}`. Add a negative: a char literal with `cp > 0x10FFFF` is rejected with a clear error (construct via the AST directly if the lexer can't emit an out-of-range one).

- [ ] **Step 2: Run it, watch it fail** — `mix test test/cure/elab/char_literal_test.exs` → FAIL (`:char` hits the `{:error, {:unsupported_expression, _}}` fallthrough; `Char` fails to resolve).

- [ ] **Step 3: Implement** —
  - `elaborate_expr_typed/4`: add `:char when is_integer(value) and value <= 0x10FFFF -> {:ok, {:char_lit, value}, {:vchar_type}}` (mirror `:integer` at 452-453, 3-tuple), plus a guard-failing clause returning a clear out-of-range error.
  - `elaborate_expr/3` (4910): add `:char when is_integer(value) and value <= 0x10FFFF -> {:ok, {:char_lit, value}}` (2-tuple — NOT the 3-tuple; spec §4.2 warns against pasting one into both sites).
  - `declarations.ex`: add `primitive_type("Char"), do: {:char_type}` before the catch-all `nil` at 1128.

- [ ] **Step 4: Run it green** — `mix test test/cure/elab/char_literal_test.exs` → PASS.

- [ ] **Step 5: Commit** — explicit pathspec, ghost author, `-m "feat(elab): Char literal expression elaboration + Char type name"`.

---

### Task 3: Char literal *patterns* (`case c of 'a' -> …`)

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` — `primitive_scrut_kind/2` (2723-2730), `literal_of?/2` (2752-2755), `lit_core/2` (2760-2762), `literal_chain/6` (2784-2798)
- May need: a `char_eq` equality global (mirror `int_eq`) — check `lib/cure/core/builtins.ex` `seed_ops`/`@int_binops` for where `int_eq` is seeded; add `char_eq` the same way if not derivable.
- Test: `test/cure/elab/char_pattern_test.exs` (new)

**Interfaces:**
- Consumes: `{:vchar_type}` (Task 1), char-literal elaboration (Task 2).
- Produces: `case c of 'a' -> X | _ -> Y` elaborates and both branches are reachable/correct.

- [ ] **Step 1: Write the failing test** — a program matching a `Char` scrutinee against a char-literal arm plus a wildcard; assert `{:ok, _}` and (via emit/run or a core probe) that the match dispatches correctly on both the equal and non-equal input.

- [ ] **Step 2: Run it, watch it fail** — `mix test test/cure/elab/char_pattern_test.exs` → FAIL (`primitive_scrut_kind` catch-all → `try_literal_match` returns `:not_applicable` → falls into `:vdata` ctor-pattern path with no clause → error).

- [ ] **Step 3: Implement** — add the `Char`/`{:vchar_type}` case to all four functions, mirroring the `Int` cases exactly: `primitive_scrut_kind` → `:char`; `literal_of?({:literal,_,v}, :char)` → `is_integer(v)`; `lit_core(v, :char)` → `{:char_lit, v}`; `literal_chain` → pick the `char_eq` global. Seed `char_eq` in `builtins.ex` if needed (mirror `int_eq`).

- [ ] **Step 4: Run it green** — `mix test test/cure/elab/char_pattern_test.exs` → PASS. Then `mix test test/cure/elab/ test/cure/core/` (scoped, not full) → no regression.

- [ ] **Step 5: Commit** — ghost author, explicit pathspec, `-m "feat(elab): Char literal patterns via try_literal_match"`.

---

### Task 4: Char emit (`{:char_lit}` → BEAM integer)

**Files:**
- Modify: `lib/cure/elab/emit.ex:210` (mirror the `{:int_lit, n}` → `{:integer, @line, n}` clause)
- Test: `test/cure/elab/char_emit_test.exs` (new)

- [ ] **Step 1: Write the failing test** — assert emitting `fn g() -> Char = 'a'` yields Erlang abstract form containing `{:integer, _, 97}` (mirror how `int_lit` emit is tested), or run it through the dependent pipeline and assert the runtime value is `97`.
- [ ] **Step 2: Run it, watch it fail** — `mix test test/cure/elab/char_emit_test.exs` → FAIL (no lower clause for `{:char_lit,_}`).
- [ ] **Step 3: Implement** — add `defp lower(_env, {:char_lit, cp}, _ctx), do: {:integer, @line, cp}` beside the `int_lit` clause at emit.ex:210.
- [ ] **Step 4: Run it green** — PASS.
- [ ] **Step 5: Commit** — `-m "feat(emit): Char lowers to a BEAM integer"`.

---

### Task 5: `type Binary = |` + `type String = List(Char)`

**Files:**
- Modify: `lib/std/string.cure` (add both `type` declarations at the top; see spec §4.3/§4.6 — aliases use the existing `type X = Y` surface form, `declarations.ex:235-242`; `Binary` mirrors `Std.Decision.Empty`'s `type Empty = |`)
- Test: `test/cure/elab/string_char_types_test.exs` (new)

**Interfaces:**
- Consumes: `Char` type (Task 2), `List` (existing builtin).
- Produces: `String` resolves to `List(Char)`; `Binary` is a usable zero-ctor `@extern` param/return type.

- [ ] **Step 1: Write the failing test** — a module declaring `type Binary = |`, `type String = List(Char)`, and an `@extern` sig `fn to_binary(s: String) -> Binary`; assert `Cure.Elab.Program.elaborate/1` returns `{:ok, _}` and `String` in a sig elaborates identically to `List(Char)`.
- [ ] **Step 2: Run it, watch it fail** — FAIL (Binary unresolved / String alias absent). *Routing caveat (spec §4.6):* put these in a module that already has a dependent trigger (an auto-generalized helper) so `dependent?/1` routes it through the dependent pipeline — `Std.String` qualifies; a bare new module of only these decls does not.
- [ ] **Step 3: Implement** — add `type Binary = |` and `type String = List(Char)` to `lib/std/string.cure`.
- [ ] **Step 4: Run it green** — PASS.
- [ ] **Step 5: Commit** — `-m "feat(std): Binary (zero-ctor) + String = List(Char) alias"`.

---

### Task 6: String literal & interpolation → charlist

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` — desugar the string-literal node into a `:list` AST of `:char` nodes routed through `desugar_list/1` (3806-3818); interpolation (`{:string_interpolation,_,parts}`) desugars to `++` of parts, interpolated parts restricted to `String`-typed exprs this wave (spec §4.4)
- Test: `test/cure/elab/string_literal_test.exs` (new)

- [ ] **Step 1: Write the failing test** — assert `"abc"` elaborates to the `List(Char)` cons spine `Cons({:char_lit,97}, Cons(98, Cons(99, Nil)))` and **emits** `[97,98,99]` (assert emitted abstract form or a dependent-pipeline run). Add: a no-interpolation string and a `"x" <> s`-style interpolation with `s: String`. Do NOT test literal-valued multi-element String patterns (spec §4.2 — pre-existing matrix-compiler miscompile, out of scope).
- [ ] **Step 2: Run it, watch it fail** — FAIL (string literal unhandled in the dependent pipeline).
- [ ] **Step 3: Implement** — desugar string literal → `:list` of `:char` nodes → existing generic `desugar_list/1`; interpolation → `++` concatenation.
- [ ] **Step 4: Run it green** — PASS.
- [ ] **Step 5: Commit** — `-m "feat(elab): string literals & interpolation to List(Char) charlist"`.

---

### Task 7: `to_binary`/`from_binary` bridge + round-trip

**Files:**
- Modify: `lib/std/string.cure` — `@extern(:unicode, :characters_to_binary, 1) fn to_binary(s: String) -> Binary` and `@extern(:unicode, :characters_to_list, 1) fn from_binary(b: Binary) -> String`
- Test: `test/cure/elab/string_bridge_test.exs` (new, elaboration) + a generic-unix AtomVM round-trip (see §8 locus)

- [ ] **Step 1: Write the failing test** — assert both `@extern` sigs elaborate (needs Task 5's `Binary`/`String`), and a demo `.cure` calling `from_binary(to_binary("abc"))` returns `"abc"`.
- [ ] **Step 2: Run it, watch it fail** — FAIL until sigs + bridge exist.
- [ ] **Step 3: Implement** — add the two `@extern` defs.
- [ ] **Step 4: Run it green (host)** — `mix test test/cure/elab/string_bridge_test.exs`. Then the cross-repo host check: build `cure` (`mix escript.build`) and run a demo module through `../../phase35/run-on-unix.sh` against generic-unix AtomVM (spec §8; the esp32-beam `CLAUDE.md` "validate on host before any claim"). Report this cross-repo result separately from the in-repo gate.
- [ ] **Step 5: Commit** — `-m "feat(std): String<->Binary bridge via unicode NIFs"`.

---

### Task 8: Ratchet — `Std.String` migration or demo module, + oracle probes

**Files:**
- Modify: `lib/std/string.cure` (structural ops → `List` ops; Unicode ops → bridge; spec §4.7) OR create `lib/std/string_demo.cure` (scope guard)
- Create: `test/oracle/char/char01_literal.{cure,idr}`, `test/oracle/char/str01_unpack.{cure,idr}` (new cluster; spec §8) + `verdicts.json`
- Test: oracle replay + KEEP-count check

- [ ] **Step 1: Oracle probes** — author paired `.cure`/`.idr`: (i) a `Char` literal + `Char`-typed sig → `same`; (ii) a `String` pattern-matched as a list → mark the Idris-`String`-is-primitive divergence honestly (`cure_stricter`/`idris_only` with the written Option-A reason, spec §2.4/§8). Run `mix cure.oracle char`; never hand-write a verdict.
- [ ] **Step 2: Ratchet** — migrate `Std.String` per §4.7, OR (scope guard) create a small demo module that `use`s the foundation and KEEPs. Obtain the before/after value-surface KEEP count by manually invoking `Cure.Elab.Program.elaborate/1` over the 39 std modules (no disposition script exists — spec §4.7). Count must move by ≥1, no prior-KEEP regression.
- [ ] **Step 3: Green gate** — `mix test test/oracle_replay_test.exs` green; then full `mix test` once, alone.
- [ ] **Step 4: Commit** — `-m "feat(std): String value-surface ratchet + char oracle cluster"`.

---

## Self-Review

- **Spec coverage:** Task 1↔§4.1, Task 2↔§4.2/§4.3, Task 3↔§4.2 patterns, Task 4↔§4.5, Task 5↔§4.3/§4.6, Task 6↔§4.4, Task 7↔§4.6, Task 8↔§4.7/§8. §5 data flow and §6 error handling are covered across Tasks 2/4/6/7. §7 non-goals (Atom, Show-rendering, graphemes, refined Char) are explicitly out of scope — no task, correct.
- **Sequencing:** Task 1 (TCB) first and gated alone; Task 5 (`Binary`) before Task 7 (bridge) and Task 8 (Unicode ops) per §9. Task 3 called out as the easy-to-forget separate path.
- **Type consistency:** `{:char_type}`/`{:char_lit, cp}` (terms) and `{:vchar_type}`/`{:vchar, cp}` (values) used uniformly; emit target `{:integer, @line, cp}`; bound guard `value <= 0x10FFFF` in both literal loci.
