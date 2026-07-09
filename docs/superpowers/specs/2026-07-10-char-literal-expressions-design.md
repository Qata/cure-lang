# Char literal expressions — design

**Status:** design approved (operator: "Yea add char literals"; `Char = Bounded(0x110000)` established in the 2026-07-10 milestone, commit 425f0bb).

**Scope:** the *expression* form of a character literal — `'a'`, `'😀'` — in the **dependent** pipeline (`lib/cure/elab/*` + `lib/cure/core/*`). Char literal *patterns* (`case c of 'a' ->`), string literals, `Binary`, and `Std.String` are **out of scope** (separate wave items, tasks #25–#30).

## 1. Goal

A source character literal elaborates to the compact `{:bounded_lit, cp}` Core node — the same value model as `Char = Bounded(0x110000)`. `'a'` is the codepoint `97`; `'😀'` is `128512`. One integer at every stage, never a `Next(…First)` tower. This is the last surface piece needed before `String = List(Char)` string literals can be built on top.

## 2. Background (already in place)

- The lexer already emits a character literal as `{:literal, [subtype: :char, line: L, col: C], cp}` where `cp` is the decoded Unicode codepoint integer (verified: `'a'` → value `97`).
- The compact Bounded value model landed (425f0bb): `{:bounded_lit, k}` : `Bounded(k+1)` minimal, `check(k, Bounded(n)) = ok` iff `0 ≤ k < n`, erases to the native integer `k`. `@builtin(:bounded)` registers the family from `Std.Bounded`.
- Integer literals already route to `{:bounded_lit, k}` in **check** mode against a `Bounded(n)` type (`elaborate_expr_checked`, the `int?`/`bounded_expected` branch).

Today a `:char` literal hits the catch-all and errors `{:unsupported_expression, {:literal, [subtype: :char, …], cp}}` in all three literal dispatchers.

## 3. Design

A character literal is **sugar for a bounded literal at the full Unicode bound.** `'a'` ≡ the value `97` typed at `Char = Bounded(0x110000)` (decimal `Bounded(1_114_112)`). The codepoint bound `0x110000` is intrinsic to char-ness — it does not come from context.

### 3.1 Type

`Char` is **not** a new kernel type. It is exactly `Bounded(0x110000)`. A user writes the name via `typealias Char = Bounded(1114112)` (the `typealias` keyword, already landed 6d5d8d6); the literal itself never needs that alias to exist — it produces the `Bounded(0x110000)` type value directly. Defining a canonical `Char` alias in the stdlib is a **separate** convenience item, out of scope here.

Because `Char` δ-reduces to `Bounded(0x110000)`, `'a' : Char` holds definitionally.

### 3.2 Where the change goes — infer only

The elaborator has three literal dispatchers:

1. `elaborate_expr_typed/4` (infer mode, returns `{:ok, term, type_value}`) — **the primary change.**
2. `elaborate_expr_checked/5` (check mode, returns `{:ok, term}`) — **no direct change needed.** Its fallback (`elaborate_expr_checked_fallback`) already does *infer-then-`Kernel.check`*: for a `:char` literal it will call `elaborate_expr_typed` (getting `{:bounded_lit, cp}`) and then `Kernel.check(ctx, {:bounded_lit, cp}, expected)`. The kernel re-derives the expected bound and admits iff `cp < bound`. So `'a'` checks against `Char` (= `Bounded(0x110000)`, `97 < 0x110000`), and — consistent with how integer literals behave — against any `Bounded(n)` with `n > cp`. This polymorphism over the bound is intentional and mirrors integer literals; char-ness is a *syntactic* signal, and the value is a genuine bounded literal.
3. `elaborate_expr/3` (scope-only, no `ctx`/`sig`, returns `{:ok, term}`) — used in type-index / scope-only positions. Emits the bare `{:bounded_lit, cp}` Core term with no type (the kernel re-checks later).

### 3.3 The infer clause (locus 1)

In `elaborate_expr_typed/4`'s `{:literal, meta, value}` `case` on `subtype`, add before the catch-all:

```
:char when is_integer(value) and value >= 0 and value <= 0x10FFFF ->
  case char_type_value(Context.signature(ctx)) do
    {:ok, ty} -> {:ok, {:bounded_lit, value}, ty}
    :no_bounded -> {:error, {:char_literal_needs_bounded, value}}
  end

:char when is_integer(value) ->
  {:error, {:char_literal_out_of_range, value}}
```

where the new private helper:

```
# The type of every character literal: Char = Bounded(0x110000). `:no_bounded`
# when the Bounded family is not registered (needs `use Std.Bounded`), so the
# error names the fix instead of crashing.
defp char_type_value(sig) do
  case Inductive.builtin(sig, :bounded) do
    nil -> :no_bounded
    fid -> {:ok, {:vdata, fid, [{:vnat, 0x110000}]}}
  end
end
```

`0x110000` = `1_114_112`; valid codepoints are `0 ≤ cp ≤ 0x10FFFF`, i.e. `cp < 0x110000`, so `{:bounded_lit, cp}` inhabits `Bounded(0x110000)`. The two-sided guard (`>= 0` and `<= 0x10FFFF`) matters because an AST-constructed literal (not from the lexer) could be out of range; the lexer itself never emits an out-of-range codepoint.

### 3.4 The scope-only clause (locus 3)

In `elaborate_expr/3`'s `subtype` `case`, add:

```
:char when is_integer(value) -> {:ok, {:bounded_lit, value}}
```

No bound guard here (no `sig` to build the type; this path only produces the term and the kernel re-checks). Kept for completeness so a char literal in a scope-only position does not spuriously error.

### 3.5 Soundness note

The elaborator assigns the infer-mode type `Bounded(0x110000)`, while the kernel's own `infer({:bounded_lit, cp})` returns the *minimal* `Bounded(cp+1)`. This is not a contradiction: the term is validated against the assigned type by **`check`**, and `check({:bounded_lit, cp}, Bounded(0x110000))` succeeds (`cp < 0x110000`). The elaborator (untrusted) is free to assign any type the kernel will `check`; it never relies on kernel `infer` reproducing `Bounded(0x110000)`. Every downstream use (argument, return, let-binding) validates via `check`, so consistency holds.

## 4. Testing

New `test/cure/elab/char_literal_test.exs`, modeled on `bounded_literal_test.exs`, using the `body_of(env, name) = Env.get_def(env, name).body` probe helper:

1. **Infer, no annotation** — `fn a() = 'a'` (or with a `Char` alias return) → body is `{:bounded_lit, 97}`.
2. **Check against `Char`** — `typealias Char = Bounded(1114112); fn a() -> Char = 'a'` → body `{:bounded_lit, 97}`.
3. **Full-plane emoji** — `'😀'` → `{:bounded_lit, 128512}` (one node).
4. **Out-of-range** — an AST-constructed `{:literal, [subtype: :char], 0x110000}` is rejected (`{:char_literal_out_of_range, _}`), and a negative codepoint likewise. (Construct via the elaborator entry directly since the lexer cannot emit these.)
5. **End-to-end runtime** — a module `fn emoji() -> Char = '😀'` compiled via the dependent `Emit.compile_and_load` and run returns the integer `128512`.
6. **Missing Bounded** — a char literal with no `use Std.Bounded` in scope errors `{:char_literal_needs_bounded, _}`, not a crash. (Only if the Bounded family is genuinely absent in the test env; if `Std.Bounded` is auto-seeded as core, assert the positive path instead and note it.)

Strict red-green TDD: write the failing test, watch it fail with `{:unsupported_expression, …}` for the `:char` case, implement, watch green. Then scoped `mix test test/cure/elab/ test/cure/core/` (no regression), and the full suite once at the gate.

## 5. Non-goals / risks

- **Not** char patterns, string literals, `Binary`, `Std.String` — separate tasks.
- **Not** a canonical stdlib `Char` alias — the literal works standalone; the alias is a later ergonomic add.
- **Risk:** the `char_type_value` helper couples char literals to a registered Bounded family. Mitigated by the clear `{:char_literal_needs_bounded, _}` error. `Std.Bounded` is `@group(:core)`; if it is auto-available the coupling is invisible in practice.
- **Risk:** allowing `'a' : Bounded(n)` for any `n > cp` (not strictly `Char`) is a deliberate consistency choice with integer literals, called out in §3.2 — not a faithfulness regression to fix.
