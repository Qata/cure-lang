# Value-Surface Wave 2 — `List` builtin family — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bring `List` and its surface sugar (`[]`, `[h | t]`, `[a, b, c]`) into the DEPENDENT pipeline as a builtin inductive family with **native BEAM-list emit** — following the Bool→atom / Nat→integer / Sigma→bare-2-tuple precedent — with NO kernel/TCB change.

**Architecture:** `List` is a plain 2-ctor `data` inductive `type List(a) = Nil | Cons(a, List(a))`. (1) It is seeded programmatically so its family + `Nil`/`Cons` ctors resolve in every module (like Sigma), and declared `@builtin(:list)` in `std/list.cure`; a structural drift test pins seed==declaration. (2) Surface `:list` nodes desugar to `Nil`/`Cons` constructor-call form in both expression and pattern position, reusing all existing ctor/pattern machinery. (3) `emit.ex` special-cases the `List` ctors to real BEAM cons cells and a `[]`/`[H|T]` `case`. "Nativeness" is emit-only; `lib/cure/core/*` (the kernel proper) is untouched.

**Tech Stack:** Elixir; Cure dependent elaborator (`lib/cure/elab/*`) + emit (`lib/cure/elab/emit.ex`) + builtin seeder (`lib/cure/core/builtins.ex`, schema/seed only) + `lib/std/list.cure`; ExUnit.

## Global Constraints

- **Spec:** `docs/superpowers/specs/2026-07-09-wave2-list-design.md` (hardened, commit f7b9464). Read it fully first; this plan implements it exactly.
- **Diff scope:** `lib/cure/core/builtins.ex` (schema line + `seed/2` chain link + new `list_family`/`list_ctors` helpers — NOT the kernel proper), `lib/std/list.cure`, `lib/cure/elab/elaborator.ex` (+ possibly a small new desugar helper module under `lib/cure/elab/`), `lib/cure/elab/emit.ex`, and new test files. The **kernel proper** — `lib/cure/core/{eval,normalise,conv,quote,kernel,term,erase,inductive}.ex` — MUST stay EMPTY of changes (builtins.ex is the seeder, not the TCB; it is the ONE `core/` file this wave touches).
- **Two-pipeline steer:** the dependent machinery lives ONLY in `lib/cure/elab/*` + `lib/cure/core/*` + `emit.ex`. IGNORE `lib/cure/compiler/*` (`codegen.ex`, `pattern_compiler.ex`) and `lib/cure/types/*` — their list/cons handling is the classic pipeline (a DECOY), read ONLY as a behavioral oracle (see §Oracle).
- **BUILD-LOCK:** #22 and Wave-1 have landed, so the build lock is free at plan-execution time. Still: only ONE `mix` suite at a time (a past concurrent run caused a kernel panic). Prefer scoped `mix test <file>`; full suite exactly ONCE at the gate. No `iex -S mix`.
- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO `Co-Authored-By`, NO Claude signature, NO trailers.
- **Explicit-pathspec staging ONLY:** `git add -- <path>` / `git commit -m "..." -- <path>`. NEVER `git add -A` / `.` / `-u` — a concurrent agent may share this worktree.
- **Tests immutable once green**, behavioral not implementation-coupled. Strict red-green.
- **Do NOT touch `lib/cure/elab/declarations.ex`'s dispatch whitelist** (the third-dispatch-layer gotcha: a bare top-level list body elaborates infer-only, acceptable this wave exactly as for pickup — ledgered, not fixed).

## Anchors verified against current source (2026-07-09)

- `Builtins.@schemas` — `builtins.ex:14-19` (currently `bool/nat/eq/sigma`).
- `Builtins.seed/2` chain — `builtins.ex:104-111` (`|> maybe_seed(:bool …) |> … |> maybe_seed(:sigma …) |> seed_ops()`).
- `maybe_seed/5` — `builtins.ex:169-175` (skips seeding a family whose name is in the `exclude` set = the compiled module's own declared type names).
- `declare_and_register/4` — `builtins.ex:177-182` (`Inductive.declare` → `validate!` → `Inductive.register_builtin`).
- Family/ctor constructors precedent — `nat_family`/`nat_ctors` (`builtins.ex:194-200`, self-referential `S`), `sigma_family`/`sigma_ctors` (`builtins.ex:227-241`, parametrized). `Inductive.family/4` and `Inductive.ctor/3,4,5` are the builders (see their arities in `inductive.ex`).
- `@builtin`/prelude-source registration — `program.ex:742-753` (`maybe_register_builtin`), `prelude_source?/1` `program.ex:215-216`, `declared_type_names/1` `program.ex:165-168`, seed call sites `program.ex:134`/`:514`.
- Emit ctor lowering cond — `emit.ex:162-182`; branch dispatch `branch_clause/3` `emit.ex:401-407`; `sigma_branch_clause` `emit.ex:413-421`; `nat_branch_clause` `emit.ex:430-443`; `sigma_ctor?` `emit.ex:513-516`; `underscore_if_unused/2` `emit.ex:479-481`.
- Parser `:list` node — `parser.ex:759-843`: `{:list, [line,col], []}` (empty); `{:list, [cons: true, …], [head, tail]}` (`[h|t]`); `{:list, [line], [e1,…,eN]}` (literal); `[a,b|rest]` right-nested via `build_multi_head_cons/3` `parser.ex:837-843`. Match-arm list patterns are the SAME `:list` nodes.
- `constructor_pattern/1` bare-var rule — `elaborator.ex:3777-3805`, nested rejected `{:error, {:unsupported_pattern, :nested_constructor_arg}}` at `:3803`.
- Value dispatchers (for the desugar clauses) — `elaborate_expr_typed` catch-all `elaborator.ex:554`; `elaborate_expr_checked` fallback `:1032`; scoped `elaborate_expr` catch-all `:4793`; the Sigma `%[..]` `:tuple` clause at `elaborator.ex:4765-4770` is the closest surface-sugar→ctor precedent.
- Sigma drift test to mirror — `test/antigen/builtin_sigma_drift_test.exs`.

---

## Task 1: Seed the `:list` builtin family + declare it in `std/list.cure`

**Deliverable:** the `:list` family is seeded into every base env, `Std.List` declares `@builtin(:list) type List(a) = Nil | Cons(a, List(a))`, and a structural drift test proves the seeded family is byte-for-byte identical to the source-declared one. Independently verifiable via the drift test alone.

**Files:**
- Modify: `lib/cure/core/builtins.ex` (schema entry, seed-chain link, `list_family`/`list_ctors` helpers)
- Modify: `lib/std/list.cure` (add the `@builtin(:list)` declaration)
- Test: `test/antigen/builtin_list_drift_test.exs` (create)

- [ ] **Step 1: Write the drift test (RED) — the oracle for the seed's exact shape**

Create `test/antigen/builtin_list_drift_test.exs`, mirroring `builtin_sigma_drift_test.exs`:

```elixir
defmodule Antigen.BuiltinListDriftTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Builtins}

  # The @builtin(:list) surface declaration in Std.List is the source of truth;
  # Builtins.seed/2 carries a byte-for-byte programmatic mirror so [..]/[h|t] work
  # in every module without `use`. This antibody fails if the two ever drift.
  # First parametrized + self-referential family through this comparison.
  @list_src """
  mod Std.List
    @group(:collections)
    @builtin(:list)
    type List(a) = Nil | Cons(a, List(a))
  """

  test "the seeded :list family exists with ctors Nil/0 and Cons/2" do
    seeded = Builtins.seed(Env.empty())
    assert Inductive.builtin(seeded, :list) == :List

    ctors =
      seeded
      |> Inductive.ctors_of(:List)
      |> Enum.map(fn c -> {c.name, length(c.args)} end)
      |> Enum.sort()

    assert ctors == [{:Cons, 2}, {:Nil, 0}]
  end

  test "prelude-compiled Std.List family is structurally identical to Builtins.seed's" do
    {:ok, env} = Cure.Elab.Program.elaborate(@list_src)
    seeded = Builtins.seed(Env.empty())

    assert Inductive.get_family(env, :List) == Inductive.get_family(seeded, :List)

    from_prelude = env |> Inductive.ctors_of(:List) |> Enum.sort_by(& &1.name)
    from_seed = seeded |> Inductive.ctors_of(:List) |> Enum.sort_by(& &1.name)
    assert from_prelude == from_seed
  end

  test "Inductive.builtin(env, :list) resolves after seeding" do
    assert Inductive.builtin(Builtins.seed(Env.empty()), :list) == :List
  end
end
```

- [ ] **Step 2: Run it — expect RED**

Run: `mix test test/antigen/builtin_list_drift_test.exs`
Expected: FAIL — `Inductive.builtin(seeded, :list)` is `nil` (no `:list` seed yet); and `Program.elaborate(@list_src)` may itself error because `@builtin(:list)` is not a known schema key. Both are the red signal.

- [ ] **Step 3: Add the schema entry**

In `lib/cure/core/builtins.ex:14-19`, add the `list` key:

```elixir
  @schemas %{
    bool: [{:False, 0}, {:True, 0}],
    nat: [{:Z, 0}, {:S, 1}],
    eq: [{:reflexive, 1}],
    sigma: [{:mk_pair, 2}],
    list: [{:Nil, 0}, {:Cons, 2}]
  }
```

- [ ] **Step 4: Add the `@builtin(:list)` declaration to `std/list.cure`**

Near the top of `mod Std.List` (after the `@group` decorator, before the functions), add:

```
@builtin(:list)
type List(a) = Nil | Cons(a, List(a))
```

(This routes through the already-working parametrized-ADT GADT machinery — `declarations.ex:103-123` `:enum` branch → `variant_to_gadt_sig` → `declare_parameterized`, the same path `Std.Iter`/`Std.NonEmpty` use.) Do NOT yet worry about whether the rest of `list.cure` elaborates — that is Task 4's audit.

- [ ] **Step 5: Add the seed helpers + chain link, converging against the drift test**

Add to the `seed/2` chain (`builtins.ex:104-111`), immediately before `|> seed_ops()`:

```elixir
    |> maybe_seed(:list, list_family(), list_ctors(), exclude)
```

Add the family/ctor helpers near `sigma_family`/`sigma_ctors` (`builtins.ex:227-241`). **The exact de Bruijn form of the ctor field/result telescope is NOT hand-guessable — derive it against the drift test.** Start from this shape (List = 1 param `a`, 0 indices, level 0; `Nil` nullary; `Cons` has fields `a` and `List(a)`, the second self-referential like `nat`'s `S`):

```elixir
  # List : (a : Type) -> Type   (1 param, no indices)
  #   Nil  : List(a)
  #   Cons : (x : a) -> (xs : List(a)) -> List(a)
  # Source of truth is the @builtin(:list) decl in Std.List; this seed is its
  # byte-for-byte mirror, pinned by builtin_list_drift_test.exs.
  defp list_family, do: Inductive.family(:List, [a: {:type, 0}], [], 0)

  defp list_ctors,
    do: [
      Inductive.ctor(:Nil, [], []),
      Inductive.ctor(:Cons, [x: {:var, 0}, xs: {:data, :List, [{:var, 1}], []}], [])
    ]
```

Then **iterate against the drift test as the oracle**: run `mix test test/antigen/builtin_list_drift_test.exs`; the `get_family(env,:List) == get_family(seeded,:List)` / sorted-ctors assertions print the exact structural diff between the source-declared family (the ground truth, built by the real elaborator from Step 4's declaration) and your `list_family`/`list_ctors`. Adjust the de Bruijn indices, field names, and any quantity/result-arg lists (`Inductive.ctor/4,5` — compare against how `sigma_ctors`/`eq_ctors` fill their 4th/5th args) until the two families are `==`. **The elaborated declaration is authoritative; the seed must match IT, not the other way round.** If they cannot be reconciled to structural equality, STOP and report — do NOT special-case `merge_env` or the drift comparison to paper over a mismatch.

- [ ] **Step 6: Run the drift test — expect GREEN**

Run: `mix test test/antigen/builtin_list_drift_test.exs`
Expected: all three tests PASS.

- [ ] **Step 7: Sanity — the seed didn't break existing builtins**

Run: `mix test test/cure/elab/builtin_prelude_seed_test.exs test/antigen/builtin_bool_drift_test.exs test/antigen/builtin_sigma_drift_test.exs`
Expected: PASS (adding `:list` to the chain must not perturb bool/nat/eq/sigma).

- [ ] **Step 8: Commit**

```bash
git -C <worktree> add -- lib/cure/core/builtins.ex lib/std/list.cure test/antigen/builtin_list_drift_test.exs
git -C <worktree> commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(elab): seed :list builtin family + @builtin(:list) in Std.List (value-surface Wave 2)" \
  -- lib/cure/core/builtins.ex lib/std/list.cure test/antigen/builtin_list_drift_test.exs
```

---

## Task 2: Desugar `:list` surface nodes → `Nil`/`Cons` ctor form (expression + pattern)

**Deliverable:** `[]`, `[h|t]`, `[a,b,c]`, and `[a,b|rest]` in expression position, and `[]`/`[h|t]` in pattern position, elaborate through the dependent pipeline (no `{:unsupported_expression, {:list,…}}`). Verified at the elaboration level (Task 3 adds runtime).

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` (add a `desugar_list/1` helper + thin `:list` clauses that rewrite-and-delegate)
- Test: `test/cure/elab/list_test.exs` (create; elaboration-level assertions in this task, runtime in Task 3)

**Design (LOCKED option i — reuse ctor machinery):** rewrite a `{:list, meta, elems}` surface node into the equivalent **surface constructor-call node** and delegate to the EXISTING elaboration of that node, so all ctor inference / pattern / exhaustiveness code is reused verbatim. A list ctor call is a `{:function_call, [name: "Cons"|"Nil", line:…, col:…], args}` surface node (the same shape `Z()`/`empty()`/`prepend(x, rest)` parse to — confirmed: `elaborate_named_call_scoped` reads `Keyword.fetch!(meta, :name)`, `elaborator.ex:4796`).

- [ ] **Step 1: Write elaboration-level tests (RED)**

Create `test/cure/elab/list_test.exs` with (for this task) elaboration-success assertions; runtime asserts come in Task 3.

```elixir
defmodule Cure.Elab.ListTest do
  @moduledoc """
  `List` value surface in the dependent pipeline (Wave 2). `[]`/`[h|t]`/`[a,b,c]`
  desugar to `Nil`/`Cons` ctor calls (reusing all ctor machinery) and emit as
  native BEAM cons cells. Tests use Int/Nat elements; nested list *patterns*
  (`[a,b] ->`) are out of scope this wave (see the ledger test).
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "an empty-list literal elaborates" do
    src = "mod M\n  fn e() -> List(Int) = []\nend\n"
    assert {:ok, _} = Program.elaborate(src)
  end

  test "a multi-element list literal elaborates" do
    src = "mod M\n  fn xs() -> List(Int) = [1, 2, 3]\nend\n"
    assert {:ok, _} = Program.elaborate(src)
  end

  test "a cons literal elaborates" do
    src = "mod M\n  fn c(h: Int, t: List(Int)) -> List(Int) = [h | t]\nend\n"
    assert {:ok, _} = Program.elaborate(src)
  end

  test "a one-deep list pattern match elaborates" do
    src =
      @nat <>
        "  fn is_empty(xs: List(Nat)) -> Bool =\n" <>
        "    match xs\n" <>
        "      [] -> true\n" <>
        "      [h | t] -> false\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "a mismatched-element list is rejected in checked position" do
    src = "mod M\n  fn bad() -> List(Int) = [1, true]\nend\n"
    assert {:error, _} = Program.elaborate(src)
  end

  test "a genuinely nested list pattern is rejected cleanly (ledger guard, NOT a crash)" do
    src =
      @nat <>
        "  fn f(xs: List(Nat)) -> Bool =\n" <>
        "    match xs\n" <>
        "      [a, b] -> true\n" <>
        "      other -> false\nend\n"

    assert {:error, _} = Program.elaborate(src)
  end
end
```

- [ ] **Step 2: Run — expect RED** (`{:error, {:unsupported_expression, {:list,…}}}` for the ok-tests; the reject tests may pass for the wrong reason pre-change).

Run: `mix test test/cure/elab/list_test.exs`

- [ ] **Step 3: Add `desugar_list/1` + the `:list` clauses**

Add a recursive surface-rewrite helper (place with other private elaborator helpers):

```elixir
  # Wave-2 List sugar → ctor-call surface form (reuses all ctor machinery).
  #   []            -> Nil()
  #   [h | t]       -> Cons(h, t)              (meta carries `cons: true`)
  #   [e1, …, eN]   -> Cons(e1, Cons(…, Nil))  (right fold)
  # Recurses into sub-elements/sub-patterns so a list-of-lists desugars fully.
  # `m` threads the original node's line/col into the synthesized ctor calls.
  defp desugar_list({:list, m, []}), do: ctor_call("Nil", m, [])

  defp desugar_list({:list, m, [h, t]} = node) do
    if Keyword.get(m, :cons, false) do
      ctor_call("Cons", m, [desugar_list(h), desugar_list(t)])
    else
      # a 2-element literal (no cons flag) folds like any other literal
      fold_list_literal([h, t], m)
    end
  end

  defp desugar_list({:list, m, elems}), do: fold_list_literal(elems, m)
  defp desugar_list(other), do: other

  defp fold_list_literal(elems, m) do
    Enum.reduce(Enum.reverse(elems), ctor_call("Nil", m, []), fn e, acc ->
      ctor_call("Cons", m, [desugar_list(e), acc])
    end)
  end

  defp ctor_call(name, m, args),
    do: {:function_call, [name: name] ++ Keyword.take(m, [:line, :col]), args}
```

Add thin `:list` clauses that desugar-and-delegate, immediately before each catch-all/fallback:
- `elaborate_expr_typed({:list, _, _} = node, names, ctx, env)` (before `:554`): `elaborate_expr_typed(desugar_list(node), names, ctx, env)`.
- `elaborate_expr_checked({:list, _, _} = node, expected_core, names, ctx, env)` (before `:1032`): delegate with `expected_core`.
- `elaborate_expr({:list, _, _} = node, scope, env)` (before the `:4793` catch-all): `elaborate_expr(desugar_list(node), scope, env)`.
- **Pattern position:** find where a `match`-arm pattern is dispatched (the caller of `constructor_pattern/1`). A `:list` pattern node must be `desugar_list`'d to the `{:function_call, [name: "Cons"|"Nil"], …}` form BEFORE `constructor_pattern/1` sees it, so a one-deep `[h|t]` becomes `Cons(h, t)` with bare-variable sub-patterns (accepted) and `[]` becomes `Nil()` (accepted). Add the desugar at the pattern-normalization entry point (mirror how the pattern path already accepts `{:function_call,…}` ctor patterns). If the cleanest hook is a single pre-pass over the arm's `:pattern`, use that; the observable contract is that no `:list` node reaches `constructor_pattern/1`.

**Verification note for the executor:** confirm by tracing that `desugar_list` is invoked in BOTH expression and pattern position — the reject test "genuinely nested list pattern" must fail with `{:unsupported_pattern, :nested_constructor_arg}` (proving the desugar reached the pattern path and produced a nested ctor pattern), NOT with `{:unsupported_expression, {:list,…}}` (which would prove the pattern path never desugared).

- [ ] **Step 4: Run — expect GREEN**

Run: `mix test test/cure/elab/list_test.exs`
Expected: all pass. The nested-pattern reject test now fails via `:nested_constructor_arg` (right reason); the mismatched-element test fails via the ctor/kernel type error.

- [ ] **Step 5: Commit**

```bash
git -C <worktree> add -- lib/cure/elab/elaborator.ex test/cure/elab/list_test.exs
git -C <worktree> commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(elab): desugar [..]/[h|t] list sugar to Nil/Cons ctor form (value-surface Wave 2)" \
  -- lib/cure/elab/elaborator.ex test/cure/elab/list_test.exs
```

---

## Task 3: Native BEAM-list emit

**Deliverable:** `[1,2,3]` compiles to the BEAM term `[1,2,3]` (real cons cells) and a list `match` compiles to a `case` on `[]`/`[H|T]`.

**Files:**
- Modify: `lib/cure/elab/emit.ex` (add `list_ctor?/2`, a cons arm in the ctor-lowering cond, and `list_branch_clause`)
- Test: `test/cure/elab/list_test.exs` (extend Task-2's file with runtime asserts)

- [ ] **Step 1: Add runtime assertions (RED)** — append to `test/cure/elab/list_test.exs`:

```elixir
  test "a list literal emits a NATIVE BEAM list" do
    src = "mod M\n  fn xs() -> List(Int) = [1, 2, 3]\nend\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.List1", functions: [:xs])

    result = apply(mod, :xs, [])
    assert result == [1, 2, 3]
    assert is_list(result)
  end

  test "the empty list emits []" do
    src = "mod M\n  fn e() -> List(Int) = []\nend\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.List2", functions: [:e])
    assert apply(mod, :e, []) == []
  end

  test "[h | t] builds the expected native list" do
    src = "mod M\n  fn c(h: Int, t: List(Int)) -> List(Int) = [h | t]\nend\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.List3", functions: [:c])
    assert apply(mod, :c, [1, [2, 3]]) == [1, 2, 3]
  end

  test "a one-deep list match selects the arm at runtime" do
    src =
      @nat <>
        "  fn is_empty(xs: List(Nat)) -> Bool =\n" <>
        "    match xs\n" <>
        "      [] -> true\n" <>
        "      [h | t] -> false\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.List4", functions: [:is_empty])
    assert apply(mod, :is_empty, [[]]) == true
    assert apply(mod, :is_empty, [[:Z]]) == false
  end
```

- [ ] **Step 2: Run — expect RED** (compiles to a tagged tuple `{:Cons,…}`/`:Nil` today, so `== [1,2,3]` / `is_list` fail, and the match won't select on `[]`/`[H|T]`).

Run: `mix test test/cure/elab/list_test.exs`

- [ ] **Step 3: Add the `list_ctor?` predicate** — in `emit.ex` near `sigma_ctor?` (`:513-516`):

```elixir
  # The canonical Std.List family (registry-keyed, nominal): its values are native
  # BEAM lists — Nil is [], Cons(h,t) is [H|T] — so Erlang/AtomVM list NIFs interop.
  defp list_ctor?(env, name) do
    fam = Inductive.builtin(env, :list)
    fam != nil and Inductive.ctor_family(env, name) == fam
  end
```

- [ ] **Step 4: Add the native cons value-lowering arm** — in the `lower(env, {:ctor, name, args}, ctx)` cond (`emit.ex:162-182`), add a `list_ctor?` branch (place it with the other builtin arms, before the generic `true ->`):

```elixir
      list_ctor?(env, name) ->
        case {name, args} do
          {:Nil, []} -> {nil, @line}
          {:Cons, [h, t]} -> {:cons, @line, lower(env, h, ctx), lower(env, t, ctx)}
        end
```

(`{nil, @line}` is the Erlang abstract form for `[]` — Elixir `nil` is the Erlang `nil` atom; `{:cons, @line, H, T}` is `[H|T]`. Matches how `sigma_ctor?` builds `{:tuple, …}`.)

- [ ] **Step 5: Add `list_branch_clause`** — register it in the `branch_clause/3` dispatch (`emit.ex:401-407`) alongside nat/sigma:

```elixir
      list_ctor?(env, cname) -> list_branch_clause(env, {cname, arity, body}, ctx)
```

and define it near `sigma_branch_clause` (`emit.ex:413-421`), following that template (field de Bruijn: index 0 = last field, so `[tail, head | ctx]`):

```elixir
  # case-on-List: Nil matches [], Cons(h,t) matches [H|T], binding both fields
  # into the de Bruijn frame exactly as the generic tagged form would.
  defp list_branch_clause(env, {:Nil, 0, body}, ctx) do
    {:clause, @line, [{nil, @line}], [], [lower(env, body, ctx)]}
  end

  defp list_branch_clause(env, {:Cons, 2, body}, ctx) do
    base = length(ctx)
    vh = :"V#{base}"
    vt = :"V#{base + 1}"
    body_form = lower(env, body, [vt, vh | ctx])
    ph = underscore_if_unused({:var, @line, vh}, body_form)
    pt = underscore_if_unused({:var, @line, vt}, body_form)
    {:clause, @line, [{:cons, @line, ph, pt}], [], [body_form]}
  end
```

- [ ] **Step 6: Run — expect GREEN**

Run: `mix test test/cure/elab/list_test.exs`
Expected: all pass, including `is_list/1` and `== [1,2,3]`.

- [ ] **Step 7: Commit**

```bash
git -C <worktree> add -- lib/cure/elab/emit.ex test/cure/elab/list_test.exs
git -C <worktree> commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "feat(elab): native BEAM-list emit for List ctors + case (value-surface Wave 2)" \
  -- lib/cure/elab/emit.ex test/cure/elab/list_test.exs
```

---

## Task 4: `Std.List` audit, oracle-equivalence, ratchet, full gate

**Deliverable:** the wave is proven correct against the classic oracle and the ratchet, with the full suite green.

- [ ] **Step 1: Audit `lib/std/list.cure`'s patterns.** Read every function; classify each as one-deep (`[]`/`[h|t]` with bare-var sub-patterns — will dependent-elaborate) vs. deeper (nested list pattern — out of scope this wave). Record the classification in the commit message / a ledger note. Do NOT rewrite deeper patterns to dodge the gap; leave them and ledger.

- [ ] **Step 2: `Std.List` smoke test.** Add to `test/cure/elab/list_test.exs` one directed test that elaborates `use Std.List` and runs a real one-deep `Std.List` function through the dependent pipeline (pick one the audit confirms is one-deep — e.g. `cons`/`is_empty`/a `head`-with-default). Assert its runtime result. Red-first, then it passes on the already-implemented Tasks 1-3.

- [ ] **Step 3: Oracle-equivalence (roadmap §3 item 6).** The classic behavioral oracle for lists is `test/cure/compiler/codegen_test.exs`, `test/cure/compiler/pattern_compiler_test.exs`, and the multi-head-cons test (`test/cure/compiler/multi_head_cons_test.exs` if present — else the cons cases in codegen_test). These are CLASSIC-pipeline tests and STAY GREEN (the classic pipeline is untouched this wave). Confirm they still pass — they are the semantics reference the dependent runtime results were mirrored against (native BEAM lists, first-arm-wins match). Do NOT edit them.

- [ ] **Step 4: Firewall + core-scope.** Run `mix test test/cure/dependent_pipeline_firewall_test.exs` (green). Confirm `git -C <worktree> diff --stat` shows the kernel proper (`core/{eval,normalise,conv,quote,kernel,term,erase,inductive}.ex`) UNTOUCHED — only `core/builtins.ex` changed in `core/`.

- [ ] **Step 5: Ratchet.** Re-run the stdlib disposition script (roadmap §0). Record KEEP before/after. Expected: `Std.List` flips toward KEEP (fully if all its used patterns are one-deep, else partially), plus any module whose only blocker was List. State which moved and which remain blocked (and on what). A regression in the prior KEEP set (bool/bounded/decision/equivalent/nat/proof/sigma/vector) = STOP.

- [ ] **Step 6: Oracle replay.** Run `mix test test/oracle_replay_test.exs` — report the live `N/N`; NO verdict may flip (List is additive).

- [ ] **Step 7: Full suite ONCE.** Run `mix test` — 0 failures, total = prior baseline (3154 after Wave 1) + all new Wave-2 tests. Any unrelated pre-existing failure your diff did not cause → STOP and report, do not "fix" out of scope.

- [ ] **Step 8: Commit** the smoke test + any ledger note:

```bash
git -C <worktree> add -- test/cure/elab/list_test.exs
git -C <worktree> commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" \
  -m "test(elab): Std.List one-deep smoke through dependent pipeline (value-surface Wave 2)" \
  -- test/cure/elab/list_test.exs
```

Each of the four commits must be independently full-suite-green (the #22 Part-A precedent) — if a mid-task commit would leave the suite red, fold it forward so every commit is green.

---

## Out of scope (do NOT build here)

- Genuinely nested list-literal **patterns** (`[1,2,3] ->`, `[a,b] ->`, `[a,b|rest] ->`) — the general `nested_constructor_arg` decision-tree lift (`elaborator.ex:3803`), shared with `Nat`'s `S(S(m))`; its own increment. The ledger-guard test pins this boundary.
- List **comprehensions** (`[x for x <- xs, …]`) — separate feature.
- Adding `Std.List` to `@auto_prelude` (seed only, per spec §1.1).
- Everything else in the program (lambda-inference, String, @extern, Map/tuples/tail).
- Any change to the kernel proper (`core/{eval,normalise,conv,quote,kernel,term,erase,inductive}.ex`), to `pickup`/`conditional`/`match`/`bool_case`/`sigma`/`nat` emit internals, or to `declarations.ex`'s dispatch whitelist.
