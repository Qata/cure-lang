# Builtin-Inductive Foundation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Introduce a builtin-inductive registry so the kernel and erasure can resolve a canonical inductive by key, use it to retire the bespoke `bool_elim` primitive by making `Bool` a real inductive checked through the general `:case`, and give `Nat` a native machine-integer runtime representation.

**Architecture:** A schema-validated registry lives on the kernel's signature struct (`Cure.Core.Env`), seeded once from the prelude's `@builtin`-tagged `Bool`/`Nat` declarations (and mirrored by a programmatic `Cure.Core.Builtins.seed/1` for kernel-internal and conformance test contexts). `infer_prim` and `eval`'s `fold/2` produce the inductive `Bool`'s `True`/`False` constructors instead of the primitive `{:vbool*}` forms; `if`/guards/literal-patterns desugar to `:case` on `Bool` instead of `bool_elim`; the `bool_elim`/`bool_type`/`bool_lit` term family is deleted across nine core modules. Erasure lowers `Bool`'s constructors to native `false`/`true` atoms and (Phase 2, below the kernel) `Nat`'s constructors to native integers.

**Tech Stack:** Elixir (compiler host), Cure surface language, BEAM/Erlang abstract forms (codegen target), ExUnit (tests), Antigen (metatheory/soundness antibodies), the differential oracle (`mix cure.oracle`) vs `idris2`.

## Global Constraints

- **Ghost-writer commits.** `git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>"`; NO `Co-Authored-By`, no Claude signature.
- **Explicit-pathspec staging only.** `git add -- <path>` and `git commit -- <path>`; NEVER `git add -A` / `git add .` (a concurrent agent may share the worktree).
- **One build at a time.** Never run two `mix` suites concurrently (a past concurrent full-suite run caused a kernel panic). Prefer scoped `mix test <file>`; run the full suite once, alone, at each phase gate.
- **Stay on branch `autopilot/lean-shape-matching`.** Do NOT create a new branch or worktree.
- **TCB HARD-STOP (Phase 1).** Every task in Phase 1 touches `lib/cure/core/*`. The Phase 1 gate (Task 12) requires: red-green per task, a new Antigen antibody, the full Antigen suite, the full test suite, AND an explicit human review before merge. Do NOT auto-merge Phase 1.
- **Z3 stays OUT of the dependent kernel TCB** — untrusted lint only (not touched by this plan; restated for scope).
- **Entry point is `start/0`**, not `main/0`; compile Cure for AtomVM with OTP 26–28 (host `mix test` may use newer).
- **Tests are behavioral and immutable once green.** The one sanctioned exception in this plan: assertions that pin the *old primitive Bool representation* (`{:vbool_type}`, `{:vbool, b}`, `bool_elim` terms, `(bool-type)` conformance lines) are being changed by an intentional representation migration — updating exactly those assertions to the new inductive representation is part of the cutover, not a test edit-to-pass. Every such change is called out in the task that makes it.

**Resolved design decisions** (the spec flagged two as open; both are decided here so implementation has no ambiguity):

1. **Bootstrap-seeded Env.** The real compile seeds `:bool`/`:nat` from the prelude's `@builtin` declarations. Kernel unit tests and the `core_conformance` harness operate on bare `Context.empty()` contexts that never load the prelude, yet `infer_prim`/`eval` now need `:bool` resolved. Decision: add `Cure.Core.Builtins.seed/1`, which declares the canonical `Bool` and `Nat` families and registers their builtin keys on an `Env`. The prelude path and the test/conformance path both obtain a seeded base env this way; a single test (Task 4, Step teardown) asserts the prelude-compiled `:bool` family is structurally identical to `Builtins.seed(Env.empty())`'s, preventing drift.

2. **Nat native-Int is contingent on monomorphisation (Phase 2).** `Nat`'s native-integer representation is applied only where `Nat` appears **concretely** in erased code. A function generic over an abstract type parameter that is instantiated at `Nat` gets the native rep in its *monomorphised* copy; an unspecialised generic body over an abstract parameter keeps the generic `{:ctor, …}` tuple/atom representation and does NOT receive native-Int lowering. Phase 2 Task 15 verifies monomorphisation runs before erasure for the dependent path and guards the fallback (an abstract-parameter body never emits a native-int decrement).

---

## Phase 1 — Registry + Bool-as-inductive (TCB, GATED)

Tasks 1–4 are purely additive (the tree stays green with the primitive `Bool` still in place). Tasks 5–11 are the cutover and deletion. Task 12 is the gate.

---

### Task 1: Builtin-bindings field + accessors on `Cure.Core.Env`

**Files:**
- Modify: `lib/cure/core/inductive.ex` (the `Cure.Core.Env` defstruct at lines 1-86, and `Cure.Core.Inductive` accessors)
- Test: `test/cure/core/builtins_registry_test.exs` (create)

**Interfaces:**
- Produces:
  - `Cure.Core.Env` gains field `builtins: %{}` (`%{atom() => atom()}`, key → family-id).
  - `Cure.Core.Inductive.register_builtin(env, key, family_id)` → `Env.t()`; raises `ArgumentError` if `key` already bound (single-registration invariant).
  - `Cure.Core.Inductive.builtin(env, key)` → `atom() | nil` (the family-id) — consumed by kernel `infer_prim` and erasure.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/core/builtins_registry_test.exs
defmodule Cure.Core.BuiltinsRegistryTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive}

  test "register_builtin binds a key resolvable by builtin/2" do
    env = Inductive.register_builtin(Env.empty(), :bool, :Bool)
    assert Inductive.builtin(env, :bool) == :Bool
  end

  test "builtin/2 returns nil for an unbound key" do
    assert Inductive.builtin(Env.empty(), :bool) == nil
  end

  test "a second registration of the same key is a hard error" do
    env = Inductive.register_builtin(Env.empty(), :bool, :Bool)
    assert_raise ArgumentError, ~r/already bound/, fn ->
      Inductive.register_builtin(env, :bool, :OtherBool)
    end
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/builtins_registry_test.exs`
Expected: FAIL — `builtins` key not in struct / `register_builtin`/`builtin` undefined.

- [ ] **Step 3: Add the field and functions**

In `lib/cure/core/inductive.ex`, extend the `Cure.Core.Env` defstruct and typespec:

```elixir
defstruct families: %{}, ctors: %{}, ctor_to_family: %{}, defs: %{}, certified: nil, builtins: %{}

@type t :: %__MODULE__{
        families: %{atom() => map()},
        ctors: %{atom() => map()},
        ctor_to_family: %{atom() => atom()},
        defs: %{atom() => map()},
        certified: MapSet.t() | nil,
        builtins: %{atom() => atom()}
      }
```

In `defmodule Cure.Core.Inductive`, add:

```elixir
@doc "Bind a builtin key to a family-id. Hard error on re-registration (single-registration invariant)."
@spec register_builtin(Env.t(), atom(), atom()) :: Env.t()
def register_builtin(%Env{builtins: b}, key, _family_id) when is_map_key(b, key) do
  raise ArgumentError, "builtin key #{inspect(key)} already bound to #{inspect(Map.fetch!(b, key))}"
end

def register_builtin(%Env{} = env, key, family_id) do
  %{env | builtins: Map.put(env.builtins, key, family_id)}
end

@doc "Resolve a builtin key to its family-id, or nil."
@spec builtin(Env.t(), atom()) :: atom() | nil
def builtin(%Env{builtins: b}, key), do: Map.get(b, key)
```

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/core/builtins_registry_test.exs`
Expected: PASS (3 tests).

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/core/inductive.ex test/cure/core/builtins_registry_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(core): builtin-bindings registry on Env (register_builtin/builtin, single-registration)"
```

---

### Task 2: Schema validation (shape + constructor names)

**Files:**
- Create: `lib/cure/core/builtins.ex` (module `Cure.Core.Builtins`)
- Test: `test/cure/core/builtins_schema_test.exs` (create)

**Interfaces:**
- Consumes: `Env`, `Inductive.get_family/2`, `Inductive.ctors_of/2`, `Inductive.arg_telescope/2` (from `inductive.ex`).
- Produces:
  - `Cure.Core.Builtins.schema(key)` → the expected schema descriptor for `:bool`/`:nat` (raises for unknown key).
  - `Cure.Core.Builtins.validate!(env, key, family_id)` → `:ok` or raises `ArgumentError` with a specific reason (wrong arity, wrong/missing constructor names). Checks **names, not arity alone** (spec §1: a `Coin = Heads | Tails` tagged `@builtin(:bool)` must be rejected).

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/core/builtins_schema_test.exs
defmodule Cure.Core.BuiltinsSchemaTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Builtins}

  defp declare_family(env, fname, ctors) do
    family = %{name: fname, params: [], indices: []}
    ctor_maps =
      Enum.map(ctors, fn {cname, arg_types} ->
        %{name: cname, family: fname, args: arg_types, result_indices: []}
      end)
    Inductive.declare(env, family, ctor_maps)
  end

  test "a well-formed Bool passes validation" do
    env = declare_family(Env.empty(), :Bool, [{:False, []}, {:True, []}])
    assert :ok = Builtins.validate!(env, :bool, :Bool)
  end

  test "Bool with wrong constructor names is rejected" do
    env = declare_family(Env.empty(), :Coin, [{:Heads, []}, {:Tails, []}])
    assert_raise ArgumentError, ~r/expected constructors/, fn ->
      Builtins.validate!(env, :bool, :Coin)
    end
  end

  test "Bool with wrong arity is rejected" do
    env = declare_family(Env.empty(), :Bad, [{:False, []}, {:True, [{:family, :Bad}]}])
    assert_raise ArgumentError, ~r/arity|nullary/, fn ->
      Builtins.validate!(env, :bool, :Bad)
    end
  end

  test "a well-formed Nat passes validation" do
    env = declare_family(Env.empty(), :Nat, [{:Z, []}, {:S, [{:family, :Nat}]}])
    assert :ok = Builtins.validate!(env, :nat, :Nat)
  end
end
```

> **Implementer note:** confirm the exact constructor-map shape produced by `Inductive.declare/3` (field names `:args`/`:name`, how a recursive field referencing the family is represented) against `lib/cure/core/inductive.ex` and an existing declared family (e.g. from `test/cure/core/` fixtures). Adjust `declare_family/3`'s ctor-map and `Builtins.validate!/3`'s arity/field inspection to match the real representation — the test's `{:family, :Nat}` placeholder must be replaced with however a self-referential constructor field is actually encoded. The *behavior* asserted (names + arity checked, mismatch raises) is fixed; the field-access mechanics follow the real struct.

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/builtins_schema_test.exs`
Expected: FAIL — `Cure.Core.Builtins.validate!/3` undefined.

- [ ] **Step 3: Implement the schema + validator**

```elixir
# lib/cure/core/builtins.ex
defmodule Cure.Core.Builtins do
  @moduledoc """
  Canonical builtin-inductive schemas and the programmatic seeder.
  Schema validation checks constructor NAMES and arities, not arity alone:
  the literal wiring (true/false -> True/False) and erasure atom mapping
  (False/True -> false/true; Z/S -> int) key off these exact names, so a
  shape-conformant but name-mismatched binding is a real miscompile risk.
  """
  alias Cure.Core.{Env, Inductive}

  # key => list of {ctor_name, arity}. Names are load-bearing.
  @schemas %{
    bool: [{:False, 0}, {:True, 0}],
    nat: [{:Z, 0}, {:S, 1}]
  }

  @spec schema(atom()) :: [{atom(), non_neg_integer()}]
  def schema(key), do: Map.fetch!(@schemas, key)

  @spec validate!(Env.t(), atom(), atom()) :: :ok
  def validate!(%Env{} = env, key, family_id) do
    expected = schema(key)
    ctors = Inductive.ctors_of(env, family_id) || []

    actual =
      ctors
      |> Enum.map(fn c -> {c.name, length(Map.get(c, :args, []))} end)
      |> Enum.sort()

    if actual == Enum.sort(expected) do
      :ok
    else
      raise ArgumentError,
            "@builtin(#{inspect(key)}) on #{inspect(family_id)}: expected constructors " <>
              "#{inspect(Enum.sort(expected))} (name and arity), got #{inspect(actual)}"
    end
  end
end
```

> **Implementer note:** `Inductive.ctors_of/2` returns the family's constructor maps (confirm return shape; the Explore report lists it at `inductive.ex:247`). `Map.get(c, :args, [])`'s key must match the real ctor-map field for the argument telescope — verify against `arg_telescope/2`'s source and use that accessor if `:args` is not a direct field. Do NOT silently pass on a missing field; if the accessor differs, use it explicitly.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/core/builtins_schema_test.exs`
Expected: PASS (4 tests).

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/core/builtins.ex test/cure/core/builtins_schema_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(core): builtin schema validation (name+arity, not arity alone)"
```

---

### Task 3: `Builtins.seed/1` — canonical Bool + Nat families, validated

**Files:**
- Modify: `lib/cure/core/builtins.ex`
- Test: `test/cure/core/builtins_seed_test.exs` (create)

**Interfaces:**
- Consumes: `Inductive.declare/3`, `register_builtin/3`, `validate!/3`.
- Produces: `Cure.Core.Builtins.seed(env)` → `Env.t()` with the canonical `Bool` (`False | True`) and `Nat` (`Z | S(Nat)`) families declared, each validated, and `:bool`/`:nat` registered. This is the base env for kernel unit tests and the conformance harness (design decision 1).

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/core/builtins_seed_test.exs
defmodule Cure.Core.BuiltinsSeedTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Builtins}

  test "seed/1 registers validated bool and nat" do
    env = Builtins.seed(Env.empty())
    assert Inductive.builtin(env, :bool) == :Bool
    assert Inductive.builtin(env, :nat) == :Nat
    assert Inductive.family?(env, :Bool)
    assert Inductive.family?(env, :Nat)
  end

  test "seeded bool family has exactly False and True" do
    env = Builtins.seed(Env.empty())
    names = env |> Inductive.ctors_of(:Bool) |> Enum.map(& &1.name) |> Enum.sort()
    assert names == [:False, :True]
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/builtins_seed_test.exs`
Expected: FAIL — `Builtins.seed/1` undefined.

- [ ] **Step 3: Implement `seed/1`**

Add to `lib/cure/core/builtins.ex` (adjust the family/ctor map literals to the exact shape `Inductive.declare/3` expects, confirmed while implementing Task 2):

```elixir
@spec seed(Env.t()) :: Env.t()
def seed(%Env{} = env) do
  env
  |> declare_and_register(:bool, bool_family(), bool_ctors())
  |> declare_and_register(:nat, nat_family(), nat_ctors())
end

defp declare_and_register(env, key, family, ctors) do
  fid = family.name
  env = Inductive.declare(env, family, ctors)
  :ok = validate!(env, key, fid)
  Inductive.register_builtin(env, key, fid)
end

# NOTE: bool_family/bool_ctors/nat_family/nat_ctors build the SAME family
# maps Inductive.declare/3 consumes elsewhere. Keep the ctor NAMES here in
# single-source-of-truth agreement with @schemas above and with eval.ex's
# hardcoded :True/:False (Task 6) — the Task 10 antibody enforces this.
```

> **Implementer note:** fill `bool_family/0`, `bool_ctors/0`, `nat_family/0`, `nat_ctors/0` with the concrete maps matching `Inductive.declare/3`'s contract. `Nat`'s `S` constructor's single field must reference the `Nat` family exactly as the real declaration path encodes a recursive argument (mirror what the prelude compile produces for `type Nat = Z | S(Nat)` — Task 4 asserts they match, so build this to that target).

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/core/builtins_seed_test.exs`
Expected: PASS (2 tests).

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/core/builtins.ex test/cure/core/builtins_seed_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(core): Builtins.seed/1 seeds canonical Bool+Nat (validated)"
```

---

### Task 4: Parser — attach `@builtin(:key)` to a `type` declaration; wire prelude registration

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (`parse_at/1` at 4159-4210, `attach_decorator/3` at 4212-4253)
- Modify: `lib/std/nat.cure` (tag with `@builtin(:nat)`, ensure it is in the `:core` group and ordered first — see Task 11 for load-order)
- Create: `lib/std/bool.cure` (`@builtin(:bool) type Bool = False | True`)
- Modify: the prelude-elaboration path that honors decorators on type declarations — `lib/cure/elab/program.ex` register pass (lines 278-313) — to call `Builtins.validate!/3` + `Inductive.register_builtin/3` when it processes a `@builtin`-tagged type **only for designated prelude sources**.
- Test: `test/cure/compiler/builtin_decorator_parse_test.exs` (create); `test/cure/elab/builtin_prelude_seed_test.exs` (create)

**Interfaces:**
- Consumes: `Builtins.validate!/3`, `Inductive.register_builtin/3`, `Builtins.seed/1` (for the equivalence assertion).
- Produces: type-declaration AST nodes carry `[decorator: {:builtin, [<key-atom>]}]` in their meta; the prelude register pass turns that into a validated builtin registration.

- [ ] **Step 1: Write the failing parse test**

```elixir
# test/cure/compiler/builtin_decorator_parse_test.exs
defmodule Cure.Compiler.BuiltinDecoratorParseTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Parser

  test "@builtin(:bool) attaches to the following type declaration" do
    src = "mod M\n  @builtin(:bool)\n  type Bool = False | True\n"
    {:ok, ast} = Parser.parse(src)   # confirm the real entry fn/return shape
    type_node = find_type_decl(ast, :Bool)
    assert {:builtin, [:bool]} = get_in_meta(type_node, :decorator)
  end
end
```

> **Implementer note:** replace `Parser.parse/1`, `find_type_decl/2`, and `get_in_meta/2` with the real parser entry point and AST-walk helpers (check an existing `test/cure/compiler/*_test.exs` for how type declarations are located in the parsed AST and how decorator meta is read). The assertion — a `type` node carries the `:builtin` decorator with the key — is the fixed contract.

- [ ] **Step 2: Run parse test to verify it fails**

Run: `mix test test/cure/compiler/builtin_decorator_parse_test.exs`
Expected: FAIL — decorator parses as a disconnected `{:decorator, …}` standalone node; the `type` node has no `:decorator` meta.

- [ ] **Step 3: Extend decorator attachment to `type`**

In `parse_at/1` (parser.ex ~line 4186), add a `:type` case alongside the `:fn`/`:local`/`:rec` cases:

```elixir
    %Token{type: :keyword, value: kw} when kw in [:fn, :local] ->
      {fn_ast, state} = parse_expr(state, 0)
      fn_ast = attach_decorator(fn_ast, dec_name, args)
      {fn_ast, state}

    %Token{type: :keyword, value: :type} ->
      {type_ast, state} = parse_type_def(state)
      type_ast = attach_decorator(type_ast, dec_name, args)
      {type_ast, state}

    %Token{type: :keyword, value: :rec} ->
      ...
```

In `attach_decorator/3`, add a clause for the type-declaration AST node shape (confirm the tag `parse_type_def/1` returns — e.g. `{:type_def, meta, body}`):

```elixir
    {:type_def, meta, body} ->
      {:type_def, meta ++ [decorator: {String.to_atom(dec_name), args}], body}
```

> **Implementer note:** verify `parse_type_def/1`'s return tuple tag and meta position (parser.ex:2542) and match it exactly. `args` for `@builtin(:bool)` is the parsed call-arg list; confirm the key arrives as an atom `:bool` (from the `%[...]`/atom literal path) and normalize to `{:builtin, [:bool]}` if the raw arg is wrapped (e.g. `{:literal, _, :bool}`).

- [ ] **Step 4: Run parse test to verify it passes**

Run: `mix test test/cure/compiler/builtin_decorator_parse_test.exs`
Expected: PASS.

- [ ] **Step 5: Add the prelude sources and the register-pass wiring, with a failing seed test**

Create `lib/std/bool.cure`:

```cure
mod Std.Bool
  fn __group__() -> Atom = :core
  @builtin(:bool)
  type Bool = False | True
```

Tag `lib/std/nat.cure`'s existing declaration:

```cure
mod Std.Nat
  fn __group__() -> Atom = :core
  @builtin(:nat)
  type Nat = Z | S(Nat)
```

Write the failing test that the prelude compile yields a registered, schema-identical `:bool`:

```elixir
# test/cure/elab/builtin_prelude_seed_test.exs
defmodule Cure.Elab.BuiltinPreludeSeedTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Builtins}

  test "compiling a program that imports Std.Bool registers :bool" do
    src = "mod M\n  fn id(b: Bool) -> Bool = b\n"
    {:ok, env} = Cure.Elab.Program.elaborate(src)   # confirm real entry
    assert Inductive.builtin(env, :bool) == :Bool
  end

  test "prelude-compiled Bool family equals Builtins.seed's" do
    src = "mod M\n  fn id(b: Bool) -> Bool = b\n"
    {:ok, env} = Cure.Elab.Program.elaborate(src)
    seeded = Builtins.seed(Env.empty())
    from_prelude = env |> Inductive.ctors_of(:Bool) |> Enum.map(& &1.name) |> Enum.sort()
    from_seed = seeded |> Inductive.ctors_of(:Bool) |> Enum.map(& &1.name) |> Enum.sort()
    assert from_prelude == from_seed
  end
end
```

- [ ] **Step 6: Run seed test to verify it fails**

Run: `mix test test/cure/elab/builtin_prelude_seed_test.exs`
Expected: FAIL — register pass ignores the `:builtin` decorator; `:bool` unregistered (also `Bool` may still be resolving as the primitive — that is fine for this task; the assertion is on the registry entry).

- [ ] **Step 7: Wire the register pass**

In `lib/cure/elab/program.ex`'s register pass (lines 278-313), when a type declaration carries `[decorator: {:builtin, [key]}]` AND the current source is a designated prelude source, after the family is declared into the env call:

```elixir
:ok = Cure.Core.Builtins.validate!(env, key, family_id)
env = Cure.Core.Inductive.register_builtin(env, key, family_id)
```

Gate this on prelude-source identity: the register pass must know whether the module being processed is a privileged prelude source (spec §1 single-registration invariant part (1)). Reuse the existing prelude/stdlib-source distinction (`lib/cure/stdlib/preload.ex` knows the stdlib source set); a `@builtin` decorator on a **non-prelude** module is ignored for registration and produces a diagnostic (a `@builtin` in user code is not honored). `register_builtin/3`'s own hard-error on a duplicate key (Task 1) is the second half of the invariant.

> **Implementer note:** determine `family_id` (the declared family's name) at the point the register pass has the type declaration in hand. If the register pass doesn't currently thread the decorator meta, add it. Keep the change minimal and localized to the register pass.

- [ ] **Step 8: Run seed test to verify it passes**

Run: `mix test test/cure/elab/builtin_prelude_seed_test.exs`
Expected: PASS (2 tests).

- [ ] **Step 9: Commit**

```bash
git add -- lib/cure/compiler/parser.ex lib/std/bool.cure lib/std/nat.cure lib/cure/elab/program.ex test/cure/compiler/builtin_decorator_parse_test.exs test/cure/elab/builtin_prelude_seed_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(parser,elab): @builtin(:key) on type decls; prelude registers validated Bool/Nat"
```

---

### Task 5: `infer_prim` returns the inductive `Bool` type

**Files:**
- Modify: `lib/cure/core/kernel.ex` (`infer_prim` at 1041-1071; the `{:bool_lit}`/`{:bool_type}` clauses at 60-61 stay for now — deleted in Task 9; the `:and`/`:or`/`:not` operand checks at 1055-1071)
- Test: `test/cure/core/prim_bool_inductive_test.exs` (create); update `test/cure/core/bool_prim_test.exs` (sanctioned migration edit)

**Interfaces:**
- Consumes: `Inductive.builtin(sig, :bool)`, `Context.signature/1` (kernel already threads `ctx → sig`), the seeded env from `Builtins.seed/1`.
- Produces: comparison/connective `{:prim, op, args}` now infer to the **type value denoting the `Bool` inductive** — the same value the kernel produces for an applied nullary-index inductive family, i.e. `Eval.eval({:global-or-family-ref to Bool}, env)` reified as a value type. Concretely define one helper `bool_type_value(sig)` and use it uniformly.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/core/prim_bool_inductive_test.exs
defmodule Cure.Core.PrimBoolInductiveTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Env, Inductive, Kernel}

  setup do
    %{ctx: Context.with_signature(Context.empty(), Builtins.seed(Env.empty()))}
  end

  test "a comparison infers to the Bool inductive, not {:vbool_type}", %{ctx: ctx} do
    {:ok, ty} = Kernel.infer(ctx, {:prim, :lt, [{:int_lit, 3}, {:int_lit, 5}]})
    refute ty == {:vbool_type}
    assert bool_inductive_type?(ty, ctx)   # helper asserts ty denotes family :Bool
  end
end
```

> **Implementer note:** `Context.with_signature/2` (or whatever installs a sig on a context — confirm the real constructor; `Context.signature/1` is the getter per the Explore report) and `bool_inductive_type?/2` must be written against the real value representation of an applied inductive family. Dump `Kernel.infer(ctx, {:ctor, :True, []})`'s type (once Bool is seeded) to learn the exact type-value shape, and assert `ty` equals it. This is the single most important shape to get right — the whole migration pivots on `infer_prim` and `{:ctor}` agreeing on the `Bool` type value.

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/prim_bool_inductive_test.exs`
Expected: FAIL — `infer_prim` still returns `{:vbool_type}`.

- [ ] **Step 3: Rewire `infer_prim`**

Add a private helper and replace the three `{:ok, {:vbool_type}}` results (comparisons, connectives, `:not`) and the connective/`:not` operand checks:

```elixir
defp bool_type_value(sig) do
  fid = Inductive.builtin(sig, :bool) || raise "builtin :bool not seeded (bootstrap/load-order bug)"
  # Build the value denoting the applied nullary-index family `fid`.
  # Mirror exactly how the kernel represents an inductive family's type value.
  build_family_type_value(sig, fid)
end
```

- Comparisons (`op in [:lt,:le,:gt,:ge]`): `{:ok, bool_type_value(Context.signature(ctx))}`.
- Connectives (`op in [:and,:or]`) and `:not`: replace `check(ctx, a, {:vbool_type})` with `check(ctx, a, bool_type_value(Context.signature(ctx)))`, and return `bool_type_value(...)`.

> **Implementer note:** `build_family_type_value/2` must produce precisely the type value `{:ctor, :True, []}` and `{:ctor, :False, []}` check against — reuse the kernel's own family→type-value construction (the code path `infer` uses for `{:ctor, …}`'s result type, or for a family reference). Do not invent a new shape.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/core/prim_bool_inductive_test.exs`
Expected: PASS.

- [ ] **Step 5: Migrate the old primitive-Bool assertions**

Update `test/cure/core/bool_prim_test.exs`'s `{:vbool_type}` expectations to the inductive `Bool` type value (sanctioned migration edit — the represented behavior intentionally changed). Keep the eval-fold assertions for Task 6.

Run: `mix test test/cure/core/bool_prim_test.exs`
Expected: the *typing* assertions PASS against the new value; eval-fold assertions may still expect `{:vbool, _}` (fixed in Task 6) — if the test file mixes both, split the eval-fold assertions into a `@tag :phase1_task6` skip or move them, and note it in the commit. Do NOT weaken the eval assertion to pass; migrate it in Task 6.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/core/kernel.ex test/cure/core/prim_bool_inductive_test.exs test/cure/core/bool_prim_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(core): infer_prim yields inductive Bool type (via builtin registry)"
```

---

### Task 6: `eval` `fold/2` produces `True`/`False` constructor values

**Files:**
- Modify: `lib/cure/core/eval.ex` (`fold/2` at 127-161, `prim/2` at 120-125)
- Test: `test/cure/core/prim_bool_eval_test.exs` (create); finish migrating `test/cure/core/bool_prim_test.exs`

**Interfaces:**
- Consumes: nothing new (design decision: `fold/2` **hardcodes** `:True`/`:False` — it has no `sig` on its path; spec §2 plumbing decision).
- Produces: bool-producing `fold/2` clauses return the constructor **value** for `True`/`False` (the value form `{:ctor, :True, []}` produces after `eval`; confirm the exact value tag — likely `{:vctor, :True, []}` or reuse how `eval({:ctor, …}, env)` evaluates). Define one helper `vbool(bool)` returning the right constructor value.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/core/prim_bool_eval_test.exs
defmodule Cure.Core.PrimBoolEvalTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Eval

  test "eval folds a comparison to the True constructor value" do
    v = Eval.eval({:prim, :lt, [{:int_lit, 3}, {:int_lit, 5}]}, [])
    assert v == Eval.eval({:ctor, :True, []}, [])
    refute v == {:vbool, true}
  end

  test "eval folds a false comparison to the False constructor value" do
    v = Eval.eval({:prim, :lt, [{:int_lit, 5}, {:int_lit, 3}]}, [])
    assert v == Eval.eval({:ctor, :False, []}, [])
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/prim_bool_eval_test.exs`
Expected: FAIL — `fold/2` still returns `{:vbool, true/false}`.

- [ ] **Step 3: Rewire `fold/2`**

Add the helper and update every bool-producing `fold` clause (comparisons `:eq/:ne/:lt/:le/:gt/:ge`, connectives `:and/:or`, `:not`):

```elixir
# Single source of truth with Builtins @schemas and seed/1. If those ctor
# names ever change, the Task 10 antibody fails — do not desync.
defp vbool(true), do: eval({:ctor, :True, []}, [])
defp vbool(false), do: eval({:ctor, :False, []}, [])

defp fold(:and, [a, b]), do: with {:ok, x} <- as_bool(a), {:ok, y} <- as_bool(b), do: {:ok, vbool(x and y)}
defp fold(:or,  [a, b]), do: with {:ok, x} <- as_bool(a), {:ok, y} <- as_bool(b), do: {:ok, vbool(x or y)}
defp fold(:not, [a]),    do: with {:ok, x} <- as_bool(a), do: {:ok, vbool(not x)}
defp fold(:eq, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a == b)}
defp fold(:lt, [{:vint, a}, {:vint, b}]), do: {:ok, vbool(a < b)}
# ...same for :ne,:le,:gt,:ge and any float/other numeric clauses that currently produce {:vbool, _}
```

`as_bool/1` maps a `True`/`False` constructor value back to an Elixir boolean for the connectives (the operands are now constructor values, not `{:vbool, _}`):

```elixir
defp as_bool(v) do
  cond do
    v == vbool(true) -> {:ok, true}
    v == vbool(false) -> {:ok, false}
    true -> :stuck
  end
end
```

> **Implementer note:** if any connective operand is a neutral (non-`True`/`False`) value, `as_bool` returns `:stuck` and `prim/2`'s existing `:stuck → neutral` path must handle it — verify `fold` returning `:stuck` (not a bad `with`) flows to the neutral case. Confirm the exact evaluated constructor-value tag by dumping `Eval.eval({:ctor, :True, []}, [])` and hardcode against it if `eval/2` recursion inside `fold` is undesirable on a hot path (a module attribute computed once is fine since it's a closed constant).

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/core/prim_bool_eval_test.exs`
Expected: PASS.

- [ ] **Step 5: Finish migrating `bool_prim_test.exs`**

Update the eval-fold assertions (`{:vbool, true}` → the `True` constructor value) and remove any temporary skip added in Task 5.

Run: `mix test test/cure/core/bool_prim_test.exs`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/core/eval.ex test/cure/core/prim_bool_eval_test.exs test/cure/core/bool_prim_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(core): eval fold produces True/False constructor values (hardcoded, single-source)"
```

---

### Task 7: Surface `true`/`false` literals elaborate to `True`/`False` constructors

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` (bool-literal clause at 307-314)
- Test: `test/cure/elab/bool_literal_ctor_test.exs` (create)

**Interfaces:**
- Consumes: the elaborator's constructor-elaboration path; `Inductive.builtin(sig, :bool)`.
- Produces: `{:literal, [subtype: :boolean], true}` elaborates to `{:ctor, :True, []}` typed at the inductive `Bool`; `false` → `{:ctor, :False, []}`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/bool_literal_ctor_test.exs
defmodule Cure.Elab.BoolLiteralCtorTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "a true literal in a Bool-returning fn elaborates and runs as the True atom" do
    src = "mod M\n  fn t() -> Bool = true\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Cure.Elab.Emit.compile_and_load(env, module: :"Cure.BoolLit1", functions: [:t])
    assert apply(mod, :t, []) == true   # erases to lowercase atom (Task 10)
  end
end
```

> **Implementer note:** until Task 10 lands the erasure rule, `apply(mod, :t, [])` may yield the atom `:True` rather than `true`. If so, split this into (a) an elaboration-shape assertion now (`elaborate` produces `{:ctor, :True, []}` for the body — assert on the core term via the elaborator's typed entry) and (b) the runtime-`true` assertion moved to Task 10. Prefer the core-term assertion here so this task is independently green.

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/bool_literal_ctor_test.exs`
Expected: FAIL — literal still elaborates to `{:bool_lit, true}`.

- [ ] **Step 3: Rewire the literal clause**

Replace the `:boolean` case in `elaborate_expr_typed({:literal, meta, value}, …)` (elaborator.ex:307-314):

```elixir
    :boolean when is_boolean(value) ->
      ctor = if value, do: :True, else: :False
      elaborate_ctor_reference(ctor, _names, _ctx, _env)   # reuse existing ctor elaboration
```

> **Implementer note:** reuse whatever path the elaborator already uses to elaborate a nullary constructor application `True()`/`False()` so the produced term and inferred type match `{:ctor}` typing exactly (don't hand-build the type). If there is no direct helper, produce `{:ctor, ctor, []}` and infer its type via the same `Kernel.infer` the ctor path uses.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/elab/bool_literal_ctor_test.exs`
Expected: PASS (per the note, the elaboration-shape assertion).

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/elaborator.ex test/cure/elab/bool_literal_ctor_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): true/false literals elaborate to True/False constructors"
```

---

### Task 8: Retarget `if` / guards / literal-patterns from `bool_elim` to `:case` on `Bool`

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` — conditional infer (316-327), conditional check (604-611), `guard_chain` (1890-1909), `try_literal_match` bool branch (1949-1974), `literal_chain` (2028-2037)
- Test: existing `test/cure/elab/conditional_test.exs`, `test/cure/elab/guard_test.exs`, and the literal-pattern test from commit `ebc6a88` should stay green after the retarget (they assert runtime behavior, not the `bool_elim` term); add `test/cure/elab/if_lowers_to_case_test.exs` asserting the new core term is `:case`.

**Interfaces:**
- Consumes: the kernel's `:case` elaboration (coverage/motive/branch conversion for a 2-constructor family — already supported), `Inductive.builtin(sig, :bool)`.
- Produces: each of the five sites emits `{:case, scrut, motive, [{:True, 0, tt}, {:False, 0, ff}]}` (confirm the `:case` branch tuple shape from `erase.ex`'s `{:case, s, m, branches}` handling and the kernel's `:case` inference) instead of `{:bool_elim, scrut, motive, tt, ff}`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/if_lowers_to_case_test.exs
defmodule Cure.Elab.IfLowersToCaseTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "if on a Bool lowers to a :case core term, not bool_elim" do
    src = "mod M\n  type N = Z | S(N)\n  fn f(b: Bool) -> N = if b then S(Z()) else Z()\n"
    {:ok, env} = Program.elaborate(src)
    body = core_body_of(env, :f)          # helper: fetch f's elaborated core term
    assert match?({:case, _, _, _}, strip_to_head(body))
    refute has_bool_elim?(body)
  end
end
```

> **Implementer note:** `core_body_of/2`, `strip_to_head/1`, `has_bool_elim?/1` walk the elaborated env's def for `:f`. Confirm how to fetch a function's core body from the elaborated `Env` (`Env.get_def/2` per Explore report) and its term shape.

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/if_lowers_to_case_test.exs`
Expected: FAIL — body is still `{:bool_elim, …}`.

- [ ] **Step 3: Retarget all five sites**

For each site, replace the `{:bool_elim, scrut, motive, tt, ff}` construction with a `:case` on `Bool`. The motive is unchanged in intent but its binder type changes from `{:bool_type}` to the `Bool` inductive type term. Introduce ONE helper in the elaborator:

```elixir
defp bool_case(scrut_term, motive_body_type, tt, ff, ctx) do
  bool_ty = bool_type_term(Context.signature(ctx))     # core Term for the Bool inductive
  motive = {:lam, bool_ty, Cure.Core.Term.shift(motive_body_type, 1, 0)}
  {:case, scrut_term, motive, [{:True, 0, tt}, {:False, 0, ff}]}
end
```

- Conditional infer (316-327): `motive` used `{:lam, {:bool_type}, shift(t_type_core,1,0)}` → `bool_case(c_core, t_type_core, t_core, e_core, ctx)`.
- Conditional check (604-611): `bool_case(c_core, expected_core, t_core, e_core, ctx)`.
- `guard_chain` (1890-1909): the `{:bool_elim, test, motive, tt, ff}` → `bool_case(test, expected, tt, ff, ctx)`.
- `try_literal_match` bool branch (1961): `{:bool_elim, scrut_term, motive, t_core, f_core}` → `bool_case(scrut_term, expected, t_core, f_core, ctx)`.
- `literal_chain` (2035): `{:bool_elim, test, motive, body_core, rest_core}` → `bool_case(test, expected, body_core, rest_core, ctx)` (the `test = {:prim, :eq, …}` line is unchanged — it now yields the inductive `Bool` which `:case` scrutinises).

> **Implementer note:** confirm `:case`'s branch ordering/exhaustiveness expectation (does the kernel require branches in family-declaration order? include both constructors?). The 2-constructor `Bool` `:case` must satisfy the kernel's existing coverage check. `bool_type_term/1` is the **core Term** (not value) for the Bool inductive — mirror how a `type Bool` reference is represented as a term in an elaborated program.

- [ ] **Step 4: Run tests to verify they pass**

Run: `mix test test/cure/elab/if_lowers_to_case_test.exs test/cure/elab/conditional_test.exs test/cure/elab/guard_test.exs`
Expected: PASS — new term is `:case`; the pre-existing behavioral tests still pass (runtime results unchanged).

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/elaborator.ex test/cure/elab/if_lowers_to_case_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): retarget if/guards/literal-patterns to :case on inductive Bool"
```

---

### Task 9: Retire `bool_elim` / `bool_type` / `bool_lit` across the nine core modules

**Files (delete the now-dead clauses):**
- Modify: `lib/cure/core/term.ex` (25, 34, 73, 87-88, 114-115, 136-137, 195-196, 224-225, 286-288, 315-316, 356-357, 374-375)
- Modify: `lib/cure/core/value.ex` (54, 72)
- Modify: `lib/cure/core/eval.ex` (49-50, 84-96)
- Modify: `lib/cure/core/quote.ex` (55-56, 76-77)
- Modify: `lib/cure/core/conv.ex` (76-77, 160, 206-207)
- Modify: `lib/cure/core/normalise.ex` (186-187, 242, 245, 247-248)
- Modify: `lib/cure/core/kernel.ex` (60-61, 253-265, 676 `infer_type_value_sort` `:vbool_type`)
- Modify: `lib/cure/core/certificate.ex` (164, 166, 254, 256)
- Modify: `lib/cure/core/serialize.ex` (38, 41, 148, 151-152 — the `(bool-type)`/`(bool <atom>)` S-expr grammar)
- Test: grep-guard test `test/cure/core/no_bool_primitive_test.exs` (create)

**Interfaces:**
- Consumes: nothing — this is pure deletion of code no longer reachable after Tasks 5–8.
- Produces: the `{:bool_type}`/`{:bool_lit}`/`{:bool_elim}`/`{:vbool}`/`{:vbool_type}`/`{:nbool_elim}` term/value forms no longer exist anywhere in `lib/cure/core`.

- [ ] **Step 1: Write the failing guard test**

```elixir
# test/cure/core/no_bool_primitive_test.exs
defmodule Cure.Core.NoBoolPrimitiveTest do
  use ExUnit.Case, async: true

  @core_files Path.wildcard("lib/cure/core/*.ex")

  test "no core module references the retired primitive Bool forms" do
    offenders =
      for f <- @core_files,
          src = File.read!(f),
          tok <- ~w(:bool_elim :bool_type :bool_lit :vbool :vbool_type :nbool_elim),
          String.contains?(src, tok),
          do: {Path.basename(f), tok}
    assert offenders == [], "still present: #{inspect(offenders)}"
  end
end
```

- [ ] **Step 2: Run guard test to verify it fails**

Run: `mix test test/cure/core/no_bool_primitive_test.exs`
Expected: FAIL — the tokens are still present in the nine modules.

- [ ] **Step 3: Delete the clauses module by module**

Remove each `:bool_type`/`:bool_lit`/`:bool_elim`/`:vbool`/`:vbool_type`/`:nbool_elim` clause/branch at the lines listed above. After each module, run that module's own test file (`mix test test/cure/core/<module>_test.exs` if present) to catch a broken deletion early. The deletion is mechanical BUT: the compiler will now reject any remaining producer — if compilation fails with "no clause matching `{:bool_elim, …}`", a producer was missed in Tasks 5–8; fix the producer, do not re-add the clause.

> **Implementer note (`certificate.ex`, SOUNDNESS):** the `bool_elim` totality/guardedness clauses (164, 166, 254, 256) must be removed such that `:case` on `Bool` is covered by the general `:case` totality path — verify the general `:case` guardedness/coverage handling already treats a 2-constructor `Bool` `:case` correctly (it must, since other inductives use it). If the certificate path had `bool_elim`-specific structural-recursion accounting, confirm the `:case` path subsumes it. This is the single most soundness-sensitive deletion — do not rush it; the Task 10 antibody + Task 12 adversarial review target exactly this.

- [ ] **Step 4: Run guard test + core suite to verify green**

Run: `mix test test/cure/core/no_bool_primitive_test.exs && mix test test/cure/core/`
Expected: PASS — no tokens remain; all core tests green.

- [ ] **Step 5: Update the conformance fixture**

Rewrite the affected lines of `test/fixtures/core_conformance.txt` to the inductive grammar:
- Line 8 `accept | (bool true) | (bool-type)` → the `True` constructor S-expr typed at the `Bool` family (use serialize.ex's new constructor grammar).
- Line 10 `accept | (bool-type) | (type 0)` → the `Bool` family reference typed at `(type 0)`.
- Line 15 `accept | (prim lt (int 3) (int 5)) | (bool-type)` → `... | <Bool family type S-expr>`.
- Line 16 `accept | (prim not (bool true)) | (bool-type)` → operand becomes the `True` constructor; result the `Bool` family type.
- Lines 24-25 (`reject` cases) — keep rejecting; update operand grammar (`(bool true)` → constructor S-expr) so the reason is unchanged (bool-not-numeric; and-needs-bool-operands).

The conformance harness base env must be `Builtins.seed(Env.empty())` (design decision 1) so `Bool` resolves. Update the harness's context construction accordingly.

> **Implementer note:** find the conformance harness (the test that reads `core_conformance.txt` — search `test/` for `core_conformance`) and confirm where it builds the checking context; inject the seeded env there.

- [ ] **Step 6: Run the conformance test to verify green**

Run: `mix test <the core_conformance test file>`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add -- lib/cure/core/term.ex lib/cure/core/value.ex lib/cure/core/eval.ex lib/cure/core/quote.ex lib/cure/core/conv.ex lib/cure/core/normalise.ex lib/cure/core/kernel.ex lib/cure/core/certificate.ex lib/cure/core/serialize.ex test/cure/core/no_bool_primitive_test.exs test/fixtures/core_conformance.txt <harness file>
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "refactor(core): retire bool_elim/bool_type/bool_lit; Bool is inductive (9 modules + conformance)"
```

---

### Task 10: Erasure — `False`/`True` lower to native `false`/`true` atoms; the drift antibody

**Files:**
- Modify: `lib/cure/elab/emit.ex` (constructor lowering at 139-143) OR `lib/cure/elab/erase.ex` (constructor erase at 20-30) — whichever is the single lowering chokepoint; prefer `emit.ex` since it produces the BEAM atom.
- Test: `test/cure/elab/bool_erasure_test.exs` (create); complete Task 7's runtime assertion; `test/antigen/builtin_bool_drift_test.exs` (create — the single-source-of-truth antibody)

**Interfaces:**
- Consumes: `Inductive.builtin(env, :bool)` to identify that a `{:ctor, name, []}` belongs to the `Bool` family.
- Produces: `{:ctor, :True, []}` lowers to the BEAM atom `true`; `{:ctor, :False, []}` to `false`; a `:case` on `Bool` scrutinises those lowercase atoms — matching what `{:prim}` comparisons already return at runtime.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/bool_erasure_test.exs
defmodule Cure.Elab.BoolErasureTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  test "True/False constructors run as lowercase BEAM booleans" do
    src = "mod M\n  fn t() -> Bool = true\n  fn f() -> Bool = false\n  fn c(b: Bool) -> Bool = if b then false else true\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.BoolErase1", functions: [:t, :f, :c])
    assert apply(mod, :t, []) == true
    assert apply(mod, :f, []) == false
    assert apply(mod, :c, [true]) == false
    assert apply(mod, :c, [false]) == true
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/bool_erasure_test.exs`
Expected: FAIL — constructors lower to atoms `:True`/`:False`, so `apply(mod, :t, [])` is `:True`, not `true`.

- [ ] **Step 3: Add the Bool-family lowering rule**

In `emit.ex`'s `lower/3` constructor clause, special-case the `Bool` family's nullary constructors to lowercase atoms:

```elixir
defp lower(env, {:ctor, name, args}, ctx) do
  cond do
    args == [] and Inductive.builtin(env, :bool) == Inductive.ctor_family(env, name) ->
      {:atom, @line, bool_atom(name)}     # :True -> true, :False -> false
    true ->
      case Enum.map(args, &lower(env, &1, ctx)) do
        [] -> {:atom, @line, name}
        forms -> {:tuple, @line, [{:atom, @line, name} | forms]}
      end
  end
end

defp bool_atom(:True), do: true
defp bool_atom(:False), do: false
```

The `:case` on `Bool` already lowers its branches keyed by constructor name; ensure the branch match patterns for a `Bool` `:case` use the lowercase atoms too (find the `:case` lowering in `emit.ex` and apply the same `bool_atom/1` mapping to the `Bool`-family branch patterns).

> **Implementer note:** `emit.ex` must have `env` in scope at `lower/3` (it takes `env` per the Explore report). Confirm `Inductive.ctor_family/2` returns the family-id for a ctor name. The `:case`-branch lowering site needs the same treatment — otherwise construction erases to `true`/`false` but the match still tests `:True`/`:False` and never fires. Test `c/1` above is the guard for that.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/elab/bool_erasure_test.exs`
Expected: PASS. Also re-run Task 7's `test/cure/elab/bool_literal_ctor_test.exs` and complete its runtime `== true` assertion.

- [ ] **Step 5: Write the drift antibody**

```elixir
# test/antigen/builtin_bool_drift_test.exs
defmodule Antigen.BuiltinBoolDriftTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Env, Eval}

  test "fold's hardcoded True/False agree with the seeded :bool schema names" do
    # Task 6 hardcodes :True/:False in eval; Task 2/3 seed the schema. They must not drift.
    names = Builtins.schema(:bool) |> Enum.map(&elem(&1, 0)) |> Enum.sort()
    assert names == [:False, :True]
    # fold's true-value must be the True constructor value.
    assert Eval.eval({:prim, :lt, [{:int_lit, 1}, {:int_lit, 2}]}, []) == Eval.eval({:ctor, :True, []}, [])
  end
end
```

- [ ] **Step 6: Run the antibody to verify it passes**

Run: `mix test test/antigen/builtin_bool_drift_test.exs`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add -- lib/cure/elab/emit.ex test/cure/elab/bool_erasure_test.exs test/cure/elab/bool_literal_ctor_test.exs test/antigen/builtin_bool_drift_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(erase): Bool constructors lower to native false/true atoms; drift antibody"
```

---

### Task 11: Load-order guarantee — Bool/Nat seed before any `:core` `{:prim}` consumer

**Files:**
- Modify: `lib/cure/stdlib/preload.ex` (grouping/ordering, lines 27-123) and/or `lib/cure/elab/program.ex` (register-pass ordering)
- Test: `test/cure/elab/builtin_load_order_test.exs` (create)

**Interfaces:**
- Consumes: the `:core` group ordering machinery.
- Produces: `Std.Bool` and `Std.Nat` are registered before any other `:core` module whose elaboration uses `{:prim}` comparisons (`Std.Eq`, `Std.Core`) or `Nat` arithmetic. A `{:prim}` reached without `:bool` seeded raises the explicit bootstrap error from Task 5's `bool_type_value/1`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/builtin_load_order_test.exs
defmodule Cure.Elab.BuiltinLoadOrderTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Inductive

  test "a program importing Std.Eq (which uses comparisons) compiles with :bool seeded" do
    src = "mod M\n  fn use_eq(a: Int, b: Int) -> Bool = a == b\n"
    assert {:ok, env} = Cure.Elab.Program.elaborate(src)
    assert Inductive.builtin(env, :bool) == :Bool
  end
end
```

> **Implementer note:** pick a source that transitively forces `Std.Eq`/`Std.Core` to elaborate their comparison `{:prim}` ops during the same compile, so a wrong order actually raises. If `elaborate/1` already lazily orders correctly, this test passes immediately — that is an acceptable outcome; keep it as a regression guard and note in the commit that ordering was already correct. If it fails with the bootstrap `raise`, implement the ordering fix below.

- [ ] **Step 2: Run test to verify it fails (or confirm already-correct)**

Run: `mix test test/cure/elab/builtin_load_order_test.exs`
Expected: FAIL with the bootstrap `raise` from `bool_type_value/1` IF ordering is wrong; PASS if the existing order already seeds first.

- [ ] **Step 3: Pin Bool/Nat first in the `:core` group (only if Step 2 failed)**

In `preload.ex` (or the register-pass ordering in `program.ex`), ensure `Std.Bool` and `Std.Nat` sort before other `:core` members. Implement a stable sub-ordering within `:core` that puts the two `@builtin` modules first (e.g. a small explicit priority list consulted before the alphabetical/discovery order).

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/elab/builtin_load_order_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/stdlib/preload.ex lib/cure/elab/program.ex test/cure/elab/builtin_load_order_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): pin Bool/Nat @builtin seed before :core prim consumers (load-order guarantee)"
```

---

### Task 12: PHASE 1 GATE — Antigen antibodies + full Antigen + full suite + oracle + adversarial review + HUMAN HARD-STOP

**Files:**
- Create: `test/antigen/builtin_bool_migration_test.exs` (the migration-soundness antibody)
- Verify only (no new production code): full suite, full Antigen, oracle replay.

**This task does not merge. It produces the evidence package for the human TCB review and STOPS.**

- [ ] **Step 1: Write the migration-soundness antibody**

An antibody asserting the `bool_elim → :case` migration preserves normal forms and termination certification, and that a malformed/duplicate `@builtin` binding is rejected:

```elixir
# test/antigen/builtin_bool_migration_test.exs
defmodule Antigen.BuiltinBoolMigrationTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Env, Inductive, Eval}

  test "case-on-Bool normal forms match the intended branch semantics" do
    # if-true reduces to the then-branch; if-false to the else-branch — via :case, not bool_elim.
    t = Eval.eval({:ctor, :True, []}, [])
    f = Eval.eval({:ctor, :False, []}, [])
    refute t == f
  end

  test "a name-mismatched @builtin(:bool) binding is rejected (Coin as Bool)" do
    env =
      Inductive.declare(Env.empty(), %{name: :Coin, params: [], indices: []},
        [%{name: :Heads, family: :Coin, args: []}, %{name: :Tails, family: :Coin, args: []}])
    assert_raise ArgumentError, fn -> Builtins.validate!(env, :bool, :Coin) end
  end

  test "a second :bool registration is a hard error, not a silent rebind" do
    env = Builtins.seed(Env.empty())
    assert_raise ArgumentError, fn -> Inductive.register_builtin(env, :bool, :OtherBool) end
  end
end
```

Run: `mix test test/antigen/builtin_bool_migration_test.exs`
Expected: PASS.

- [ ] **Step 2: Run the full Antigen suite (alone)**

Run: `mix test test/antigen/`
Expected: PASS — no soundness antibody regressed.

- [ ] **Step 3: Run the oracle replay + relevant clusters (alone)**

Run: `mix test test/oracle_replay_test.exs`
Then re-run the behavior-preservation clusters and confirm accept/accept unchanged:
Run: `mix cure.oracle cond && mix cure.oracle guard && mix cure.oracle match`
Expected: verdicts unchanged (accept/accept `same`); no cluster regresses.

- [ ] **Step 4: Run the FULL suite ONCE, alone**

Run: `mix test`
Expected: PASS (baseline before this run was 2548 passing; expect that plus the new tests, minus none).

- [ ] **Step 5: Dispatch an independent adversarial review subagent**

Dispatch ONE subagent (general-purpose, Sonnet) to adversarially verify the Phase 1 diff (`git diff main...HEAD -- lib/cure/core lib/cure/elab lib/cure/compiler`), specifically probing: (a) can any term still reach a deleted `bool_elim` clause and crash or mis-check; (b) does `:case`-on-`Bool` totality/coverage in `certificate.ex` genuinely subsume what `bool_elim` accounted for (no non-total term now certified total); (c) can a `{:prim}` be reached with `:bool` unseeded to produce a wrong type silently instead of the intended `raise`; (d) does `fold/2`'s hardcoded `:True`/`:False` ever disagree with the schema. Require exact file:line evidence for each.

- [ ] **Step 6: Assemble the evidence package and HARD-STOP for human review**

Write `docs/superpowers/plans/PHASE1-GATE-EVIDENCE.md` summarizing: the per-task commits, red→green evidence, the antibody results, full-Antigen + full-suite + oracle results, and the adversarial reviewer's findings + resolutions. Then **STOP** — do NOT merge, do NOT proceed to Phase 2. Notify the operator: Phase 1 (TCB) is ready for review with the evidence package.

---

## Phase 2 — Nat → Int runtime erasure (untrusted, ungated but full-suite verified)

Phase 2 begins ONLY after the human approves Phase 1. It touches no kernel code. The `:nat` schema + `@builtin(:nat)` binding already landed in Phase 1 (Task 3/4), so Phase 2 is purely erase/emit consumption of an already-validated binding (spec §Phasing ownership clarification).

---

### Task 13: Erase `Z`/`S` to native integers (construction)

**Files:**
- Modify: `lib/cure/elab/emit.ex` (constructor lowering — extend the Task 10 `cond` with a `:nat` family arm)
- Test: `test/cure/elab/nat_erasure_construction_test.exs` (create)

**Interfaces:**
- Consumes: `Inductive.builtin(env, :nat)`, `Inductive.ctor_family/2`.
- Produces: `{:ctor, :Z, []}` lowers to integer `0`; `{:ctor, :S, [n]}` lowers to `lower(n) + 1`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/nat_erasure_construction_test.exs
defmodule Cure.Elab.NatErasureConstructionTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  test "Nat literals erase to native integers, not nested tuples" do
    src = "mod M\n  fn three() -> Nat = S(S(S(Z())))\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.NatC1", functions: [:three])
    assert apply(mod, :three, []) == 3
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/nat_erasure_construction_test.exs`
Expected: FAIL — `three/0` returns `{:S, {:S, {:S, :Z}}}`.

- [ ] **Step 3: Add the `:nat` construction lowering**

Extend `emit.ex`'s `lower/3` constructor `cond` (from Task 10):

```elixir
    args == [] and nat_family?(env, name) ->        # :Z
      {:integer, @line, 0}
    match?([_], args) and nat_family?(env, name) -> # :S(n)
      [inner] = args
      {:op, @line, :+, lower(env, inner, ctx), {:integer, @line, 1}}
```

with `defp nat_family?(env, name), do: Inductive.builtin(env, :nat) == Inductive.ctor_family(env, name)`.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/elab/nat_erasure_construction_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/emit.ex test/cure/elab/nat_erasure_construction_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(erase): Nat Z/S construction lowers to native integers"
```

---

### Task 14: Erase `match` on `Nat` to integer test/decrement

**Files:**
- Modify: `lib/cure/elab/emit.ex` (the `:case` lowering — add a `:nat`-family branch form)
- Test: `test/cure/elab/nat_erasure_match_test.exs` (create)

**Interfaces:**
- Consumes: `Inductive.builtin(env, :nat)`; the `:case` lowering site.
- Produces: a `:case` scrutinising a `Nat` lowers to `case <n> of 0 -> <Z-branch>; _ -> (<S-var> = <n> - 1; <S-branch>)` — the `S(m)` branch binds `m` to `n - 1`.

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/nat_erasure_match_test.exs
defmodule Cure.Elab.NatErasureMatchTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  test "pattern-matching a Nat uses integer test/decrement and returns correctly" do
    src = "mod M\n  fn pred(n: Nat) -> Nat = match n\n    Z() -> Z()\n    S(m) -> m\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.NatM1", functions: [:pred])
    assert apply(mod, :pred, [0]) == 0
    assert apply(mod, :pred, [5]) == 4
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/nat_erasure_match_test.exs`
Expected: FAIL — the `:case` lowering emits atom/tuple patterns (`:Z` / `{:S, m}`) that never match the integer inputs.

- [ ] **Step 3: Add the `:nat` `:case` lowering**

In the `:case` lowering, when the scrutinee's family is `:nat`, emit the integer-test form instead of atom/tuple constructor patterns: a `0 ->` clause for the `Z` branch, and a catch-all `Other ->` clause that binds the `S` branch's variable to `Other - 1` before the branch body. Preserve branch order/semantics.

> **Implementer note:** locate the `:case` lowering in `emit.ex` (the counterpart to `erase.ex`'s `{:case, s, m, branches}`), read how branches carry `{ctor, arity, body}` and the branch's bound variable, and construct the Erlang `case` abstract form with the two clauses. The `S(m)` branch's bound `m` must be an Erlang match `M = Scrut - 1` (or a fresh var bound in the clause). Guard: this arm fires only when `Inductive.builtin(env, :nat) == <scrutinee family>`; all other families keep the existing constructor-pattern lowering unchanged.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/elab/nat_erasure_match_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/emit.ex test/cure/elab/nat_erasure_match_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(erase): Nat match lowers to integer test/decrement"
```

---

### Task 15: Generics/monomorphisation guard + `S`/`Z` as first-class values

**Files:**
- Modify: `lib/cure/elab/emit.ex` (ensure `S`/`Z` used as first-class values lower to the increment/zero closures)
- Test: `test/cure/elab/nat_generics_guard_test.exs` (create)

**Interfaces:**
- Consumes: the monomorphisation stage (verify it runs before erasure for the dependent path) and `Inductive.builtin(env, :nat)`.
- Produces: `S`/`Z` referenced as values (not immediately applied) lower to `fun(N) -> N + 1 end` / `0`; and a concrete `Nat` argument to a monomorphised generic function uses the native rep. An abstract-parameter generic body over an un-instantiated type variable does NOT emit native-int decrement (design decision 2).

- [ ] **Step 1: Write the failing test**

```elixir
# test/cure/elab/nat_generics_guard_test.exs
defmodule Cure.Elab.NatGenericsGuardTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  test "S used as a first-class value is the increment closure" do
    src = "mod M\n  fn bump(f: (Nat) -> Nat, n: Nat) -> Nat = f(n)\n  fn go() -> Nat = bump(S, Z())\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.NatG1", functions: [:go])
    assert apply(mod, :go, []) == 1
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/nat_generics_guard_test.exs`
Expected: FAIL — bare `S` lowers to the atom `:S` / an arity-mismatched constructor form.

- [ ] **Step 3: Lower first-class `S`/`Z`; add the monomorphisation guard**

- Lower a bare `Z` value to `{:integer, @line, 0}` and a bare `S` value to a 1-arg increment closure `fun(N) -> N + 1 end` (Erlang abstract form).
- Verify the dependent pipeline monomorphises before erasure. If a generic body over an abstract type parameter reaches erasure un-monomorphised, it must NOT apply the `:nat` native lowering (the parameter isn't concretely `Nat`); the native lowering fires only on a concrete `Nat` family match, which an abstract type variable never satisfies. Add a comment at the `nat_family?/2` guard site recording this.

> **Implementer note:** confirm where monomorphisation runs relative to `erase`/`emit` for the dependent path (search the pipeline for the monomorphisation stage; the cure-language skill notes "generics + monomorphisation"). If monomorphisation is guaranteed pre-erasure, the guard is automatically satisfied (abstract parameters are gone by erasure) and this test plus a comment suffice. If NOT guaranteed, STOP and report — do not emit a representation-ambiguous body; this is the open case the spec flagged, and a wrong choice here is a silent miscompile.

- [ ] **Step 4: Run test to verify it passes**

Run: `mix test test/cure/elab/nat_generics_guard_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/emit.ex test/cure/elab/nat_generics_guard_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(erase): first-class S/Z closures; monomorphisation guard for Nat rep"
```

---

### Task 16: Representation-agreement property + Nat oracle probe + Phase 2 full-suite gate

**Files:**
- Create: `test/property/nat_representation_agreement_test.exs`
- Create: `test/oracle/nat/nat01_arith.cure`, `test/oracle/nat/nat01_arith.idr`, `test/oracle/nat/verdicts.json`
- Verify only: full suite.

**Interfaces:**
- Consumes: the erased-Nat runtime (Tasks 13-15) and the inductive-Nat kernel evaluation.
- Produces: a property test that erased-Nat evaluation agrees with inductive-Nat evaluation on a generated corpus; an oracle probe confirming efficient `Nat` arithmetic compiles + runs to the right integer on the BEAM, accept/accept vs Idris.

- [ ] **Step 1: Write the representation-agreement property**

```elixir
# test/property/nat_representation_agreement_test.exs
defmodule Cure.Property.NatRepresentationAgreementTest do
  use ExUnit.Case, async: true
  # For each n in a generated corpus, the erased runtime value of a Nat-producing
  # program equals n, matching the inductive-Nat count. Use the project's existing
  # property/StreamData harness if present; otherwise a deterministic corpus 0..64.

  for n <- 0..64 do
    test "erased S^#{n}(Z) evaluates to #{n}" do
      src = "mod M\n  fn v() -> Nat = #{String.duplicate("S(", unquote(n))}Z()#{String.duplicate(")", unquote(n))}\n"
      {:ok, env} = Cure.Elab.Program.elaborate(src)
      {:ok, mod} = Cure.Elab.Emit.compile_and_load(env, module: :"Cure.NatP#{unquote(n)}", functions: [:v])
      assert apply(mod, :v, []) == unquote(n)
    end
  end
end
```

> **Implementer note:** if the repo has an Antigen/StreamData generator convention for corpora, use it instead of the `0..64` unrolled range to match house style; the agreement invariant (erased value == inductive count) is the fixed contract.

- [ ] **Step 2: Run the property to verify it passes** (Tasks 13-15 make it green)

Run: `mix test test/property/nat_representation_agreement_test.exs`
Expected: PASS.

- [ ] **Step 3: Add the oracle probe**

Create the paired probe (faithful transliteration, same signature both languages):

`test/oracle/nat/nat01_arith.cure`:
```cure
mod M
  type Nat = Z | S(Nat)
  fn plus(a: Nat, b: Nat) -> Nat = match a
    Z() -> b
    S(m) -> S(plus(m, b))
  fn four() -> Nat = plus(S(S(Z())), S(S(Z())))
```

`test/oracle/nat/nat01_arith.idr` (`%default total`, no module line):
```idris
%default total
data Nat' = Z | S Nat'
plus : Nat' -> Nat' -> Nat'
plus Z b = b
plus (S m) b = S (plus m b)
four : Nat'
four = plus (S (S Z)) (S (S Z))
```

- [ ] **Step 4: Run the oracle and freeze verdicts**

Run: `mix cure.oracle nat`
Expected: both accept; write `test/oracle/nat/verdicts.json` with relation `same` (never hand-write a verdict — let the oracle produce it).

- [ ] **Step 5: Replay green**

Run: `mix test test/oracle_replay_test.exs`
Expected: PASS.

- [ ] **Step 6: Run the FULL suite ONCE, alone (Phase 2 gate)**

Run: `mix test`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add -- test/property/nat_representation_agreement_test.exs test/oracle/nat/nat01_arith.cure test/oracle/nat/nat01_arith.idr test/oracle/nat/verdicts.json
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(nat): representation-agreement property + Nat arithmetic oracle probe"
```

---

## Self-Review (against the spec)

**Spec coverage:**
- §1 registry mechanism → Tasks 1 (field/accessors), 3 (seed), 4 (parser + prelude wiring). ✅
- §1 schema checks **names not arity** → Task 2. ✅
- §1 single-registration invariant (both halves: prelude-only honoring + hard error on duplicate) → Task 1 (hard error) + Task 4 (prelude-only gate). ✅
- §1 `@builtin`-on-`type` parser gap → Task 4. ✅
- §1 `Env` builtins-field extension → Task 1. ✅
- §1 nominal-not-structural caveat → surfaced in Task 15's note + design decision 2; a locally-redeclared `Nat` gets no native rep (it isn't the `:nat` family). ✅
- §2 `infer_prim` → inductive Bool → Task 5. ✅
- §2 `fold/2` hardcodes `:True`/`:False` + single-source-of-truth + drift assertion → Task 6 + Task 10 antibody. ✅
- §2 literals → constructors → Task 7. ✅
- §2 if/guard/literal retarget to `:case` → Task 8. ✅
- §2 retire across **nine** modules incl. `serialize.ex` + conformance fixture → Task 9. ✅
- §2 erasure to lowercase atoms → Task 10. ✅
- §3 Nat→Int construction/match/first-class/arith → Tasks 13, 14, 15. ✅
- §3 soundness placement (untrusted) + representation-agreement → Task 16. ✅
- §3 generics gap (open) → resolved as design decision 2, guarded in Task 15. ✅
- §Phasing sequential, Phase 1 first, `:nat` schema seeded in Phase 1 → Tasks 3/4 seed `:nat`; Phase 2 consumes only. ✅
- §Testing antibodies (malformed + name-mismatched + duplicate + migration + drift) → Tasks 2, 10, 12. ✅
- §Risks bootstrapping/load-order → Task 11; migration churn → Task 8's reuse of green tests; capitalization → Tasks 7/10. ✅

**Placeholder scan:** No "TBD"/"handle edge cases". The two spec-flagged open questions are resolved as explicit design decisions (bootstrap-seeded Env; monomorphisation-contingent Nat rep). Implementer notes flag every place the exact struct/term shape must be confirmed against real source before coding — these are verification instructions, not deferred decisions.

**Type consistency:** `Inductive.builtin/2`, `register_builtin/3`, `Builtins.validate!/3`, `Builtins.seed/1`, `Builtins.schema/1`, `bool_type_value/1` (kernel), `bool_type_term/1`/`bool_case/5` (elab), `vbool/1`/`as_bool/1` (eval), `bool_atom/1`/`nat_family?/2` (emit) are used consistently across the tasks that define and consume them.

**Known implementer-verification points (must confirm against source before/while coding, called out inline):** exact ctor-map field names from `Inductive.declare/3`; the value/term shape of an applied nullary inductive family (the pivot of Tasks 5-8); the `:case` branch-tuple shape and coverage expectation; `parse_type_def/1`'s return tag; the conformance-harness context-construction site; whether monomorphisation is guaranteed pre-erasure (Task 15 STOP-condition if not).
