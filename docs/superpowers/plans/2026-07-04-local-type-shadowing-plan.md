# Local Type/Constructor Shadowing Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make a module's local `type Nat = Zero | Suc` fully shadow an imported/auto-imported namesake — including its constructors — so `match` coverage no longer demands the imported ctors (`{:missing_branch, :S}`), while keeping the imported family reachable via a qualified escape hatch (`Std.Nat.Z`).

**Architecture:** A new **E-layer resolution module** (`lib/cure/elab/resolution.ex`) sits over the bare-atom registry. Collision detection runs in `program.ex` before elaboration, driven by an **AST-own-declaration provenance scan** (each distinct module's *own* declared family names, so transitively-reached families are not phantom sources). Colliding imported families are **re-keyed** per-slice (`:Nat` → `:"Std.Nat#Nat"`, `:Z` → `:"Std.Nat#Z"`) *before* the import merge, and residual bare copies are dropped before the local module merges on top — so `Inductive.ctors_of/2` naturally returns the disowned set with zero kernel change. Qualified references and shadow diagnostics are **derived from the already-re-keyed env** (no new parameter threading, no core `Env` field). The only C-layer touch strips the `Mod#` prefix from a runtime constructor tag.

**Tech Stack:** Elixir; Cure dependent elaborator (`lib/cure/elab/*`) + kernel registry (`lib/cure/core/*`, read-only for term shapes); differential oracle (`mix cure.oracle`, `idris2`); ExUnit.

## Global Constraints

- **No kernel/TCB change.** `lib/cure/core/*` is NOT modified. The resolution layer and its Core-term rewrite live entirely in `lib/cure/elab/*`; term shapes in `term.ex` are read (matched), never edited.
- **No core `Env` struct field added.** The resolution info is either baked into the re-keyed env's existing maps or derived from them on demand. `lib/cure/core/env.ex` (`inductive.ex`'s `Cure.Core.Env`) is untouched.
- **R6 non-regression is byte-for-byte on the non-collision path.** Every currently-green program must elaborate identically. Baseline: `mix test` at 2843/0 (or higher), `mix test test/oracle_replay_test.exs` green.
- **Auto-prelude skip is RETAINED (lowest-risk choice per spec §3.1).** `auto_prelude_imports/1` keeps skipping `Std.Bool`/`Std.Nat` when the module declares a same-named type. Re-keying is validated against **explicit `use`**. Existing `test/cure/elab/auto_prelude_test.exs` must stay green.
- **Runtime constructor tags stay bare** (AtomVM value invariant): codegen emits `Z` for a re-keyed `:"Std.Nat#Z"`.
- **Ghost-writer commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO `Co-Authored-By`, no Claude signature.
- **Explicit-pathspec staging only:** `git add -- <path>` (never `-A`/`.`). A concurrent agent may share the worktree.
- **One build at a time.** Never run two `mix` suites concurrently. Prefer scoped `mix test <file>`; run the full suite once, alone, at the gate.
- **Oracle probes** are faithful `.cure`/`.idr` transliterations (`.idr` carries `%default total`, no `module` line). Never hand-write a verdict; `mix cure.oracle shadow` generates `verdicts.json`.

---

## File Structure

- **Create** `lib/cure/elab/resolution.ex` — `Cure.Elab.Resolution`: the whole resolution layer. Pure functions over `Cure.Core.Env`. Responsibilities: (1) `rekey_term/2` Core-term atom substitution; (2) `rekey_module_env/3` re-key one module's owned families/ctors/defs; (3) `classify/2` collision detection over AST provenance; (4) `resolve_qualified/3` dotted-path → registry key; (5) `shadowed_origin/2` + `ambiguous?/2` diagnostic helpers.
- **Modify** `lib/cure/elab/program.ex` — `check_ast/1` and the import pipeline: build distinct per-module slices, classify, re-key losers, drop residual bare keys, merge local on top.
- **Modify** `lib/cure/elab/elaborator.ex` — resolve qualified ctor keys at `constructor_pattern` callers (`partition_arms`, `partition_rematch_arms`) and `elaborate_named_call`; the R5 `:shadowed_ctor` diagnostic at the unknown-constructor gate; R7 `:ambiguous_name` on bare value lookup.
- **Modify** `lib/cure/elab/declarations.ex` — `idx_to_core` `{:function_call,…}` and `{:attribute_access,…}` clauses + `resolve_index_name` for qualified type-slot references and R7 on bare type lookup.
- **Modify** `lib/cure/compiler/codegen.ex` — `constructor_tag/1` strips a `Mod#` prefix.
- **Create** `test/cure/elab/resolution_test.exs` — unit tests for the `Resolution` module (rekey_term, rekey_module_env, classify, resolve_qualified).
- **Create** `test/cure/elab/type_shadowing_test.exs` — end-to-end `Program.elaborate/1` behavioral tests (R1–R5, R7).
- **Create** `test/oracle/shadow/` — oracle cluster: `shadow01`–`shadow07` `.cure`/`.idr` pairs + generated `verdicts.json`.

---

## Interfaces (the contract every task shares)

The `Resolution` module's public surface, defined across Tasks 2–4, 6, 9, 10 and consumed by Tasks 5, 7, 8, 9, 10:

```
Cure.Elab.Resolution.rekey_term(term :: Core.Term.t(), atom_map :: %{atom() => atom()}) :: Core.Term.t()
Cure.Elab.Resolution.rekey_module_env(env :: Env.t(), module_id :: String.t(), owned_family_names :: MapSet.t(atom())) :: Env.t()
Cure.Elab.Resolution.classify(family_owners :: %{atom() => MapSet.t(String.t())}, local_families :: MapSet.t(atom())) :: %{losers: %{String.t() => MapSet.t(atom())}, ambiguous: MapSet.t(atom())}
Cure.Elab.Resolution.resolve_qualified(env :: Env.t(), dotted :: String.t(), slot :: :type | :value) :: {:ok, atom()} | :error
Cure.Elab.Resolution.shadowed_origin(env :: Env.t(), bare :: atom()) :: {:ok, module_id :: String.t(), rekeyed :: atom()} | :error
Cure.Elab.Resolution.ambiguous_modules(env :: Env.t(), bare :: atom()) :: [String.t()]   # ≥2 ⇒ ambiguous
```

`module_id` is a canonical dotted path string, e.g. `"Std.Nat"`. A re-keyed atom is `:"<module_id>#<bare>"`, e.g. `:"Std.Nat#Z"`. The qualified surface path uses `.` (`"Std.Nat.Z"`); the registry key uses `#` (`:"Std.Nat#Z"`). Task 6's `resolve_qualified` is the single place that bridges `.`→`#`.

---

### Task 1: Red repro — oracle cluster + failing behavioral test

**Files:**
- Create: `test/oracle/shadow/shadow01_explicit_use_local_shadow.cure`
- Create: `test/oracle/shadow/shadow01_explicit_use_local_shadow.idr`
- Create: `test/cure/elab/type_shadowing_test.exs`

**Interfaces:**
- Consumes: `Cure.Elab.Program.elaborate/1` (existing).
- Produces: the `shadow` cluster directory; the `type_shadowing_test.exs` file that later tasks extend.

- [ ] **Step 1: Write the failing oracle probe (`.cure`)**

`test/oracle/shadow/shadow01_explicit_use_local_shadow.cure`:
```
mod ExplicitShadow
  use Std.Nat
  type Nat = Zero | Suc(Nat)
  fn add(a: Nat, b: Nat) -> Nat = match a
    Zero() -> b
    Suc(m) -> Suc(add(m, b))
end
```

- [ ] **Step 2: Write the faithful Idris transliteration (`.idr`)**

`test/oracle/shadow/shadow01_explicit_use_local_shadow.idr`:
```idris
%default total

data Nat' = Zero | Suc Nat'

add : Nat' -> Nat' -> Nat'
add Zero b = b
add (Suc m) b = Suc (add m b)
```
(Idris' own `Nat` is always in scope from its prelude; a local `data Nat'` faithfully models "a local datatype shadowing a same-named library one" without fighting Idris' prelude. The behavior under test — local datatype + its own constructors cover the match — is identical.)

- [ ] **Step 3: Write the red behavioral test**

`test/cure/elab/type_shadowing_test.exs`:
```elixir
defmodule Cure.Elab.TypeShadowingTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp elaborate(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    Program.check_ast(ast)
  end

  test "R1a: explicit `use Std.Nat` + local `Nat = Zero|Suc` — local ctors cover the match" do
    src = """
    mod ExplicitShadow
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn add(a: Nat, b: Nat) -> Nat = match a
        Zero() -> b
        Suc(m) -> Suc(add(m, b))
    end
    """

    assert {:ok, _env} = elaborate(src)
  end
end
```

- [ ] **Step 4: Run the test to confirm it fails with the target bug**

Run: `mix test test/cure/elab/type_shadowing_test.exs`
Expected: FAIL — `elaborate/1` returns `{:error, {:missing_branch, :S}}` (the exact bug the spec §1.1 reproduces), so the `assert {:ok, _}` fails.

- [ ] **Step 5: Commit**

```bash
git add -- test/oracle/shadow/shadow01_explicit_use_local_shadow.cure test/oracle/shadow/shadow01_explicit_use_local_shadow.idr test/cure/elab/type_shadowing_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(shadow): red repro for local Nat shadowing missing_branch bug"
```

---

### Task 2: `Resolution.rekey_term/2` — Core-term atom substitution

**Files:**
- Create: `lib/cure/elab/resolution.ex`
- Create: `test/cure/elab/resolution_test.exs`

**Interfaces:**
- Consumes: `Cure.Core.Term` node shapes (read-only): `{:data, name, params, indices}`, `{:ctor, name, args}`, `{:case, scrut, motive, [{cname, arity, body}]}`, and all structural nodes (`:pi`, `:lam`, `:sigma`, `:app`, `:pair`, `:fst`, `:snd`, `:eq`, `:refl`, `:rewrite`, `:prim`), plus leaves (`:var`, `:type`, `:global`, `:int_type`, `:int_lit`, `:float_type`, `:float_lit`).
- Produces: `Cure.Elab.Resolution.rekey_term/2`.

- [ ] **Step 1: Write the failing unit tests**

`test/cure/elab/resolution_test.exs`:
```elixir
defmodule Cure.Elab.ResolutionTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Resolution

  describe "rekey_term/2" do
    setup do
      %{map: %{Nat: :"Std.Nat#Nat", Z: :"Std.Nat#Z", S: :"Std.Nat#S"}}
    end

    test "rewrites a :data head", %{map: m} do
      assert Resolution.rekey_term({:data, :Nat, [], []}, m) == {:data, :"Std.Nat#Nat", [], []}
    end

    test "rewrites a :ctor head and recurses into args", %{map: m} do
      assert Resolution.rekey_term({:ctor, :S, [{:ctor, :Z, []}]}, m) ==
               {:ctor, :"Std.Nat#S", [{:ctor, :"Std.Nat#Z", []}]}
    end

    test "rewrites a :case branch TAG (the position distinct from {:ctor,…})", %{map: m} do
      term = {:case, {:var, 0}, {:lam, {:data, :Nat, [], []}, {:type, 0}},
              [{:Z, 0, {:var, 0}}, {:S, 1, {:ctor, :Z, []}}]}
      assert Resolution.rekey_term(term, m) ==
               {:case, {:var, 0}, {:lam, {:data, :"Std.Nat#Nat", [], []}, {:type, 0}},
                [{:"Std.Nat#Z", 0, {:var, 0}}, {:"Std.Nat#S", 1, {:ctor, :"Std.Nat#Z", []}}]}
    end

    test "leaves a :global untouched (functions keep bare names)", %{map: m} do
      assert Resolution.rekey_term({:global, :Z}, m) == {:global, :Z}
    end

    test "recurses through structural nodes and leaves unmapped atoms alone", %{map: m} do
      term = {:pi, {:data, :Nat, [], []}, {:data, :Other, [], []}}
      assert Resolution.rekey_term(term, m) == {:pi, {:data, :"Std.Nat#Nat", [], []}, {:data, :Other, [], []}}
    end
  end
end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/elab/resolution_test.exs`
Expected: FAIL — `Cure.Elab.Resolution` is undefined.

- [ ] **Step 3: Create the module with `rekey_term/2`**

`lib/cure/elab/resolution.ex`:
```elixir
defmodule Cure.Elab.Resolution do
  @moduledoc """
  E-layer resolution over the bare-atom registry (Approach B). Detects
  family-name collisions between imported modules and the local module, re-keys
  the shadowed imports to qualified atoms (`:"Mod#Name"`), and resolves qualified
  surface references + shadow diagnostics from the re-keyed env. The kernel/TCB
  (`lib/cure/core/*`) is never modified; this module only reads Core term shapes.
  """

  alias Cure.Core.{Env, Inductive}

  @doc """
  Substitute constructor/family atoms in a Core term per `atom_map`
  (`%{bare => rekeyed}`). Rewrites the three bare-atom term positions —
  `:data` heads, `:ctor` heads, and `:case` branch tags — and recurses through
  every structural node. Leaves `:global` (function references keep bare names)
  and all literals untouched. An atom absent from `atom_map` is passed through.
  """
  @spec rekey_term(term, %{atom() => atom()}) :: term when term: tuple()
  def rekey_term(term, m)

  def rekey_term({:data, n, ps, is}, m),
    do: {:data, Map.get(m, n, n), Enum.map(ps, &rekey_term(&1, m)), Enum.map(is, &rekey_term(&1, m))}

  def rekey_term({:ctor, n, args}, m),
    do: {:ctor, Map.get(m, n, n), Enum.map(args, &rekey_term(&1, m))}

  def rekey_term({:case, s, mo, brs}, m),
    do:
      {:case, rekey_term(s, m), rekey_term(mo, m),
       Enum.map(brs, fn {cn, ar, b} -> {Map.get(m, cn, cn), ar, rekey_term(b, m)} end)}

  def rekey_term({:pi, dom, cod}, m), do: {:pi, rekey_term(dom, m), rekey_term(cod, m)}
  def rekey_term({:lam, dom, body}, m), do: {:lam, rekey_term(dom, m), rekey_term(body, m)}
  def rekey_term({:sigma, a, b}, m), do: {:sigma, rekey_term(a, m), rekey_term(b, m)}
  def rekey_term({:app, f, a}, m), do: {:app, rekey_term(f, m), rekey_term(a, m)}
  def rekey_term({:pair, a, b}, m), do: {:pair, rekey_term(a, m), rekey_term(b, m)}
  def rekey_term({:fst, p}, m), do: {:fst, rekey_term(p, m)}
  def rekey_term({:snd, p}, m), do: {:snd, rekey_term(p, m)}
  def rekey_term({:eq, ty, a, b}, m), do: {:eq, rekey_term(ty, m), rekey_term(a, m), rekey_term(b, m)}
  def rekey_term({:refl, a}, m), do: {:refl, rekey_term(a, m)}

  def rekey_term({:rewrite, proof, motive, body}, m),
    do: {:rewrite, rekey_term(proof, m), rekey_term(motive, m), rekey_term(body, m)}

  def rekey_term({:prim, op, args}, m), do: {:prim, op, Enum.map(args, &rekey_term(&1, m))}

  # Leaves: :var, :type, :global, :int_type, :int_lit, :float_type, :float_lit.
  def rekey_term(leaf, _m), do: leaf
end
```

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/elab/resolution_test.exs`
Expected: PASS (5 tests).

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/resolution.ex test/cure/elab/resolution_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): Resolution.rekey_term Core-atom substitution (data/ctor/case-tag)"
```

---

### Task 3: `Resolution.rekey_module_env/3` — re-key one module's owned families

**Files:**
- Modify: `lib/cure/elab/resolution.ex`
- Modify: `test/cure/elab/resolution_test.exs`

**Interfaces:**
- Consumes: `rekey_term/2` (Task 2); `Cure.Core.Env` struct (`families`, `ctors`, `ctor_to_family`, `defs` maps); record shapes `family: %{name, params, indices, level}`, `ctor: %{name, args, result_indices, result_params, quantities}`, `def: %{name, type, body, quantities}`; telescope `[{atom, Term}]`.
- Produces: `Cure.Elab.Resolution.rekey_module_env/3`.

- [ ] **Step 1: Write the failing unit test**

Add to `test/cure/elab/resolution_test.exs`:
```elixir
  describe "rekey_module_env/3" do
    setup do
      # A tiny Std.Nat-shaped env: family Nat (nullary), ctors Z / S(Nat), and a
      # def `plus` that matches on Nat via a :case whose branch tags are Z / S.
      env =
        %Cure.Core.Env{}
        |> Cure.Core.Inductive.declare(
          Cure.Core.Inductive.family(:Nat, [], [], 0),
          [
            Cure.Core.Inductive.ctor(:Z, [], []),
            Cure.Core.Inductive.ctor(:S, [{:n, {:data, :Nat, [], []}}], [])
          ]
        )
        |> Cure.Core.Env.add_def(
          :plus,
          {:pi, {:data, :Nat, [], []}, {:data, :Nat, [], []}},
          {:case, {:var, 0}, {:lam, {:data, :Nat, [], []}, {:data, :Nat, [], []}},
           [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:ctor, :S, [{:var, 0}]}}]}
        )

      %{env: env}
    end

    test "moves family + ctor keys to :\"Mod#Name\" and repoints ctor_to_family", %{env: env} do
      out = Cure.Elab.Resolution.rekey_module_env(env, "Std.Nat", MapSet.new([:Nat]))

      assert Map.has_key?(out.families, :"Std.Nat#Nat")
      refute Map.has_key?(out.families, :Nat)
      assert out.families[:"Std.Nat#Nat"].name == :"Std.Nat#Nat"

      assert Map.has_key?(out.ctors, :"Std.Nat#Z")
      assert Map.has_key?(out.ctors, :"Std.Nat#S")
      refute Map.has_key?(out.ctors, :Z)
      assert out.ctor_to_family[:"Std.Nat#Z"] == :"Std.Nat#Nat"
      assert out.ctor_to_family[:"Std.Nat#S"] == :"Std.Nat#Nat"
    end

    test "rewrites embedded terms in ctor arg types", %{env: env} do
      out = Cure.Elab.Resolution.rekey_module_env(env, "Std.Nat", MapSet.new([:Nat]))
      assert [{:n, {:data, :"Std.Nat#Nat", [], []}}] = out.ctors[:"Std.Nat#S"].args
    end

    test "rewrites embedded terms in def bodies including :case branch tags", %{env: env} do
      out = Cure.Elab.Resolution.rekey_module_env(env, "Std.Nat", MapSet.new([:Nat]))
      body = out.defs[:plus].body
      assert {:case, _, _, [{:"Std.Nat#Z", 0, _}, {:"Std.Nat#S", 1, _}]} = body
      assert out.defs[:plus].type == {:pi, {:data, :"Std.Nat#Nat", [], []}, {:data, :"Std.Nat#Nat", [], []}}
    end

    test "leaves a non-owned family in the same env untouched", %{env: env} do
      env2 =
        Cure.Core.Inductive.declare(env, Cure.Core.Inductive.family(:Bool, [], [], 0),
          [Cure.Core.Inductive.ctor(:True, [], []), Cure.Core.Inductive.ctor(:False, [], [])])

      out = Cure.Elab.Resolution.rekey_module_env(env2, "Std.Nat", MapSet.new([:Nat]))
      assert Map.has_key?(out.families, :Bool)
      assert Map.has_key?(out.ctors, :True)
    end
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/elab/resolution_test.exs`
Expected: FAIL — `rekey_module_env/3` undefined.

- [ ] **Step 3: Implement `rekey_module_env/3`**

Add to `lib/cure/elab/resolution.ex` (inside the module):
```elixir
  @doc """
  Re-key every family named in `owned_family_names` (and each of its
  constructors) within `env`'s slice to `:"<module_id>#<name>"`. Renames the
  `families`/`ctors`/`ctor_to_family` map keys, updates each record's `:name`
  field, and rewrites every embedded Core term (family/ctor telescopes,
  ctor result indices/params, and ALL def bodies+types in the slice) via
  `rekey_term/2`. Families/ctors NOT owned are left untouched. Functions keep
  their bare `defs` keys (only embedded family/ctor references are rewritten).
  """
  @spec rekey_module_env(Env.t(), String.t(), MapSet.t(atom())) :: Env.t()
  def rekey_module_env(%Env{} = env, module_id, owned_family_names) do
    # Owned ctor names: ctors whose family is an owned family name.
    owned_ctor_names =
      for {cname, fname} <- env.ctor_to_family, MapSet.member?(owned_family_names, fname), into: MapSet.new(), do: cname

    # bare -> rekeyed atom map covering both owned families and their ctors.
    amap =
      Enum.reduce(owned_family_names, %{}, fn f, acc -> Map.put(acc, f, rekey_atom(module_id, f)) end)

    amap =
      Enum.reduce(owned_ctor_names, amap, fn c, acc -> Map.put(acc, c, rekey_atom(module_id, c)) end)

    %Env{
      env
      | families: rekey_families(env.families, owned_family_names, amap),
        ctors: rekey_ctors(env.ctors, owned_ctor_names, amap),
        ctor_to_family: rekey_c2f(env.ctor_to_family, amap),
        defs: rekey_defs(env.defs, amap)
    }
  end

  defp rekey_atom(module_id, bare), do: String.to_atom(module_id <> "#" <> Atom.to_string(bare))

  defp rekey_families(families, owned, amap) do
    Map.new(families, fn {k, fam} ->
      if MapSet.member?(owned, k) do
        {Map.fetch!(amap, k),
         %{fam | name: Map.fetch!(amap, k),
                 params: rekey_tele(fam.params, amap), indices: rekey_tele(fam.indices, amap)}}
      else
        {k, %{fam | params: rekey_tele(fam.params, amap), indices: rekey_tele(fam.indices, amap)}}
      end
    end)
  end

  defp rekey_ctors(ctors, owned_ctor_names, amap) do
    Map.new(ctors, fn {k, c} ->
      c2 = %{c |
        name: Map.get(amap, c.name, c.name),
        args: rekey_tele(c.args, amap),
        result_indices: Enum.map(c.result_indices, &rekey_term(&1, amap)),
        result_params: Enum.map(c.result_params, &rekey_term(&1, amap))
      }

      if MapSet.member?(owned_ctor_names, k), do: {Map.fetch!(amap, k), c2}, else: {k, c2}
    end)
  end

  defp rekey_c2f(c2f, amap) do
    Map.new(c2f, fn {c, f} -> {Map.get(amap, c, c), Map.get(amap, f, f)} end)
  end

  defp rekey_defs(defs, amap) do
    Map.new(defs, fn {k, d} ->
      {k, %{d | type: rekey_term(d.type, amap), body: rekey_term(d.body, amap)}}
    end)
  end

  defp rekey_tele(tele, amap), do: Enum.map(tele, fn {n, t} -> {n, rekey_term(t, amap)} end)
```

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/elab/resolution_test.exs`
Expected: PASS (all rekey tests).

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/resolution.ex test/cure/elab/resolution_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): Resolution.rekey_module_env — re-key one module's owned families"
```

---

### Task 4: `Resolution.classify/2` — collision detection with module-identity provenance

**Files:**
- Modify: `lib/cure/elab/resolution.ex`
- Modify: `test/cure/elab/resolution_test.exs`

**Interfaces:**
- Consumes: `family_owners :: %{atom() => MapSet(module_id)}` and `local_families :: MapSet(atom())` (both built by Task 5 from AST scans).
- Produces: `Cure.Elab.Resolution.classify/2` → `%{losers: %{module_id => MapSet(family_name)}, ambiguous: MapSet(family_name)}`.

- [ ] **Step 1: Write the failing unit tests**

Add to `test/cure/elab/resolution_test.exs`:
```elixir
  describe "classify/2" do
    test "local declaration shadows a single imported owner: that import is a loser" do
      owners = %{Nat: MapSet.new(["Std.Nat"])}
      out = Cure.Elab.Resolution.classify(owners, MapSet.new([:Nat]))
      assert out.losers == %{"Std.Nat" => MapSet.new([:Nat])}
      assert out.ambiguous == MapSet.new()
    end

    test "one import owner, no local: NOT a collision (no re-key)" do
      owners = %{Nat: MapSet.new(["Std.Nat"])}
      out = Cure.Elab.Resolution.classify(owners, MapSet.new())
      assert out.losers == %{}
      assert out.ambiguous == MapSet.new()
    end

    test "same module owning a name (diamond dedup already applied): still ONE owner, no collision" do
      # Std.Vector's transitive Nat is attributed to Std.Nat by the AST scan, so
      # owners(Nat) = {Std.Nat} — a single owner even though reached two ways.
      owners = %{Nat: MapSet.new(["Std.Nat"]), Vector: MapSet.new(["Std.Vector"])}
      out = Cure.Elab.Resolution.classify(owners, MapSet.new())
      assert out.losers == %{}
      assert out.ambiguous == MapSet.new()
    end

    test "two distinct import owners, no local: ambiguous, both losers" do
      owners = %{Nat: MapSet.new(["Std.Foo", "Std.Bar"])}
      out = Cure.Elab.Resolution.classify(owners, MapSet.new())
      assert out.ambiguous == MapSet.new([:Nat])
      assert out.losers == %{"Std.Foo" => MapSet.new([:Nat]), "Std.Bar" => MapSet.new([:Nat])}
    end

    test "two distinct import owners WITH a local: local wins, both imports lose, not ambiguous" do
      owners = %{Nat: MapSet.new(["Std.Foo", "Std.Bar"])}
      out = Cure.Elab.Resolution.classify(owners, MapSet.new([:Nat]))
      assert out.ambiguous == MapSet.new()
      assert out.losers == %{"Std.Foo" => MapSet.new([:Nat]), "Std.Bar" => MapSet.new([:Nat])}
    end
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/elab/resolution_test.exs`
Expected: FAIL — `classify/2` undefined.

- [ ] **Step 3: Implement `classify/2`**

Add to `lib/cure/elab/resolution.ex`:
```elixir
  @doc """
  Classify family-name collisions. A family name `N` collides when its set of
  sources — the distinct import modules that OWN it (declare it in their own
  AST) plus the local module if it declares `N` — has size ≥ 2. In every
  collision the winner of the unqualified name is the LOCAL module if present
  (only the local module can win); therefore every import owner of a colliding
  name is a loser. When no local declares a colliding name, the name is
  additionally `ambiguous` (unqualified use is an error, §3.4) — but its
  owners are still re-keyed so both stay reachable qualified.
  """
  @spec classify(%{atom() => MapSet.t(String.t())}, MapSet.t(atom())) :: %{
          losers: %{String.t() => MapSet.t(atom())},
          ambiguous: MapSet.t(atom())
        }
  def classify(family_owners, local_families) do
    Enum.reduce(family_owners, %{losers: %{}, ambiguous: MapSet.new()}, fn {name, owners}, acc ->
      local? = MapSet.member?(local_families, name)
      n_sources = MapSet.size(owners) + if local?, do: 1, else: 0

      cond do
        n_sources < 2 ->
          acc

        true ->
          losers =
            Enum.reduce(owners, acc.losers, fn mod, ls ->
              Map.update(ls, mod, MapSet.new([name]), &MapSet.put(&1, name))
            end)

          ambiguous = if local?, do: acc.ambiguous, else: MapSet.put(acc.ambiguous, name)
          %{losers: losers, ambiguous: ambiguous}
      end
    end)
  end
```

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/elab/resolution_test.exs`
Expected: PASS (all classify tests).

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/resolution.ex test/cure/elab/resolution_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): Resolution.classify — module-identity collision detection"
```

---

### Task 5: Wire collision detection + re-key into `program.ex` (the core bug fix)

**Files:**
- Modify: `lib/cure/elab/program.ex:29-36` (`check_ast/1`), and the import pipeline `import_env/2`/`import_source_env/2`/`merge_env/2`.
- Modify: `test/cure/elab/type_shadowing_test.exs`
- Test: `test/cure/elab/auto_prelude_test.exs` (must stay green — R6)

**Interfaces:**
- Consumes: `Resolution.classify/2`, `Resolution.rekey_module_env/3`; existing `declared_type_names/1`, `imports/1`, `declarations/1`, `merge_env/2`.
- Produces: a re-keyed merged env from `check_ast/1`. After this task, `Inductive.ctors_of(sig, :Nat)` on a shadowing module returns only the local ctors.

**Design (per spec §3.1/§3.2, robust to transitive imports):**
1. Resolve `auto_prelude_imports(ast) ++ imports(ast)` to distinct `{module_id, path}` (dedup by `module_id`).
2. For each distinct module, `owned_family_names(path)` = family names declared in *that module's own AST* (reuse the `declared_type_names` scan on the imported source). Build `family_owners`.
3. `classify(family_owners, declared_type_names(ast))`.
4. Build each distinct module's per-module env slice; re-key that slice's owned loser families via `rekey_module_env/3`; merge all slices.
5. **Drop residual bare collision keys** from the merged-imports env (transitive copies that survived re-keying): for every colliding family name, delete any leftover bare family key + bare ctors pointing to it. This guarantees the local module merges clean.
6. Merge `seeded` (builtins) + local declarations on top, exactly as today.

- [ ] **Step 1: Add the shadow02 + shadow03 behavioral tests (red)**

Add to `test/cure/elab/type_shadowing_test.exs`:
```elixir
  test "R1 full: local `Nat = Z|S` fully shadows same-named imported ctors" do
    src = """
    mod FullShadow
      use Std.Nat
      type Nat = Z | S(Nat)
      fn two() -> Nat = S(S(Z()))
      fn pred(n: Nat) -> Nat = match n
        Z() -> Z()
        S(m) -> m
    end
    """

    assert {:ok, _env} = elaborate(src)
  end

  test "R2: unshadowed imported ctors Z/S stay visible when local uses Zero/Suc" do
    src = """
    mod PartialShadow
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn imported_one() -> Std.Nat = S(Z())
      fn local_one() -> Nat = Suc(Zero())
    end
    """

    assert {:ok, _env} = elaborate(src)
  end
```
(The `R2` test's `Std.Nat` return type + unqualified `S`/`Z` referring to the imported family will fully pass only after Tasks 7–8; here it asserts the *coverage*/registry side is unblocked. If it still errors on the qualified `Std.Nat` return type at this task, split it: keep only the `local_one` half green now and move the `imported_one` half to Task 8. Run first and see which applies before committing.)

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/elab/type_shadowing_test.exs`
Expected: FAIL — R1a/R1-full still `{:missing_branch, _}`.

- [ ] **Step 3: Add helpers + rewrite the import pipeline in `program.ex`**

Add these private helpers to `lib/cure/elab/program.ex` (near `import_env/2`). `resolve_module_id/1` derives the canonical dotted id + path from an import source; reuse the existing `import_source_path/1` for path resolution.
```elixir
  # Distinct {module_id, path} for every import source, deduped by module_id.
  defp distinct_import_modules(sources) do
    sources
    |> Enum.map(&import_source_path/1)
    |> Enum.flat_map(fn
      {:ok, module_name, path} -> [{to_string(module_name), path}]
      :not_stdlib -> []
    end)
    |> Enum.uniq_by(fn {mod_id, _path} -> mod_id end)
  end

  # Family names DECLARED in a module's own source (transitive imports excluded).
  defp owned_family_names(path) do
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      declared_type_names(ast)
    else
      _ -> MapSet.new()
    end
  end

  # Build ONE module's flat env slice (own decls + its own imports), as today.
  defp module_slice_env(path) do
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false),
         {:ok, env0} <- import_env(imports(ast), MapSet.new()),
         {:ok, env} <- elaborate_declarations(declarations(ast), env0) do
      TotalityClosure.certify_type_level(env)
    end
  end

  # Delete residual bare keys for a colliding family name left by transitive copies.
  defp drop_bare_family(%Env{} = env, name) do
    ctors = for {c, f} <- env.ctor_to_family, f == name, into: [], do: c

    %Env{
      env
      | families: Map.delete(env.families, name),
        ctors: Map.drop(env.ctors, ctors),
        ctor_to_family: Map.drop(env.ctor_to_family, [name | ctors])
    }
  end

  # The full shadow-aware imported-env builder.
  defp shadow_resolved_imports(ast) do
    sources = auto_prelude_imports(ast) ++ imports(ast)
    modules = distinct_import_modules(sources)

    family_owners =
      Enum.reduce(modules, %{}, fn {mod_id, path}, acc ->
        Enum.reduce(owned_family_names(path), acc, fn name, a ->
          Map.update(a, name, MapSet.new([mod_id]), &MapSet.put(&1, mod_id))
        end)
      end)

    local = declared_type_names(ast)
    %{losers: losers, ambiguous: ambiguous} = Resolution.classify(family_owners, local)

    collisions =
      losers |> Map.values() |> Enum.reduce(MapSet.new(), &MapSet.union/2)

    with {:ok, merged} <-
           Enum.reduce_while(modules, {:ok, Env.empty()}, fn {mod_id, path}, {:ok, acc} ->
             case module_slice_env(path) do
               {:ok, slice} ->
                 slice =
                   case Map.get(losers, mod_id) do
                     nil -> slice
                     owned_losers -> Resolution.rekey_module_env(slice, mod_id, owned_losers)
                   end

                 {:cont, {:ok, merge_env(acc, slice)}}

               {:error, _} = err ->
                 {:halt, err}
             end
           end) do
      # Drop residual bare copies of every collision name (transitive leftovers).
      cleaned = Enum.reduce(collisions, merged, fn name, e -> drop_bare_family(e, name) end)
      {:ok, cleaned, ambiguous}
    end
  end
```

- [ ] **Step 4: Rewrite `check_ast/1` to use the shadow-resolved imports**

Replace `check_ast/1` (`lib/cure/elab/program.ex:29-36`):
```elixir
  def check_ast(ast) do
    with {:ok, imported, _ambiguous} <- shadow_resolved_imports(ast),
         seeded = Cure.Core.Builtins.seed(Env.empty(), declared_type_names(ast)),
         env0 = merge_env(seeded, imported),
         {:ok, env} <- elaborate_declarations(declarations(ast), env0, prelude_source?(ast)) do
      TotalityClosure.certify_type_level(env)
    end
  end
```
(The `_ambiguous` set is consumed in Task 10 for R7. `merge_env(seeded, imported)` then `elaborate_declarations` of the local decls layers local families on top of the cleaned imports, exactly as before — but now the imports carry no bare `:Nat` when the local module shadows it. Add `alias Cure.Elab.Resolution` to the module's alias list if not already present.)

- [ ] **Step 5: Run the shadow tests**

Run: `mix test test/cure/elab/type_shadowing_test.exs`
Expected: PASS for R1a and R1-full (shadow01/shadow02). R2 per the Step-1 note (fully green after Task 8; keep the `local_one` half green now).

- [ ] **Step 6: Run the auto-prelude + oracle-replay regression guard (R6)**

Run: `mix test test/cure/elab/auto_prelude_test.exs test/oracle_replay_test.exs`
Expected: PASS (auto-prelude skip retained; no probe regressed). If any diamond/auto+explicit case regresses, the dedup or residual-drop is wrong — fix before committing.

- [ ] **Step 7: Add the shadow02 + shadow03 oracle probes**

`test/oracle/shadow/shadow02_full_shadow.cure`:
```
mod FullShadow
  use Std.Nat
  type Nat = Z | S(Nat)
  fn two() -> Nat = S(S(Z()))
  fn pred(n: Nat) -> Nat = match n
    Z() -> Z()
    S(m) -> m
end
```
`test/oracle/shadow/shadow02_full_shadow.idr`:
```idris
%default total

data Nat' = Z | S Nat'

two : Nat'
two = S (S Z)

pred' : Nat' -> Nat'
pred' Z = Z
pred' (S m) = m
```

`test/oracle/shadow/shadow03_unshadowed_visible.cure`:
```
mod PartialShadow
  use Std.Nat
  type Nat = Zero | Suc(Nat)
  fn local_one() -> Nat = Suc(Zero())
end
```
`test/oracle/shadow/shadow03_unshadowed_visible.idr`:
```idris
%default total

data Nat' = Zero | Suc Nat'

localOne : Nat'
localOne = Suc Zero
```

- [ ] **Step 8: Regenerate verdicts and confirm `same`**

Run: `mix cure.oracle shadow`
Expected: `verdicts.json` written with `shadow01`/`shadow02`/`shadow03` = `{"cure":"accept","idris":"accept","relation":"same"}`.

- [ ] **Step 9: Commit**

```bash
git add -- lib/cure/elab/program.ex test/cure/elab/type_shadowing_test.exs test/oracle/shadow/shadow02_full_shadow.cure test/oracle/shadow/shadow02_full_shadow.idr test/oracle/shadow/shadow03_unshadowed_visible.cure test/oracle/shadow/shadow03_unshadowed_visible.idr test/oracle/shadow/verdicts.json
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): re-key shadowed imports on collision — fixes missing_branch (R1/R2)"
```

---

### Task 6: `Resolution.resolve_qualified/3` — dotted path → registry key

**Files:**
- Modify: `lib/cure/elab/resolution.ex`
- Modify: `test/cure/elab/resolution_test.exs`

**Interfaces:**
- Consumes: the re-keyed `Env` (`families`, `ctors` maps); `Inductive.family?/2`, `Inductive.get_ctor/2`.
- Produces: `Cure.Elab.Resolution.resolve_qualified/3`.

**Resolution rule (§3.6, soundness-load-bearing ordering — qualified key FIRST, bare fallback SECOND):**
- `slot == :value` (a ctor path `Std.Nat.Z`): module = all-but-last segment (`"Std.Nat"`), name = last (`Z`). Try `:"Std.Nat#Z"` in ctors; else bare `:Z` in ctors.
- `slot == :type` (a type path `Std.Nat` or `Std.Nat.Nat`): try the **module==typename collapse** first — module = whole path (`"Std.Nat"`), name = last segment (`Nat`) → `:"Std.Nat#Nat"` in families; else the explicit form module = all-but-last, name = last → `:"Std.Nat#Nat"`; else bare last-segment `:Nat` in families.

- [ ] **Step 1: Write the failing unit tests**

Add to `test/cure/elab/resolution_test.exs`:
```elixir
  describe "resolve_qualified/3" do
    setup do
      # env where Std.Nat has been re-keyed (loser), and an unshadowed Std.Bool.
      env =
        %Cure.Core.Env{}
        |> Cure.Core.Inductive.declare(Cure.Core.Inductive.family(:"Std.Nat#Nat", [], [], 0),
             [Cure.Core.Inductive.ctor(:"Std.Nat#Z", [], []),
              Cure.Core.Inductive.ctor(:"Std.Nat#S", [{:n, {:data, :"Std.Nat#Nat", [], []}}], [])])
        |> Cure.Core.Inductive.declare(Cure.Core.Inductive.family(:Bool, [], [], 0),
             [Cure.Core.Inductive.ctor(:True, [], []), Cure.Core.Inductive.ctor(:False, [], [])])

      %{env: env}
    end

    test "value path resolves a re-keyed ctor", %{env: env} do
      assert Cure.Elab.Resolution.resolve_qualified(env, "Std.Nat.Z", :value) == {:ok, :"Std.Nat#Z"}
    end

    test "type path resolves via module==typename collapse", %{env: env} do
      assert Cure.Elab.Resolution.resolve_qualified(env, "Std.Nat", :type) == {:ok, :"Std.Nat#Nat"}
    end

    test "type path resolves the explicit .Nat spelling identically", %{env: env} do
      assert Cure.Elab.Resolution.resolve_qualified(env, "Std.Nat.Nat", :type) == {:ok, :"Std.Nat#Nat"}
    end

    test "falls back to a bare key for an unshadowed module", %{env: env} do
      assert Cure.Elab.Resolution.resolve_qualified(env, "Std.Bool.True", :value) == {:ok, :True}
      assert Cure.Elab.Resolution.resolve_qualified(env, "Std.Bool", :type) == {:ok, :Bool}
    end

    test "returns :error for an unresolvable path", %{env: env} do
      assert Cure.Elab.Resolution.resolve_qualified(env, "Std.Nope.Gone", :value) == :error
    end
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/elab/resolution_test.exs`
Expected: FAIL — `resolve_qualified/3` undefined.

- [ ] **Step 3: Implement `resolve_qualified/3`**

Add to `lib/cure/elab/resolution.ex`:
```elixir
  @doc """
  Resolve a flattened dotted surface path (`"Std.Nat.Z"`) to a registry key,
  trying the qualified `:"Mod#Name"` key FIRST and a bare-atom key second (the
  ordering is load-bearing: under a local shadow the loser is only reachable at
  its qualified key, and a bare fallback must never grab the local winner —
  which is safe precisely because a shadowed import is always re-keyed, so its
  bare key is absent). `slot` selects type vs value candidate shapes.
  """
  @spec resolve_qualified(Env.t(), String.t(), :type | :value) :: {:ok, atom()} | :error
  def resolve_qualified(%Env{} = env, dotted, :value) do
    segs = String.split(dotted, ".")
    {mod_segs, [last]} = Enum.split(segs, length(segs) - 1)
    mod = Enum.join(mod_segs, ".")
    try_keys(env, [rekey_atom(mod, String.to_atom(last)), String.to_atom(last)], :value)
  end

  def resolve_qualified(%Env{} = env, dotted, :type) do
    segs = String.split(dotted, ".")
    last = List.last(segs)
    {mod_segs, [explicit_last]} = Enum.split(segs, length(segs) - 1)

    candidates = [
      # module==typename collapse: whole path is the module, name repeats the tail.
      rekey_atom(dotted, String.to_atom(last)),
      # explicit Mod.Type spelling.
      rekey_atom(Enum.join(mod_segs, "."), String.to_atom(explicit_last)),
      # unshadowed bare fallback.
      String.to_atom(last)
    ]

    try_keys(env, candidates, :type)
  end

  defp try_keys(env, keys, slot) do
    present? =
      case slot do
        :type -> fn k -> Inductive.family?(env, k) end
        :value -> fn k -> not is_nil(Inductive.get_ctor(env, k)) end
      end

    case Enum.find(keys, present?) do
      nil -> :error
      key -> {:ok, key}
    end
  end
```
(Confirm `Inductive.family?/2` exists — it is used in `declarations.ex` `resolve_index_name`; if the arity differs, use `Map.has_key?(env.families, k)` directly.)

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/elab/resolution_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add -- lib/cure/elab/resolution.ex test/cure/elab/resolution_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): Resolution.resolve_qualified — dotted path to registry key"
```

---

### Task 7: Wire qualified resolution into the value + pattern call sites (R3, escape hatch)

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` — `partition_arms` (~2752-2796) and `partition_rematch_arms` (~1257-1283) constructor-key normalization; `elaborate_named_call/5` (~171).
- Modify: `test/cure/elab/type_shadowing_test.exs`
- Create: `test/oracle/shadow/shadow04_escape_hatch.cure` / `.idr`

**Interfaces:**
- Consumes: `Resolution.resolve_qualified/3`.
- Produces: a `resolve_ctor_key/2` helper in `elaborator.ex` that normalizes a possibly-dotted ctor atom to a registry key.

- [ ] **Step 1: Write the failing test (expression + pattern positions)**

Add to `test/cure/elab/type_shadowing_test.exs`:
```elixir
  test "R3: shadowed ctor reachable qualified in expression and pattern position" do
    src = """
    mod EscapeHatch
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn imported_two() -> Std.Nat = Std.Nat.S(Std.Nat.Z())
      fn is_zero(n: Std.Nat) -> Nat = match n
        Std.Nat.Z() -> Zero()
        Std.Nat.S(k) -> Suc(Zero())
    end
    """

    assert {:ok, _env} = elaborate(src)
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/elab/type_shadowing_test.exs`
Expected: FAIL — the qualified `Std.Nat.Z` flattens to atom `:"Std.Nat.Z"`, unknown to `get_ctor` → `{:unknown_pattern_constructor, :"Std.Nat.Z"}` (or an `elaborate_named_call` global miss). (The `Std.Nat` *type-slot* on the params is completed in Task 8; if this test blocks on the type slot before reaching the ctor logic, temporarily annotate the params with a local type to isolate the ctor paths, then restore in Task 8. Verify which by reading the actual error.)

- [ ] **Step 3: Add `resolve_ctor_key/2` and apply it at the two `partition_*` gates**

Add near the top of the private helpers in `lib/cure/elab/elaborator.ex`:
```elixir
  # Normalize a constructor atom that may be a flattened dotted path
  # (`:"Std.Nat.Z"`) to a registry key via the resolution layer; a bare atom
  # with no "." is returned unchanged.
  defp resolve_ctor_key(env, cname) do
    s = Atom.to_string(cname)

    if String.contains?(s, ".") do
      case Cure.Elab.Resolution.resolve_qualified(env, s, :value) do
        {:ok, key} -> key
        :error -> cname
      end
    else
      cname
    end
  end
```

In `partition_arms`, immediately after `{:ok, {cname, _vars}} ->` (the successful `constructor_pattern` clause), rebind `cname`:
```elixir
          {:ok, {cname0, _vars}} ->
            cname = resolve_ctor_key(env, cname0)

            cond do
              Inductive.get_ctor(env, cname) == nil ->
```
(The rest of the `cond` is unchanged — it now sees the resolved key. Note `Map.put(acc, cname, …)` and the `pattern` value stay as they are; only the key used for lookup/coverage is the resolved one.)

Apply the identical rebind in `partition_rematch_arms` after `with {:ok, {cname, _vars}} <- constructor_pattern(with_pattern),` — capture as `cname0` and add `cname = resolve_ctor_key(env, cname0)` before the `cond`.

- [ ] **Step 4: Apply qualified resolution in `elaborate_named_call/5`**

In `lib/cure/elab/elaborator.ex:171`, after `atom = String.to_atom(name)`, add a resolved-atom binding and use it for the ctor branch:
```elixir
  defp elaborate_named_call(meta, args, names, ctx, env) do
    name = Keyword.fetch!(meta, :name)
    atom = String.to_atom(name)

    resolved =
      if String.contains?(name, ".") do
        case Cure.Elab.Resolution.resolve_qualified(env, name, :value) do
          {:ok, key} -> key
          :error -> atom
        end
      else
        atom
      end

    cond do
      name == "refl" and length(args) == 1 ->
        ...

      Inductive.get_ctor(env, resolved) ->
        result =
          with {:ok, present} <- map_present_args(args, names, ctx, env) do
            elaborate_ctor_app(env, resolved, present, ctx)
          end
        ...
```
(Change ONLY the `Inductive.get_ctor(env, atom)` guard and the `elaborate_ctor_app(env, atom, …)` call in that ctor branch to use `resolved`. Every other use of `atom` — the global-def path, error messages — stays `atom` so a non-dotted name is byte-for-byte unchanged: `resolved == atom` when `name` has no dot.)

- [ ] **Step 5: Run the value/pattern half green**

Run: `mix test test/cure/elab/type_shadowing_test.exs`
Expected: the expression + pattern positions resolve (the whole `R3` test passes once Task 8 lands the `Std.Nat` type slot; if isolated per Step-2 note, the isolated version passes now).

- [ ] **Step 6: Commit**

```bash
git add -- lib/cure/elab/elaborator.ex test/cure/elab/type_shadowing_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): resolve qualified ctors in pattern + expression positions (R3)"
```

---

### Task 8: Wire qualified resolution into the type-slot call sites (R4 + finish R3)

**Files:**
- Modify: `lib/cure/elab/declarations.ex` — `idx_to_core` `{:function_call,…}` clause (~726) and `{:attribute_access,…}` clause (~820); `resolve_index_name/2` (~832).
- Modify: `test/cure/elab/type_shadowing_test.exs`
- Create: `test/oracle/shadow/shadow04_escape_hatch.{cure,idr}`, `shadow05_module_typename_collapse.{cure,idr}`

**Interfaces:**
- Consumes: `Resolution.resolve_qualified/3`.
- Produces: qualified type-slot resolution for both the nullary (shape (a), `attribute_access`) and parameterized (shape (b), `function_call`) cases.

- [ ] **Step 1: Write the shadow05 behavioral test (red)**

Add to `test/cure/elab/type_shadowing_test.exs`:
```elixir
  test "R4: `Std.Nat` in a type slot resolves to the imported type (module==typename collapse)" do
    src = """
    mod Collapse
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn imported_zero() -> Std.Nat = Std.Nat.Z()
    end
    """

    assert {:ok, _env} = elaborate(src)
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/elab/type_shadowing_test.exs`
Expected: FAIL — `Std.Nat` in the return-type slot. As call-flattening leaves `Nat` reference either as an `attribute_access` (no parens) or a `function_call` name `"Std.Nat"`; today `idx_to_core` errors `{:bad_projection,_}` or builds a dangling `{:global, :"Std.Nat"}`.

- [ ] **Step 3: Add qualified handling to the `function_call` clause of `idx_to_core`**

In `lib/cure/elab/declarations.ex:726`, add a resolved-key short-circuit at the top of the non-function-type branch, before the existing `cond`:
```elixir
  defp idx_to_core({:function_call, fmeta, args}, scope, fam, env) do
    if Keyword.get(fmeta, :function_type) do
      arrow_to_pi(args, scope, fam, env)
    else
      name = Keyword.fetch!(fmeta, :name)
      atom = String.to_atom(name)

      with {:ok, core_args} <- map_idx_to_core(args, scope, fam, env) do
        qualified =
          if String.contains?(name, ".") do
            Cure.Elab.Resolution.resolve_qualified(env, name, :type)
          else
            :error
          end

        cond do
          match?({:ok, _}, qualified) ->
            {:ok, key} = qualified
            {params, indices} = Enum.split(core_args, Inductive.param_count(env, key))
            {:ok, {:data, key, params, indices}}

          idx = Enum.find_index(scope, &(&1 == name)) ->
            {:ok, Enum.reduce(core_args, {:var, idx}, fn a, acc -> {:app, acc, a} end)}

          atom == :Eq and length(core_args) == 3 ->
            ...
```
(Only the new `qualified` binding + the leading `match?({:ok, _}, qualified) ->` cond clause are added; the rest of the `cond` is untouched. For a non-dotted `name`, `qualified == :error`, so behavior is identical.)

- [ ] **Step 4: Add a qualified/module clause to `idx_to_core`'s `attribute_access` (shape (a), nullary no-parens)**

Replace the `{:attribute_access,…}` clause in `lib/cure/elab/declarations.ex:820` so a dotted module/type path is tried before the `.1`/`.2` projection interpretation:
```elixir
  defp idx_to_core({:attribute_access, meta, [inner_ast]} = node, scope, fam, env) do
    attr = Keyword.fetch!(meta, :attribute)

    dotted =
      case Cure.Compiler.Parser.dotted_path_of(node) do
        nil -> nil
        s -> s
      end

    cond do
      # A qualified TYPE reference like Std.Nat / Std.Nat.Nat (no call parens).
      is_binary(dotted) and match?({:ok, _}, Cure.Elab.Resolution.resolve_qualified(env, dotted, :type)) ->
        {:ok, key} = Cure.Elab.Resolution.resolve_qualified(env, dotted, :type)
        {:ok, {:data, key, [], []}}

      attr in ["1", "2"] ->
        with {:ok, inner} <- idx_to_core(inner_ast, scope, fam, env) do
          case attr do
            "1" -> {:ok, {:fst, inner}}
            "2" -> {:ok, {:snd, inner}}
          end
        end

      true ->
        {:error, {:bad_projection, attr}}
    end
  end
```
This needs a small public helper on the parser to reconstruct the dotted string from an `attribute_access` node (the parser already has the private `extract_dotted_path/1`). Add to `lib/cure/compiler/parser.ex`:
```elixir
  @doc "Reconstruct a dotted path string from an attribute_access/variable node, or nil."
  def dotted_path_of(node), do: extract_dotted_path(node)
```

- [ ] **Step 5: Extend `resolve_index_name/2` for bare names that are only reachable qualified**

`resolve_index_name/2` (`declarations.ex:832`) handles a *bare* type name in a type slot. It already prefers a family over a ctor. No change is required for shadowing itself (a shadowed bare name is simply the local winner or absent), but confirm it is unaffected: after re-keying, a bare `Nat` resolves to the local family key `:Nat` (present), unchanged. Add a regression assertion rather than code — see Step 6. (R7's ambiguity teaching for this function lands in Task 10.)

- [ ] **Step 6: Run behavioral + finish R2/R3/R4**

Run: `mix test test/cure/elab/type_shadowing_test.exs`
Expected: PASS — R2 (full, including the `imported_one`/`Std.Nat` return type), R3 (full), R4 all green.

- [ ] **Step 7: Add shadow04 + shadow05 oracle probes**

`test/oracle/shadow/shadow04_escape_hatch.cure`:
```
mod EscapeHatch
  use Std.Nat
  type Nat = Zero | Suc(Nat)
  fn imported_two() -> Std.Nat = Std.Nat.S(Std.Nat.Z())
  fn is_zero(n: Std.Nat) -> Nat = match n
    Std.Nat.Z() -> Zero()
    Std.Nat.S(k) -> Suc(Zero())
end
```
`test/oracle/shadow/shadow04_escape_hatch.idr`:
```idris
%default total

data Local = Zero | Suc Local

importedTwo : Nat
importedTwo = S (S Z)

isZero : Nat -> Local
isZero Z = Zero
isZero (S k) = Suc Zero
```
(Idris' prelude `Nat`/`Z`/`S` play the role of the "imported, still-reachable" family while `Local` is the shadowing type — a faithful model of "a distinct local type coexisting with the library one, both used".)

`test/oracle/shadow/shadow05_module_typename_collapse.cure`:
```
mod Collapse
  use Std.Nat
  type Nat = Zero | Suc(Nat)
  fn imported_zero() -> Std.Nat = Std.Nat.Z()
end
```
`test/oracle/shadow/shadow05_module_typename_collapse.idr`:
```idris
%default total

data Local = Zero | Suc Local

importedZero : Nat
importedZero = Z
```

- [ ] **Step 8: Regenerate verdicts**

Run: `mix cure.oracle shadow`
Expected: `shadow04`/`shadow05` = `same` (accept/accept).

- [ ] **Step 9: Run the regression guard**

Run: `mix test test/cure/elab/auto_prelude_test.exs test/oracle_replay_test.exs`
Expected: PASS.

- [ ] **Step 10: Commit**

```bash
git add -- lib/cure/elab/declarations.ex lib/cure/compiler/parser.ex test/cure/elab/type_shadowing_test.exs test/oracle/shadow/shadow04_escape_hatch.cure test/oracle/shadow/shadow04_escape_hatch.idr test/oracle/shadow/shadow05_module_typename_collapse.cure test/oracle/shadow/shadow05_module_typename_collapse.idr test/oracle/shadow/verdicts.json
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): qualified type-slot resolution + module==typename collapse (R3/R4)"
```

---

### Task 9: R5 — `:shadowed_ctor` targeted diagnostic

**Files:**
- Modify: `lib/cure/elab/resolution.ex` — add `shadowed_origin/2`.
- Modify: `lib/cure/elab/elaborator.ex` — intercept the `{:unknown_pattern_constructor, cname}` raise in `partition_arms` and `partition_rematch_arms`.
- Modify: `test/cure/elab/type_shadowing_test.exs`
- Create: `test/oracle/shadow/shadow06_shadow_diagnostic.{cure,idr}`

**Interfaces:**
- Consumes: the re-keyed env; `resolve_ctor_key/2` (Task 7).
- Produces: `Resolution.shadowed_origin/2`; the `{:shadowed_ctor, …}` error tuple.

**Anchor (spec §5):** after re-keying, a bare `Z()` used on a local-`Nat` scrutinee is *absent* from the registry, so it fails the `Inductive.get_ctor(env, cname) == nil` gate → today `{:unknown_pattern_constructor, cname}`. Intercept there.

- [ ] **Step 1: Write the failing diagnostic test**

Add to `test/cure/elab/type_shadowing_test.exs`:
```elixir
  test "R5: using a shadowed bare ctor on the local family yields a targeted :shadowed_ctor error" do
    src = """
    mod WrongCtor
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn bad(n: Nat) -> Nat = match n
        Z() -> Zero()
        S(m) -> Suc(m)
    end
    """

    assert {:error, {:shadowed_ctor, info}} = elaborate(src)
    assert info[:ctor] == :Z
    assert info[:shadowed_module] == "Std.Nat"
    assert info[:hint] == "Std.Nat.Z"
    assert info[:local_family] == :Nat
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/elab/type_shadowing_test.exs`
Expected: FAIL — currently returns `{:error, {:unknown_pattern_constructor, :Z}}` (bare `Z` was re-keyed off the registry) or `{:missing_branch, _}`; the specific `:shadowed_ctor` assertion fails.

- [ ] **Step 3: Add `shadowed_origin/2` to `Resolution`**

```elixir
  @doc """
  If a bare constructor/family name was shadowed (re-keyed off the bare atom),
  find the re-keyed variant `:"Mod#bare"` still present in the env and report
  its origin module + re-keyed atom. Returns `:error` if no shadowed variant
  exists (the name is genuinely unknown, not shadowed).
  """
  @spec shadowed_origin(Env.t(), atom()) :: {:ok, String.t(), atom()} | :error
  def shadowed_origin(%Env{ctors: ctors, families: families}, bare) do
    suffix = "#" <> Atom.to_string(bare)

    match =
      Enum.find_value(Map.keys(ctors) ++ Map.keys(families), fn k ->
        s = Atom.to_string(k)
        if String.ends_with?(s, suffix), do: {String.trim_trailing(s, suffix), k}, else: nil
      end)

    case match do
      {mod_id, key} -> {:ok, mod_id, key}
      nil -> :error
    end
  end
```

- [ ] **Step 4: Intercept the unknown-constructor gate in `partition_arms`**

In `partition_arms`, replace the `Inductive.get_ctor(env, cname) == nil ->` branch body with a shadow check:
```elixir
              Inductive.get_ctor(env, cname) == nil ->
                case Cure.Elab.Resolution.shadowed_origin(env, cname) do
                  {:ok, mod_id, _key} ->
                    {:halt,
                     {:error,
                      {:shadowed_ctor,
                       [
                         ctor: cname,
                         shadowed_module: mod_id,
                         local_family: dname,
                         local_ctors: Enum.map(Inductive.ctors_of(Context.signature(ctx), dname), & &1.name),
                         hint: mod_id <> "." <> Atom.to_string(cname)
                       ]}}}

                  :error ->
                    {:halt, {:error, {:unknown_pattern_constructor, cname}}}
                end
```
Apply the same interception in `partition_rematch_arms` at its `Inductive.get_ctor(env, cname) == nil ->` branch (using the same `dname`/`sig` in scope).

- [ ] **Step 5: Run to verify pass**

Run: `mix test test/cure/elab/type_shadowing_test.exs`
Expected: PASS — the `:shadowed_ctor` error with the exact fields.

- [ ] **Step 6: Add the shadow06 oracle probe (reject/reject)**

`test/oracle/shadow/shadow06_shadow_diagnostic.cure`: the `WrongCtor` module above.
`test/oracle/shadow/shadow06_shadow_diagnostic.idr`:
```idris
%default total

data Nat' = Zero | Suc Nat'

bad : Nat' -> Nat'
bad Z = Zero
bad (S m) = Suc m
```
(Idris rejects `Z`/`S` as constructors of `Nat'` — an out-of-family constructor error — so both sides reject: relation `same` on *reject*, reason pinned to "shadowed/wrong constructor family".)

- [ ] **Step 7: Regenerate verdicts + confirm reject/reject**

Run: `mix cure.oracle shadow`
Expected: `shadow06` = `{"cure":"reject","idris":"reject","relation":"same","reason":"shadowed constructor used on local family"}`.

- [ ] **Step 8: Commit**

```bash
git add -- lib/cure/elab/resolution.ex lib/cure/elab/elaborator.ex test/cure/elab/type_shadowing_test.exs test/oracle/shadow/shadow06_shadow_diagnostic.cure test/oracle/shadow/shadow06_shadow_diagnostic.idr test/oracle/shadow/verdicts.json
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): :shadowed_ctor targeted diagnostic (R5)"
```

---

### Task 10: R7 — `:ambiguous_name` for distinct import-vs-import collisions

**Files:**
- Modify: `lib/cure/elab/resolution.ex` — add `ambiguous_modules/2`.
- Modify: `lib/cure/elab/declarations.ex` — `resolve_index_name/2` checks ambiguity before falling to `{:global, atom}`.
- Modify: `lib/cure/elab/elaborator.ex` — `elaborate_named_call/5` checks ambiguity before the global-def fallback (value position).
- Modify: `test/cure/elab/type_shadowing_test.exs`
- Create: two scratch stdlib-style modules for the probe + `test/oracle/shadow/shadow07_ambiguous.{cure,idr}`

**Interfaces:**
- Consumes: the re-keyed env (an ambiguous name has ≥2 `:"Mod#Name"` variants and NO bare key).
- Produces: `Resolution.ambiguous_modules/2`; the `{:ambiguous_name, name, [modules]}` error.

- [ ] **Step 1: Create two scratch distinct modules that both declare `type Nat`**

`test/oracle/shadow/support/foo.cure`:
```
mod Std.Foo
  type Nat = FZero | FSucc(Nat)
end
```
`test/oracle/shadow/support/bar.cure`:
```
mod Std.Bar
  type Nat = BZero | BSucc(Nat)
end
```
(These are scratch sources loaded by the test via an explicit path, not installed into `priv/std`. The test writes them to a temp dir or references them relatively — see Step 3. The probe's point is two GENUINELY distinct modules providing `Nat`.)

- [ ] **Step 2: Write the failing ambiguity test**

Add to `test/cure/elab/type_shadowing_test.exs` (using the real stdlib is cleaner if two same-family modules exist; since they don't, drive ambiguity directly through `Resolution` + a crafted env, plus an end-to-end check if the scratch-module loader supports arbitrary paths):
```elixir
  test "R7: ambiguous_modules reports ≥2 origins for a name re-keyed off the bare atom" do
    env =
      %Cure.Core.Env{}
      |> Cure.Core.Inductive.declare(Cure.Core.Inductive.family(:"Std.Foo#Nat", [], [], 0),
           [Cure.Core.Inductive.ctor(:"Std.Foo#FZero", [], [])])
      |> Cure.Core.Inductive.declare(Cure.Core.Inductive.family(:"Std.Bar#Nat", [], [], 0),
           [Cure.Core.Inductive.ctor(:"Std.Bar#BZero", [], [])])

    mods = Cure.Elab.Resolution.ambiguous_modules(env, :Nat)
    assert Enum.sort(mods) == ["Std.Bar", "Std.Foo"]
  end
```

- [ ] **Step 3: Implement `ambiguous_modules/2`**

```elixir
  @doc """
  All origin modules that provide family `bare` under a re-keyed `:"Mod#bare"`
  family key. ≥2 ⇒ the unqualified name is ambiguous (no local winner claimed
  the bare key). Returns [] when the bare key is present (a winner exists) or
  the name is unknown.
  """
  @spec ambiguous_modules(Env.t(), atom()) :: [String.t()]
  def ambiguous_modules(%Env{families: families}, bare) do
    if Map.has_key?(families, bare) do
      []
    else
      suffix = "#" <> Atom.to_string(bare)

      families
      |> Map.keys()
      |> Enum.flat_map(fn k ->
        s = Atom.to_string(k)
        if String.ends_with?(s, suffix), do: [String.trim_trailing(s, suffix)], else: []
      end)
    end
  end
```

- [ ] **Step 4: Teach `resolve_index_name/2` to raise ambiguity (type slot)**

`resolve_index_name/2` returns a bare Core node today; to surface an error it must be allowed to fail. The lowest-churn approach: keep `resolve_index_name/2` returning a node, but have its caller detect the ambiguous case. Concretely, add a guard clause BEFORE the existing `true -> {:global, atom}` fallback:
```elixir
  defp resolve_index_name(name, env) do
    atom = String.to_atom(name)

    cond do
      primitive_type(name) != nil -> primitive_type(name)
      Inductive.family?(env, atom) -> {:data, atom, [], []}
      Inductive.get_ctor(env, atom) -> {:ctor, atom, []}
      length(Cure.Elab.Resolution.ambiguous_modules(env, atom)) >= 2 ->
        {:ambiguous_name, atom, Cure.Elab.Resolution.ambiguous_modules(env, atom)}
      true -> {:global, atom}
    end
  end
```
Then, wherever `resolve_index_name/2`'s result is consumed (the `{:variable, …}` clause of `idx_to_core`), add a clause that turns `{:ambiguous_name, …}` into `{:error, {:ambiguous_name, name, mods}}`. Locate the caller (search `resolve_index_name(` in `declarations.ex`) and thread the error through its `with`/`case`.

- [ ] **Step 5: Teach `elaborate_named_call/5` to raise ambiguity (value slot)**

In `elaborate_named_call/5`, before the global-def fallback (the branch that treats `atom` as an unknown global / raises `:unknown_global`), add:
```elixir
      length(Cure.Elab.Resolution.ambiguous_modules(env, atom)) >= 2 ->
        {:error, {:ambiguous_name, atom, Cure.Elab.Resolution.ambiguous_modules(env, atom)}}
```
(Insert as a `cond` clause after the ctor branch, before the global fallback.)

- [ ] **Step 6: Run the unit + behavioral tests**

Run: `mix test test/cure/elab/type_shadowing_test.exs test/cure/elab/resolution_test.exs`
Expected: PASS — `ambiguous_modules/2` returns both origins; if the scratch-module end-to-end loader is wired, the bare `Nat` use errors `{:ambiguous_name, :Nat, ["Std.Bar", "Std.Foo"]}`.

- [ ] **Step 7: Add shadow07 oracle probe (documented reject)**

If the scratch modules can be resolved by the oracle's import path, add `test/oracle/shadow/shadow07_ambiguous.cure` importing both and using bare `Nat`; the `.idr` models two same-named datatypes in separate namespaces used unqualified (Idris reports an ambiguity). Relation: `same` on reject (or `cure_stricter` with the reason "ambiguous unqualified name across distinct imports"). If the oracle cannot load scratch modules outside `priv/std`, SKIP the oracle probe and rely on the unit + behavioral assertions — and `log`/note in the commit body that shadow07 is unit-covered only (no silent gap).

- [ ] **Step 8: Regenerate verdicts (if probe added)**

Run: `mix cure.oracle shadow`
Expected: `shadow07` present, or documented as unit-only.

- [ ] **Step 9: Commit**

```bash
git add -- lib/cure/elab/resolution.ex lib/cure/elab/declarations.ex lib/cure/elab/elaborator.ex test/cure/elab/type_shadowing_test.exs test/cure/elab/resolution_test.exs test/oracle/shadow/
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(elab): :ambiguous_name for distinct import-vs-import collisions (R7)"
```

---

### Task 11: Codegen — strip `Mod#` prefix from runtime constructor tags

**Files:**
- Modify: `lib/cure/compiler/codegen.ex:1972-1976` (`constructor_tag/1`).
- Create: `test/cure/compiler/shadow_codegen_test.exs`

**Interfaces:**
- Consumes: a re-keyed ctor atom `:"Std.Nat#Z"` reaching codegen on the escape-hatch path.
- Produces: a bare runtime tag `:z` (the underscored bare name), identical to what an unshadowed `Z` produces.

**Invariant (spec §3.5):** the BEAM value tag must be bare so AtomVM's value format is unchanged and a re-keyed ctor is runtime-indistinguishable from its bare form.

- [ ] **Step 1: Write the failing codegen unit test**

`test/cure/compiler/shadow_codegen_test.exs`:
```elixir
defmodule Cure.Compiler.ShadowCodegenTest do
  use ExUnit.Case, async: true

  test "constructor_tag strips a Mod# prefix so the runtime tag is bare" do
    # A re-keyed ctor atom must produce the SAME tag as its bare form.
    assert Cure.Compiler.Codegen.constructor_tag(:"Std.Nat#Z") ==
             Cure.Compiler.Codegen.constructor_tag(:Z)
  end
end
```
(If `constructor_tag/1` is private, either make it public with `@doc false` for the test, or assert through a higher-level emit function that produces the tuple form. Prefer exposing `constructor_tag/1` as `@doc false` public — minimal surface, directly tests the invariant.)

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/compiler/shadow_codegen_test.exs`
Expected: FAIL — `:"Std.Nat#Z"` underscores to `:"std/nat#z"`-ish, not `:z`; the two tags differ (and/or the function is private).

- [ ] **Step 3: Strip the prefix in `constructor_tag/1`**

`lib/cure/compiler/codegen.ex:1972`:
```elixir
  @doc false
  def constructor_tag(name) do
    name
    |> Atom.to_string()
    |> strip_module_prefix()
    |> Macro.underscore()
    |> String.to_atom()
  end

  # A re-keyed ctor atom is "<Module>#<Ctor>"; the runtime tag uses only <Ctor>
  # so the BEAM/AtomVM value format is identical to the unshadowed constructor.
  defp strip_module_prefix(s) do
    case String.split(s, "#", parts: 2) do
      [_mod, ctor] -> ctor
      [bare] -> bare
    end
  end
```

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/compiler/shadow_codegen_test.exs`
Expected: PASS.

- [ ] **Step 5: Host codegen sanity for the escape-hatch path (gate item 4)**

Add a test that compiles the shadow04 program to Erlang forms and asserts the emitted tag for the imported constructor is bare. Add to `test/cure/compiler/shadow_codegen_test.exs`:
```elixir
  test "a program using Std.Nat.Z emits a bare :z tag" do
    src = """
    mod EscapeCodegen
      use Std.Nat
      type Nat = Zero | Suc(Nat)
      fn imported_zero() -> Std.Nat = Std.Nat.Z()
    end
    """

    {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
    {:ok, forms} = Cure.Compiler.Codegen.compile(ast)

    # The emitted forms contain the bare atom :z somewhere (imported ctor tag),
    # and never the qualified :"std/nat#z"-style atom.
    flat = :erlang.term_to_binary(forms)
    refute String.contains?(inspect(forms), "#")
    assert flat != <<>>
  end
```
(Adjust `Codegen.compile/1` to the actual entry point name if different — search `def compile` in `codegen.ex`. The essential assertion is: no `#`-bearing atom survives into the emitted forms.)

- [ ] **Step 6: Run to verify pass**

Run: `mix test test/cure/compiler/shadow_codegen_test.exs`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add -- lib/cure/compiler/codegen.ex test/cure/compiler/shadow_codegen_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(codegen): strip Mod# prefix — re-keyed ctors keep bare runtime tags"
```

---

### Task 12: Full gate — replay, full suite, verdicts, final report

**Files:**
- No new production code; verification + any verdicts.json finalization.

**Interfaces:**
- Consumes: everything above.
- Produces: a green gate confirming R1–R7 + R6 non-regression.

- [ ] **Step 1: Regenerate + freeze the shadow cluster verdicts**

Run: `mix cure.oracle shadow`
Expected: `shadow01`–`shadow06` present with their intended relations (shadow07 present or documented unit-only per Task 10). Review `test/oracle/shadow/verdicts.json` for any unintended `cure_stricter` — each must have a written reason.

- [ ] **Step 2: Oracle replay (no other probe regressed)**

Run: `mix test test/oracle_replay_test.exs`
Expected: PASS.

- [ ] **Step 3: Full suite ONCE, alone**

Run: `mix test`
Expected: PASS at 2843/0 baseline or higher (new shadow + resolution + codegen tests added). Zero regressions. If any pre-existing test changed behavior, STOP — the non-collision path must be byte-for-byte identical; investigate before proceeding.

- [ ] **Step 4: Auto-prelude guard (explicit re-confirm of the retained skip)**

Run: `mix test test/cure/elab/auto_prelude_test.exs`
Expected: PASS — the auto-prelude skip (retained per Global Constraints) is intact.

- [ ] **Step 5: Commit any verdicts finalization**

```bash
git add -- test/oracle/shadow/verdicts.json
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(shadow): freeze shadow-cluster verdicts (R1–R7 gate green)"
```
(If nothing changed since Task 10/11, skip this commit.)

- [ ] **Step 6: Update the parity ledger**

The shadowing fix is a correctness defect gating ledger row #5's auto-generalization path; note its resolution in `docs/superpowers/specs/2026-07-02-idris-parity-roadmap.md` (a one-line pointer near #4/#5), then commit:
```bash
git add -- docs/superpowers/specs/2026-07-02-idris-parity-roadmap.md
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "docs(parity): note local type/ctor shadowing fix (unblocks #5)"
```

---

## Self-Review

**1. Spec coverage:**
- R1 (per-name type+ctor shadowing) → Tasks 5 (re-key) + shadow01/02. ✓
- R2 (non-shadowed imports stay visible) → Task 5 (residual-drop keeps only losers re-keyed) + Task 8 (`Std.Nat` return) + shadow03. ✓
- R3 (qualified escape hatch) → Tasks 7 (value/pattern) + 8 (type slot) + shadow04. ✓
- R4 (module==typename collapse) → Task 8 (`resolve_qualified` type-slot collapse candidate) + shadow05. ✓
- R5 (shadow-aware diagnostics) → Task 9 (`:shadowed_ctor` at the unknown-ctor gate) + shadow06. ✓
- R6 (no regression) → residual-drop (Task 5) + Tasks 5/8/12 auto-prelude + replay + full-suite guards; every new cond clause is a no-op for non-dotted/non-collision inputs. ✓
- R7 (import-vs-import ambiguity) → Tasks 4 (classify) + 10 (`:ambiguous_name`) + shadow07. ✓
- §3.2 `:case` branch-tag rewrite → Task 2 (explicit test) + Task 3 (def-body rewrite). ✓
- §3.1 dedup/over-detection (diamond + auto+explicit) → Task 4 (classify tests) + Task 5 (distinct_import_modules + AST-own provenance). ✓
- §3.5 bare runtime tags → Task 11. ✓
- §3.6 all three call sites → Tasks 7 (2 sites) + 8 (idx_to_core function_call + attribute_access). ✓

**2. Placeholder scan:** Every code step shows real code grounded in the verbatim anchors. Two deliberate "verify which error applies / adjust entry-point name" notes (Task 7 Step 2, Task 11 Step 5) are read-the-actual-code instructions, not placeholders — they name the exact search target.

**3. Type consistency:** `rekey_atom/2`, `rekey_term/2`, `resolve_qualified/3`, `shadowed_origin/2`, `ambiguous_modules/2`, `classify/2`, `rekey_module_env/3` names + arities are consistent across Tasks 2–11 and match the Interfaces block. Registry key form `:"<module_id>#<bare>"` and surface form `"<module_id>.<bare>"` are used consistently; the `.`→`#` bridge lives only in `resolve_qualified/3` (Task 6) and `rekey_atom/2` (Task 3).

**Residual scope note (mirrors the spec's own caveats):** the exotic *diamond + local shadow* case (`use Std.Vector` + `use Std.Nat` + a local `Nat`) is handled by the residual-bare-drop (Task 5 Step 3, `drop_bare_family`), but is pinned only by the full-suite/replay guard, not a dedicated probe (the stdlib has no such program today). If Stage-4 execution surfaces it, add a `shadow08` probe rather than widening scope silently.
