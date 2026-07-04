# Local type shadowing (types + constructors) with qualified escape hatch — design

**Date:** 2026-07-04
**Layer:** E (elaborator, `lib/cure/elab/*`) + a contained C-layer touch (codegen runtime tags). **Kernel/TCB (`lib/cure/core/*`) is NOT modified.**
**Status:** design approved (Approach B). This spec is the source of truth for the implementation plan.

## 1. Problem

A module may declare its own type whose name collides with an imported (or auto-imported) family. Value/function shadowing already works (local defs win, last-writer in the `defs` map). **Type + constructor shadowing does not fully work:** a local `type Nat = Zero | Suc(Nat)` shadows correctly in *declarations and signatures*, but the `match` exhaustiveness/coverage checker still resolves the scrutinee's family to the imported namesake's constructor set, producing `{:error, {:missing_branch, :S}}`.

### 1.1 Reproduction (confirmed)

```
mod ExplicitShadow
  use Std.Nat                       # imports family Nat = Z | S
  type Nat = Zero | Suc(Nat)        # local shadow
  fn add(a: Nat, b: Nat) -> Nat = match a
    Zero() -> b
    Suc(m) -> Suc(add(m, b))
end
```
`Cure.Elab.Program.elaborate/1` → `{:error, {:missing_branch, :S}}`.

The auto-prelude case (no explicit `use`) already works, because `program.ex`'s
`auto_prelude_imports/1` skips auto-importing `Std.Nat` when the module declares
its own `type Nat` (collision-avoidance keyed on `declared_type_names`). That
skip does **not** cover an explicit `use`, nor import-vs-import collisions.

### 1.2 Root cause (confirmed by source read)

The registry keys families and constructors by **bare atom**, and imports flatten
in with **zero provenance**:
- `program.ex` `import_source_env/2` elaborates each imported module's
  declarations into a fresh flat `Env` and `merge_env`s it under bare keys
  (`Std.Nat` → family `:Nat`, ctors `:Z`, `:S`).
- `Inductive.declare/3` (inductive.ex:183) does `Map.put(families, :Nat, …)` and,
  per ctor, `Map.put(ctor_to_family, cname, :Nat)`.
- `Inductive.ctors_of(env, :Nat)` (inductive.ex:275) returns **every** ctor whose
  `ctor_to_family[name] == :Nat`.

So after `use Std.Nat` registers `Z,S → :Nat` and the local `type Nat` registers
`Zero,Suc → :Nat` (overwriting `families[:Nat]` but **not** disowning `Z,S`), the
`ctor_to_family` map holds all four `{Zero,Suc,Z,S} → :Nat`. Coverage
(`elaborator.ex` `elaborate_rematch_branches`, line ~1293, and the sibling path
~1816) iterates `ctors_of(dname)` and demands a branch for each of the four →
`{:missing_branch, :S}`. **The imported constructors are never disowned from the
shadowed family's key.**

### 1.3 Faithfulness note (checked against upstream clones)

Idris2 (`Core/Name.idr`) keys definitions by namespaced `NS : Namespace -> Name ->
Name` (+ `Resolved Int`); Agda (`Syntax/Abstract/Name.hs`) uses `QName{qnameModule,
qnameName}` + a unique `NameId`. **Fully-qualified naming is the faithful
representation.** We deliberately adopt the *behavior-faithful* Approach B (below),
not the *representation-faithful* Approach A, because the operator's requirements
are purely about observable shadowing semantics and B keeps the TCB and the AtomVM
runtime value format untouched. What A would additionally buy — Agda-style
ambiguous same-named constructors disambiguated by expected type, self-describing
Core terms, nested namespaces — is explicitly out of scope (§7).

## 2. Requirements (observable behavior)

R1. **Per-name shadowing of both types and constructors.** A local `type Nat = Z |
    S` fully shadows imported `Nat` including its `Z`/`S` constructors: unqualified
    `Nat`/`Z`/`S` all resolve to the local family; the imported `Nat` is
    unreachable *unqualified*.
R2. **Non-shadowed imported names stay visible.** With local `type Nat = Zero |
    Suc`, unqualified `Nat` → local; unqualified `Z`/`S` (not redeclared locally)
    → still the imported `Std.Nat` constructors.
R3. **Qualified escape hatch always works:** `Std.Nat` in a type slot → the
    imported type; `Std.Nat.Z` in an expression/pattern → the imported
    constructor — regardless of any local shadow.
R4. **Module==typename collapse.** When a module `M`'s last path segment equals a
    type it declares (module `Std.Nat` declares `type Nat`), `Std.Nat` in a type
    slot resolves to that `Nat` type directly — the user need not write
    `Std.Nat.Nat`.
R5. **Shadow-aware diagnostics.** Using a shadowed constructor where the in-scope
    family is the local one yields a targeted error naming the shadowed origin and
    the correct qualified form — not a generic `{:foreign_ctor,_}` /
    `{:missing_branch,_}`.
R6. **No regression.** Every currently-green program elaborates unchanged; the
    non-collision path is byte-for-byte identical. The 2843/0 suite and the oracle
    replay stay green.

## 3. Approach B — resolution layer over bare atoms

The registry stays bare-atom keyed. A resolution layer in the elaborator maps
surface names → registry keys with shadowing precedence, and collisions trigger a
targeted re-keying of the shadowed import(s).

### 3.1 Collision detection

After the imported `Env` is built and the local declarations' family names are
known (both available in `program.ex check_ast/1` before/at
`elaborate_declarations`), compute the multiset of **family names** contributed by
(a) each imported module and (b) the local module. A **collision** is any family
name provided by ≥2 distinct sources. Detection covers **both** local-vs-import
**and** import-vs-import.

**Interaction with the auto-prelude skip.** `program.ex auto_prelude_imports/1`
today *skips* auto-importing `Std.Bool`/`Std.Nat` when the module declares a
same-named type, so no collision arises for the auto case. The general mechanism
here can subsume that skip: prefer to **stop skipping** and let auto-imported
families collide + re-key like any other, so the qualified escape hatch (`Std.Nat.Z`)
works uniformly even when the type was only auto-imported. If the plan instead
retains the skip (lowest-risk), then reaching an auto-prelude type's shadowed
constructor requires an explicit `use Std.Nat` — acceptable, but the plan must
state which choice it takes and keep the existing auto-prelude tests green either
way. The re-keying path must be validated against **explicit `use`** regardless.

### 3.2 Re-keying the shadowed families (the core transform)

For each colliding family name `N`:
- **Winner of the unqualified name `N`:** the local declaration if the local
  module declares `type N`; else — if exactly one import provides `N` — that
  import; else (≥2 imports, no local) `N` is **unqualified-ambiguous** (§3.4).
- **Losers** (every import providing `N` that is not the winner) are **re-keyed**:
  the family key `:N` becomes the qualified atom `:"<Module>#N"` (e.g.
  `:"Std.Nat#Nat"`), and each of its constructors `:C` becomes `:"<Module>#C"`
  (e.g. `:"Std.Nat#Z"`). The re-key is applied to that imported module's slice of
  the `Env`:
  - `families`: move `:N` → `:"<Module>#N"` (family record's `name` field updated).
  - `ctors`: move each `:C` → `:"<Module>#C"` (ctor record's `name` field updated
    — see §3.5 for the runtime-tag caveat).
  - `ctor_to_family`: repoint each re-keyed ctor to the re-keyed family.
  - `defs`: rewrite the imported module's Core terms so every `{:data, :N, …}`,
    `{:ctor, :C, …}`, and any embedded family/ctor atom is substituted to its
    re-keyed atom (a pure atom-substitution walk over the term forms).
- **Constructor-name collisions within a re-keyed family are harmless**: local `Z`
  and re-keyed `:"Std.Nat#Z"` are distinct keys; both may exist.

Because the winner keeps the bare key `:N` and its bare ctor keys, and everything
else in the program already references bare keys, **no non-colliding term changes**.
The disown is automatic: after re-keying, `ctor_to_family` maps `Zero,Suc → :Nat`
(local) and `Std.Nat#Z, Std.Nat#S → :"Std.Nat#Nat"`, so `ctors_of(:Nat)` returns
exactly `{Zero,Suc}` and coverage passes.

### 3.3 Resolution table

Alongside re-keying, build a **resolution table** recording, per module, the
mapping from qualified surface paths to registry keys:
- `"Std.Nat"` (as a type) → the `Nat` type key from module `Std.Nat`
  (`:"Std.Nat#Nat"` when re-keyed, else `:Nat`) — this is R4's collapse.
- `"Std.Nat.Z"` → the ctor key (`:"Std.Nat#Z"` when re-keyed, else `:Z`).
- `"Std.Nat.Nat"` → same as `"Std.Nat"` (both spellings accepted).

The table also retains **shadowed-but-present** names (which bare surface name is
now only reachable qualified, and from which module) to power R5's diagnostics.

The table is threaded into elaboration. It lives in the E-layer (NOT in the core
`Env` struct) — e.g. carried on the elaboration context/`names` environment or a
sibling structure passed to `elaborate_expr_typed` / declaration elaboration —
so `lib/cure/core/*` is untouched.

### 3.4 Unqualified ambiguity

If ≥2 imports provide family `N` and the local module does not declare `N`, bare
`N` (and any bare ctor name provided by >1 of them) is ambiguous. Using it
unqualified is an error: `{:ambiguous_name, N, [Module1, Module2]}` with a message
listing the qualified forms. Both families are still reachable via their qualified
paths. (This case is rare today — the stdlib has no duplicate family names — but
detection must not silently let one import clobber another.)

### 3.5 Runtime constructor tags stay bare (AtomVM invariant)

The BEAM/AtomVM value representation tags a constructor by its **bare** name
(`Zero`, `Suc`, `Z`, `S`). Qualified keys are elaborator/registry-internal only.
Codegen (`lib/cure/compiler/codegen.ex`) must emit the **bare** tag even for a
re-keyed constructor: strip the `"<Module>#"` prefix from a ctor atom of the form
`:"Mod#C"` → `C` when producing the runtime tag. This is the only C-layer touch and
is exercised **only** on the escape-hatch path (a re-keyed ctor actually used).
Structural tag collisions across distinct families are safe: type safety is
enforced entirely at compile time, and BEAM ADTs routinely share tags across types.

### 3.6 Qualified reference resolution in the elaborator

Qualified references parse as nested `{:attribute_access, [attribute: seg], [base]}`
chains (`Std.Nat.Z` → `attribute_access("Z", attribute_access("Nat", var "Std"))`).
The dependent elaborator currently handles `attribute_access` only for tuple
projection. Extend it so that, **when the flattened dotted path resolves in the
resolution table** to a type or constructor key:
- In a **type slot** (`idx_to_core` / type-expression elaboration,
  `declarations.ex`): `Std.Nat` / `Std.Nat.Nat` → `{:data, <key>, params, indices}`.
- In an **expression / pattern position** (`elaborator.ex`): `Std.Nat.Z` →
  the constructor reference/pattern for `<ctor key>`.
- A dotted path that does **not** resolve to a type/ctor falls through to the
  existing tuple-projection / attribute behavior unchanged (no regression).

Path flattening reuses the parser's dotted-path handling shape
(`extract_dotted_path`); the leading segment(s) form the module path, the last
segment the type/ctor name.

## 4. Worked examples

| Program | Unqualified resolves | Escape hatch |
|---|---|---|
| `use Std.Nat` (Z\|S) + local `Nat = Zero\|Suc` | `Nat`,`Zero`,`Suc` → local; `Z`,`S` → imported (R2) | `Std.Nat` → imported type; `Std.Nat.Z` → imported ctor |
| `use Std.Nat` (Z\|S) + local `Nat = Z\|S` | `Nat`,`Z`,`S` → local (imported fully shadowed, R1) | `Std.Nat.Z` → imported ctor (still reachable, R3) |
| `use Std.Nat` only, no local `Nat` | `Nat`,`Z`,`S` → imported (unchanged) | `Std.Nat.Z` also works |
| `use A` + `use B`, both define `Nat`, no local | bare `Nat` → `{:ambiguous_name,…}` (R3.4) | `A.Nat` / `B.Nat` each resolve |

## 5. Diagnostics (R5)

The resolver retains, per bare surface name, whether it is *shadowed* (present in
an import but not the unqualified winner) and its origin module + sibling ctor set.
Two shadow-aware errors replace the generic ones **only when a shadow is in play**:

- **Wrong shadowed constructor in a pattern/coverage context.** Matching `Z()` on a
  scrutinee whose in-scope family is the local `Nat = Zero | Suc`:
  `{:shadowed_ctor, ctor: :Z, shadowed_module: "Std.Nat", local_family: :Nat,
    local_ctors: [:Zero, :Suc], hint: "Std.Nat.Z"}`
  rendered as: *"`Z` is a constructor of `Std.Nat`, which is shadowed here by the
  local `Nat` (constructors `Zero`, `Suc`). Write `Std.Nat.Z` to use the shadowed
  constructor."*
- **Missing branch that is actually a shadow artifact** — if coverage would report
  `{:missing_branch, C}` for a constructor `C` that belongs to a *shadowed* family
  rather than the scrutinee's family, emit the `:shadowed_ctor`-style hint instead
  of the bare `:missing_branch`.

When no shadow is in play, the existing `{:foreign_ctor,_}` / `{:missing_branch,_}`
errors are unchanged (R6).

## 6. Test strategy (TDD, differential oracle)

Each behavior is pinned by a paired `.cure`/`.idr` oracle probe (faithful
transliteration, `%default total`, no `module` line) plus a focused elaborator
unit test. Red-first: the repro (P-a) is currently `{:missing_branch, :S}`.

Oracle cluster `shadow` (new), probes:
- **shadow01** — R1-partial repro: `use Std.Nat` + local `Nat = Zero|Suc`, match
  `Zero`/`Suc`. Cure currently rejects; Idris accepts (local shadows). Target:
  `same` (accept).
- **shadow02** — R1 full: local `Nat = Z|S` shadowing same-named imported ctors;
  construct + match locally. Target `same`.
- **shadow03** — R2: local `Nat = Zero|Suc`; a function using unqualified `Z`/`S`
  still refers to imported `Std.Nat`. Target `same` (both accept, both resolve to
  imported).
- **shadow04** — R3 escape hatch: after a local shadow, `Std.Nat.Z` /
  `Std.Nat` used explicitly. Target `same`.
- **shadow05** — R4 collapse: `Std.Nat` in a type slot (no `.Nat`). Target `same`.
- **shadow06** — R5 diagnostic: match a shadowed ctor on the wrong family; assert
  the specific `:shadowed_ctor` error (Cure-only unit assertion; Idris side is a
  parallel type error — relation `cure_stricter`/documented, or an idris probe that
  also errors → `same` on *reject*, with the reason pinned to the message).
- **shadow07** — R3.4 ambiguity: two imports both defining `Nat`, no local, bare
  use → `{:ambiguous_name,…}`. (Constructed with a scratch second stdlib-style
  module if none exists; relation documents the deliberate reject.)

Unit tests (behavioral, immutable once green):
- `test/cure/elab/type_shadowing_test.exs` — the R1–R5 cases at
  `Program.elaborate/1` granularity, asserting `{:ok,_}` / specific error tuples.
- Extend `test/cure/elab/auto_prelude_test.exs` only if a new auto-prelude
  interaction surfaces (auto-prelude collision-avoidance must remain green).

Gate (run once, alone — never concurrent suites):
1. New unit + oracle probes green.
2. `mix test test/oracle_replay_test.exs` green (no other probe regressed).
3. Full suite `mix test` green (2843/0 baseline or higher).
4. Codegen sanity for the escape-hatch path: a program using `Std.Nat.Z` compiles
   and the emitted constructor tag is bare `Z` (assert on the generated forms; a
   host run is sufficient — no hardware needed for this invariant).

## 7. Non-goals

- **Fully-qualified internal naming (Approach A).** Not adopted; see §1.3.
- **Agda-style ambiguous-constructor type-directed disambiguation.** Constructors
  remain a one-name→one-family map per resolution scope; ambiguity is an error
  (§3.4), not resolved by expected type.
- **Nested / sub-module namespaces.** Cure modules are flat; `Module#Name` handles
  one level. No arbitrary nesting.
- **Qualifying `defs` (functions).** Function/value shadowing already works
  (last-writer-wins); this spec does not change it. Only families + constructors
  gain the resolution layer. (If a function name genuinely needs qualified access
  it can be added later on the same table; out of scope here.)
- **No kernel/TCB change.** `lib/cure/core/*` is not modified.

## 8. Risk + layer summary

- **Primary layer E** (`lib/cure/elab/program.ex` collision detection + re-key +
  table; `lib/cure/elab/elaborator.ex` + `lib/cure/elab/declarations.ex` qualified
  resolution + diagnostics). No soundness surface — the kernel still checks the
  same Core it always did; only *which* family key a name resolves to changes,
  entirely before the kernel sees a term.
- **Contained C touch** (`lib/cure/compiler/codegen.ex`) — strip `Mod#` prefix for
  runtime tags; escape-hatch path only.
- **Chief risk:** a missed collision silently reverting to clobber. Mitigated by
  detecting *all* family-name collisions (import-vs-import included) with a simple
  set-comparison, and by shadow07/shadow0x probes. The re-key term-rewrite is a
  bounded pure atom substitution over one module's `defs`, unit-tested directly.
- **Regression guard:** non-collision path is a no-op; R6 asserted by the full
  suite + replay.
