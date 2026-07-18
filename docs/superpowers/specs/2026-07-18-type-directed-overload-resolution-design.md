# Type-Directed Overload Resolution (Ph1) — Design

**Status:** design approved 2026-07-18 (operator gate). Buildable slice of the
parent design `docs/superpowers/specs/2026-07-10-overloading-and-argument-labels-design.md`
(commit `b25081e`). This spec pins the implementation-level decisions the parent
left open and narrows scope to the piece we build now.

**Goal:** let several functions share a name and have the **call site** pick the
right one from the surrounding type context — Idris2-style "elaborate-and-prune",
keyed by `(name, arity, argument types)`. Both **same-module** and
**cross-module** overload sets are in scope.

**Zero TCB.** This is a surface (P) + elaborator/resolution (E) + emit feature.
Overload sets and the chosen member resolve away during elaboration; emitted Core
and BEAM calls are positional and name-mangled. The trusted kernel
(`lib/cure/core/*`) never sees an overload set and is not touched. No Antigen
antibody is needed (no new Core former, no kernel rule).

---

## 1. Scope

**In scope (Ph1 — named resolution):**
- Same-module overload sets: two `fn plus(...)` with different parameter types in
  one `mod`.
- Cross-module overload sets: `Std.Char.to_int(Char)` and
  `Std.String.to_int(String)` both reachable unqualified under the name `to_int`,
  resolved by argument type.
- Resolution by **argument type**; diagnostics for zero and multiple survivors;
  qualified `Mod.f` remains the always-available escape hatch.

**Explicitly OUT (deferred, do not build here):**
- **Argument labels** (Swift-style, parent spec Ph2). Not in this run.
- **The `+`/operator ergonomic.** Making `MkM(3) + MkM(4)` dispatch to a
  user overload is deferred until a Swift-style precedence-group + custom-infix
  syntax structure is spec'd. Do NOT add a `+`→overload desugar or any operator
  special-case in `elaborate_expr_typed`. The existing operand-directed operator
  routing (`<>`/non-numeric `+`→`Std.Semigroup.combine`; `<`/`>`/`<=`/`>=`→
  `Std.Ord`) stays exactly as-is.
- The `_ x`-label-suppression form (parent spec Ph3).

## 2. The pin (definition of done)

`test/cure/elab/type_directed_overload_test.exs` (`@moduletag :overload`, the one
`@tag :skip` deleted) must pass. Its source defines two `fn plus` — one on
`Meters`, one on `Grams` — in a single module and asserts
`plus(MkM(3), MkM(4))` resolves to the `Meters` overload and
`plus(MkG(10), MkG(20))` to the `Grams` one, verified through runtime results
(`add_m() == 7`, `add_g() == 30`) after a real `compile_and_load`. A
cross-module analogue (below) is added as a second pin.

Today both fail at `{:codegen_error, {:duplicate_definition, :plus}}` — the
surface cannot even express a set. This is the wall Task 1 removes.

## 3. Real-language alignment

Idris2 type-directed disambiguation: when a name is ambiguous, Idris2 elaborates
each candidate against the argument/expected types and keeps the one that checks;
the chosen definition is emitted under its own mangled internal name. We port the
mechanism and oracle-probe the covered cases against `idris2 --check`. Alignment
target for this feature is **Idris2** (surface + resolution only; the TCB-binding
Agda/Lean/Idris alignment law does not apply — nothing in `core/*` changes).

## 4. Architecture — four touch points

Current single-winner name resolution is grounded in these code paths (verified
2026-07-18):

- **Dedup gate** — `Cure.Elab.Program.check_no_duplicate_defs/1`
  (`lib/cure/elab/program.ex:344`) → `first_dup_per_module` raises
  `:duplicate_definition` on any repeated `:function_def` **name** in a module.
  The key is the bare name only, **not** name+arity: `f/1` and `f/2` in one module
  are rejected today too. Its stated reason: `Env.add_def` is a silent `Map.put`,
  so a true duplicate would let a program typecheck one body and run another.
- **Env keying** — every def is stored under a canonical owner-qualified atom
  `Mod#name` (`Cure.Elab.Name.qualify`). Two same-module `plus` map to the same
  key `Mod#plus` and the second silently overwrites the first.
- **Resolution** — `Cure.Elab.Resolution.resolve_bare/2`
  (`lib/cure/elab/resolution.ex:50`) returns `{:ok, key}` for a unique provider or
  `{:ambiguous, owners}` for ≥2 cross-module providers; `resolve_canonical_suffix`
  matches keys ending in `"#name"`. Call sites consume it via
  `applied_def_key/3` (`lib/cure/elab/declarations.ex:2083`, dependent-index
  position) and the term-position `elaborate_named_call` path.
- **Emit** — `emitted_name/1` and `remote_target/2` (`lib/cure/elab/emit.ex:229`,
  `:236`) turn a canonical key into a BEAM function name via `Cure.Elab.Name.base`,
  with an `emit_aliases` override map keyed by canonical key.

The design threads an **overload discriminator** through all four so a set of
same-name members has distinct identities end-to-end.

### 4.1 Overload identity — the discriminator

An **overload member** is identified by a canonical key that extends the base
`Mod#name` with a stable per-member discriminator, so members never collide in
`env.defs` and never overwrite. The discriminator is the member's **arity plus a
declaration-order ordinal within the `(module, name)` group**, rendered so that:

1. two members of the same set get distinct keys (`Mod#plus/2#0`, `Mod#plus/2#1`);
2. the base name `plus` and arity remain mechanically recoverable from the key
   (the bare-suffix resolver and emit both need the base);
3. a set of size one is byte-identical to today's `Mod#plus` (no discriminator),
   so the overwhelming non-overloaded majority of the stdlib is unchanged and no
   existing golden/emit test moves.

The exact key spelling is a plan-level decision; the design constraint is (1)–(3).
Ordinal-by-declaration-order is chosen over full-signature mangling because it is
short, always well-defined, and independent of how parameter types print; type
information lives in the member's telescope, which resolution reads directly.

### 4.2 Building the overload set

The dedup gate (§4 touch point 1) is **transformed, not removed**. Repeated
`:function_def` names in a module are no longer an automatic error. Instead:

- Group a module's function defs by **name** (the gate's current key).
- A group of size ≥2 is a candidate overload set. Assign each member a
  discriminated key (§4.1) and register all of them (no overwrite).
- Members with **distinct arities** (`f/1` vs `f/2`) are a legal set trivially
  disambiguated by arity at the call site — the transform legalizes these too
  (they are rejected today), needing no type check.
- **The safety the old gate protected is preserved** for the same-arity case: if
  two members of a group have the same arity and parameter telescopes that
  mutually unify (i.e. no argument could ever tell them apart — a genuine
  accidental redefinition, not an overload), that is still an error:
  `{:overlapping_overload, name, arity}`. Same name + same arity + distinguishable
  types = a set; same arity + indistinguishable types = the old duplicate bug,
  still rejected.

### 4.3 Call-site resolution — elaborate-and-prune

At an applied use `name(a₁, …, aₙ)` where `name` resolves to an overload set (size
≥2), resolve as follows:

1. **Gather** the candidate set: all in-scope members with this `name` and this
   arity `n`. Same-module members come from the local group; cross-module members
   come from generalizing `resolve_bare` to return **every** suffix match rather
   than collapsing to one/ambiguous. A qualified head `Mod.name` restricts the set
   to that one module (escape hatch, unchanged path).
2. **Infer** each argument's type in inference mode (the arguments are elaborated
   once; results are reused for the winning member so no double-elaboration cost on
   the happy path).
3. **Prune**: keep a candidate iff each argument's inferred type unifies with the
   corresponding parameter type in the candidate's telescope.
4. **Decide**:
   - exactly one survivor → resolve the head to that member's discriminated key;
   - zero survivors → `{:no_matching_overload, name, arg_types}`;
   - more than one survivor → `{:ambiguous_overload, name, candidate_owners}`,
     with a diagnostic naming the qualified escape hatch (`Mod.name`) as the fix.
     (Ph1 has no labels; labels are the parent spec's later tie-breaker.)

A set of size one bypasses all of this and takes today's exact single-winner path
— the feature is inert for non-overloaded names.

Pruning is **first-order argument-type unification** against each candidate's
declared parameter types — sufficient for the motivating cases (Char vs String,
Meters vs Grams, and the stdlib collisions). Full Idris-style
elaborate-each-candidate-against-expected-type (return-type-directed resolution
when arguments are themselves ambiguous) is a documented limitation, not built in
Ph1; if zero/one argument disambiguates, the expected-type fallback is out of
scope and surfaces as `{:no_matching_overload}` or `{:ambiguous_overload}` telling
the user to qualify.

### 4.4 Emission

Each overload member emits under a **distinct BEAM function name** derived from
its discriminated key, because two same-arity members would otherwise both claim
`plus/2` and the second would overwrite the first in the module's function table
(the runtime-level twin of the env-overwrite bug). Resolution in §4.3 has already
rewritten every call site's head to the specific member key, so the emitted call
targets the specific mangled name. A size-one set emits under the plain base name
exactly as today (constraint §4.1.3). The `emit_aliases`/`emitted_name` hook is the
insertion point; no change to `remote_target`'s remote/local decision is needed
beyond honoring the discriminated name.

## 5. Cross-module pin

Add to the pin test a cross-module case proving the parent spec's actual
motivation. Two small modules each export a same-named, differently-typed function
(e.g. `by_int(Int)` in one, `by_bool(Bool)` disambiguated only by argument type —
or a faithful `to_int(Char)` vs `to_int(String)` pair), a consumer `use`s both and
calls the name unqualified, and the call resolves by argument type. Because
`compile_and_load` takes a single source, the cross-module case is exercised either
through a multi-module fixture compiled via the project's multi-file path or via a
prebuilt-beam `EXTRA_BEAMS` harness; the plan picks the mechanism already used by
existing cross-module tests. The behavioral assertion (correct runtime result per
type) is mechanism-agnostic.

## 6. Error taxonomy

| Condition | Error |
|---|---|
| Same name+arity, parameter types mutually indistinguishable | `{:overlapping_overload, name, arity}` (replaces the accidental-duplicate case of `:duplicate_definition`) |
| Call matches no candidate's argument types | `{:no_matching_overload, name, arg_types}` |
| Call matches ≥2 candidates | `{:ambiguous_overload, name, owners}` (diagnostic: qualify as `Mod.name`) |

The same-arity indistinguishable case that previously raised
`:duplicate_definition` at this gate is now reported as `:overlapping_overload`;
the gate no longer rejects a legal set. `:duplicate_definition` at its other,
unrelated sites (it also propagates wrapped as `{:codegen_error, …}` — the
compiler's outer wrapper at `compiler.ex:331/422`, not a second guard) and the
`:unknown_global` diagnostic for genuinely-unknown names are unchanged.

## 7. Non-goals

- No kernel/`core/*` change; no new Core former; no Antigen antibody.
- No argument labels; no operator overloading; no return-type-directed resolution.
- No change to qualified-path resolution (`Mod.f` already restricts to one owner).
- No change to the operand-directed Semigroup/Ord operator routing.

## 8. Test plan

Strict TDD, behavioral and immutable tests:

1. **Pin (same-module)** — the existing `type_directed_overload_test.exs` case,
   `@tag :skip` deleted; asserts runtime results after `compile_and_load`.
2. **Pin (cross-module)** — §5; asserts the unqualified call resolves by argument
   type across modules.
3. **Overlap rejection** — two same-name, same-arity members with unifiable
   parameter types → `{:overlapping_overload, …}` (the preserved safety check).
   This is the red test proving §4.2 did not just delete the guard.
4. **No-match** — a call whose argument types match no member →
   `{:no_matching_overload, …}`.
5. **Ambiguous** — a call matching ≥2 members → `{:ambiguous_overload, …}`; and a
   qualified `Mod.name` at the same site resolves cleanly (escape hatch).
6. **Inertness** — a representative existing single-definition module still
   compiles byte-identically (guard against key-format regressions); the full
   suite green is the backstop.
7. **Oracle** — an `idris2 --check` probe for the covered same-module and
   cross-module cases, added to the OTP/oracle harness if the argument-type
   resolution has a natural Idris transcription; skipped with a recorded reason if
   Idris is unavailable in the environment.

## 9. Risks

- **Key-format ripple.** The `Mod#name` suffix is matched textually in several
  resolver helpers (`resolve_canonical_suffix`, `shadowed_origin`,
  `ambiguous_modules`, all keyed on the `"#name"` suffix). The discriminator must
  keep the base name recoverable so these keep working for size-one sets; the
  inertness test (§8.6) and full-suite green are the guards. This is the highest-
  risk area and is why the discriminator is additive (absent for size-one).
- **Double elaboration of arguments.** Naive elaborate-each-candidate re-checks
  arguments per candidate. Infer argument types once, reuse for the winner (§4.3
  step 2) to avoid O(candidates) blow-up and duplicated side effects.
- **Ambiguity where a human expects a match.** First-order-only pruning may reject
  a case Idris would resolve via expected type. Ph1 surfaces this as an actionable
  `{:ambiguous_overload}`/`{:no_matching_overload}` telling the user to qualify —
  never a silent mis-resolution.
