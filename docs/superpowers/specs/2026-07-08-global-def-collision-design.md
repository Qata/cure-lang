# Global-def collision protection — Design

**Date:** 2026-07-08
**Status:** Approved (operator batch authorization, autopilot run; first of three
sequenced initiatives — identity-type-as-inductive and the parity queue follow)
**Topic:** global-def-collision

## 1. Problem — a genuine E-layer soundness gap

When two modules in scope both define a global function `foo`, the later one
silently overwrites the earlier one. Flagged during K12 slice-4; never landed.

Ground truth (verified on this checkout):

- `Cure.Elab.Program.merge_env/2` (`lib/cure/elab/program.ex:629`) merges
  imported environment slices with `Map.merge(left.defs, right.defs)` — on a
  key collision the right slice wins, silently.
- The shadowing machinery (`lib/cure/elab/resolution.ex`, the locked
  Approach-B design: E-layer resolution over bare atoms, collision-triggered
  re-keying to `"Mod#Name"` atoms) protects **families and constructors
  only**. Its own doc comment states the gap verbatim: *"Functions keep their
  bare `defs` keys."* (`resolution.ex:62-63`; `rekey_module_env/3-4` re-keys
  `families`/`ctors`/`ctor_to_family` and only *renames references inside*
  `defs` bodies, never the def keys themselves.)

Consequence: `use A` + `use B` where both define `helper/1` gives whichever
slice merged last — the program type-checks and runs against the *other*
module's function. Proof-relevant code can silently call the wrong lemma. This
is exactly the class of silent-wrong-binding the family/ctor re-keying was
built to prevent; globals were left out.

## 2. Design — extend Approach B to `defs`, faithfully

No new mechanism. The locked type-shadowing decision (Approach B:
collision-triggered re-keying over bare atoms + qualified escape hatch,
core/TCB untouched) is extended to the third and last unprotected namespace.

### 2.1 Collision-triggered re-keying for def keys

In the import-merge path (`shadow_resolved_imports/1` →
`Resolution.rekey_module_env/…`):

- Detect def-name collisions across slices exactly as family/ctor collisions
  are detected today (bare-atom key intersection, including against the
  importing module's own locally-declared def names).
- A colliding def owned by an imported slice is re-keyed to
  `rekey_atom(module_id, name)` (`"Mod#name"`), and — as with ctors — every
  reference to it inside that slice's def bodies/types and telescopes is
  rewritten via the existing `rekey_term/2` atom map. The `certified` set and
  `quantities` metadata follow their def across the re-key (a certified
  total function must remain certified under its new key — otherwise
  δ-unfolding silently stops for it).
- Non-colliding defs keep bare keys (zero cost for the common case; identical
  to family/ctor behavior).

### 2.2 Reference resolution, same rules as types/ctors

For a bare reference `foo` where collisions were re-keyed:

1. The **local** module's own `foo` wins (local shadows import — mirrors the
   existing family/ctor rule and every real language's shadowing).
2. Otherwise, if exactly one import provides `foo`, that one (its re-keyed or
   bare atom) is used.
3. Otherwise — two or more imports provide `foo` and no local exists — the
   reference is an **ambiguity error**, a new E-code carrying the candidate
   modules, matching Idris's "Ambiguous name" / Agda's ambiguous-identifier
   errors. Silent picking is precisely the bug being fixed, so no default
   winner. The error text names the qualified escape hatch.
4. **Qualified references always work**: `A.foo(x)` resolves through module
   identity regardless of collisions (existing qualified machinery; the
   elaborator maps it to the re-keyed atom when one exists).

### 2.3 What is NOT changed

- **Kernel/TCB untouched.** Re-keyed defs are just differently-named globals
  to the kernel; `{:global, name}` semantics, conversion, certificates are
  oblivious (same argument that carried the family/ctor re-keying).
- **AtomVM/runtime tags untouched.** Def re-keying is an elaboration-env
  concern; emitted BEAM function names derive from the module actually being
  compiled (its own defs are local and bare). Cross-module *runtime* calls
  already go through qualified/remote resolution (codegen), not env keys.
- The classic (non-dependent) checker path is out of scope: its module
  compilation is per-file against loaded beams, and cross-module value calls
  resolve at codegen (see the auto-import-order spec §2). This gap is the
  dependent elaborator's env merge.
- No surface-syntax change. (The qualified escape hatch already exists.)

## 3. Error handling

| Condition | Behavior |
|---|---|
| Import collides with local def | Local wins; import re-keyed; both reachable (qualified for the import) |
| Two imports collide, bare reference used | New E-code ambiguity error listing candidates + qualified-form hint |
| Two imports collide, no reference to the name | No error (collision is latent; both re-keyed and reachable qualified) |
| Certified def re-keyed | Certificate follows the key; δ-unfolding unaffected |

E-code: next free number in the shared E/W/H sequence at implementation time
(089 expected — 086/087/088 were taken by the auto-import-order work;
implementation verifies against the registry).

## 4. Testing (TDD; red first, immutable once correct)

1. **Red reproduction of the gap**: two stdlib-style fixture modules both
   defining `helper/1` with observably different bodies (e.g. returning
   distinct constants); a third module `use`s both and calls `helper`
   qualified — assert each qualified call reaches ITS module's body. Then the
   bare-call case: assert the ambiguity error (this is the case that today
   silently returns the last-merged body — the red test pins today's wrong
   value and goes green on the error).
2. **Local-shadows-import**: importing module defines its own `helper`; bare
   call resolves locally; qualified call still reaches the import.
3. **Certificate survival**: a certified-total colliding def remains
   δ-unfoldable after re-keying (conversion test that requires unfolding, in
   the style of the existing totality tests).
4. **No-collision fast path**: unrelated imports keep bare keys (assert env
   keys directly — guards against re-keying everything).
5. **Antigen**: one antibody probe in the existing global-def family
   (mirrors the K12 slice-4 probe that found the gap) asserting the
   overwrite is impossible.
6. Full `mix test`, `mix cure.check.examples` — green, sequentially.

## 5. Out of scope

- Identity-type-as-inductive (next initiative in this batch).
- Classic-checker cross-module semantics; codegen resolution (covered by
  auto-import-order W088 work).
- Renaming/re-exporting surface syntax.
