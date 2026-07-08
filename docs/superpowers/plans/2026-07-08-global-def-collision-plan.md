# Global-Def Collision Protection Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the E-layer soundness gap where cross-module same-named global functions silently overwrite, by extending the locked Approach-B collision-triggered re-keying from families/ctors to `defs` — with the ambiguity trichotomy enforced at BOTH bare-reference resolution sites.

**Architecture:** `shadow_resolved_imports/1` (program.ex) gains a def-ownership scan parallel to `family_owners`; `Resolution.classify/2` output for defs drives `rekey_module_env` to move colliding def KEYS (and their `certified` membership) to `"Mod#name"` atoms; `ambiguous_modules/2` generalizes to consult `defs`; the trichotomy (local wins → unique import → E089 ambiguity) is enforced in `elaborate_named_call/5` (call position — extends the existing R7 check) and `resolve_free/2` (bare-value position — currently has zero checking).

**Spec:** `docs/superpowers/specs/2026-07-08-global-def-collision-design.md` (hardened). §2.1-2.2 are the contract; §4 names the red tests.

## Global Constraints

- One build/test run at a time, always sequential. OTP 26–28.
- Kernel/TCB untouched: no changes under `lib/cure/core/` EXCEPT none — even the `certified` re-key happens in `lib/cure/elab/resolution.ex` by rebuilding the Env struct field (the Env struct itself is not modified).
- TDD: red first for the stated reason, minimal green, refactor; tests immutable once correct (escape hatch only for a test proven wrong before ever green, argued explicitly).
- Commits authored as the user only, NO co-author trailers.
- Worktree root: `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/kernel-parity-batch`.

## Verified ground truth (2026-07-08 — trust these)

- `merge_env/2` blind-merges defs: `program.ex:629`.
- Ownership/classify/rekey flow for families: `shadow_resolved_imports/1` at `program.ex:532-590` — `family_owners` map (`owned_family_names(path)` per transitive module, `program.ex:489`), `Resolution.classify(family_owners, local)` → `%{losers, ambiguous}`, per-slice `Resolution.rekey_module_env(s, owner_mod, owned_losers, local_ctors)`, then `drop_bare_family` cleanup.
- `rekey_module_env/4` (`resolution.ex:79-103`): builds bare→`Mod#name` `amap`, rewrites `families`/`ctors`/`ctor_to_family`/`defs`(references only)/`builtins`. Does NOT touch `certified`.
- `ambiguous_modules/2` (`resolution.ex:285-300`): families-only; returns `[]` when the bare key exists, else origin modules providing `Mod#bare`.
- Call-position resolution + R7 precedent: `elaborate_named_call/5` (`elaborator.ex:231`); ambiguity check at `elaborator.ex:304-305` produces `{:error, {:ambiguous_name, atom, modules}}`.
- Bare-value resolution: `resolve_free/2` (`elaborator.ex:~4641`), zero checking, falls through to `{:global, atom}`.
- `local_def_names/1` is public (`program.ex:153-154`).
- `{:ambiguous_name, _, _}` has NO `format_error/2` clause and no E-code in `lib/cure/compiler/errors.ex` yet (grep verified) — it currently hits the catch-all. E089 is free.
- K12 probe file: `test/cure/elab/global_namespace_soundness_test.exs` (`check/1` helper: lex→parse→`Program.check_ast/1`). Cross-module tests need the import path: fixture modules must be reachable as stdlib-style sources — the dependent elaborator only imports `Std.*` (`import_source_path`), so cross-module fixtures follow the pattern used by existing cross-module tests (see `Cure.Elab.CrossModuleNamesTest` — read it in Task 1 and reuse its fixture mechanism verbatim; if it writes temp files into a stdlib-source override dir via the `:cure` env, reuse that).

---

### Task 1: Red tests — the gap, pinned at all three surfaces

**Files:**
- Modify: `test/cure/elab/global_namespace_soundness_test.exs` (append a new `describe "cross-module global collisions"`)

**Interfaces produced:** none (tests only — they encode §4.1/§4.2/§4.4 of the spec).

- [ ] **Step 1:** Read `test/cure/elab/cross_module_names_test.exs` and copy its fixture mechanism for making two importable modules (call them `Std.CollA` and `Std.CollB` in a tmp stdlib dir, or whatever mechanism that file actually uses). Each defines `fn helper(x: Nat) -> Nat` with observably different bodies (`Z()` vs `S(Z())` result shapes) AND a certified-total marker-compatible shape (plain structural, no recursion).
- [ ] **Step 2:** Append tests (adjust ONLY the fixture plumbing to match the mechanism found in Step 1; the assertions are immutable):

```elixir
  describe "cross-module global def collisions (design 2026-07-08)" do
    test "bare call of a doubly-imported name is an ambiguity error, not last-merge-wins" do
      # use Std.CollA + use Std.CollB, body: helper(Z())
      # TODAY: silently binds the last-merged helper -> {:ok, _}
      # AFTER: {:error, {:ambiguous_name, :helper, mods}} with both modules listed
      assert {:error, {:ambiguous_name, :helper, mods}} = check(fixture_bare_call())
      assert Enum.sort(mods) == ["Std.CollA", "Std.CollB"]
    end

    test "bare VALUE reference (higher-order arg) raises the same ambiguity error" do
      # fn ap(f: Nat -> Nat, x: Nat) -> Nat = f(x)  ... ap(helper, Z())
      assert {:error, {:ambiguous_name, :helper, _}} = check(fixture_bare_value())
    end

    test "qualified calls reach their own module's body despite the collision" do
      # Std.CollA.helper(Z()) and Std.CollB.helper(Z()) both elaborate
      assert {:ok, _env} = check(fixture_qualified_both())
    end

    test "local def shadows the imports; qualified still reaches them" do
      assert {:ok, _env} = check(fixture_local_shadow())
    end

    test "non-colliding imported defs keep bare keys (no blanket re-keying)" do
      {:ok, env} = check(fixture_no_collision())
      assert Map.has_key?(env.defs, :lonely_helper)
      refute Enum.any?(Map.keys(env.defs), fn k ->
               String.ends_with?(Atom.to_string(k), "#lonely_helper")
             end)
    end
  end
```

- [ ] **Step 3:** Run: `mix test test/cure/elab/global_namespace_soundness_test.exs 2>&1 | tail -15`
Expected red: the two ambiguity tests FAIL (today `check` returns `{:ok, _}` — the silent overwrite — or an unrelated error; record which). The qualified/local/no-collision tests may pass or fail depending on current qualified handling — record the actual split; any currently-green test is regression cover, not a red gate.
- [ ] **Step 4:** Commit: `git add test/cure/elab/global_namespace_soundness_test.exs && git commit -m "test(elab): pin cross-module global-def collision gap (red)"` — committing red tests is intentional here; the suite gate at the end of Task 4 is where everything must be green. (If the repo's CI-on-every-commit discipline forbids committed reds, fold this commit into Task 2's instead and say so.)

### Task 2: Re-keying — ownership scan, classify, rekey defs + certified

**Files:**
- Modify: `lib/cure/elab/program.ex` (`shadow_resolved_imports/1`, new `owned_def_names/1`)
- Modify: `lib/cure/elab/resolution.ex` (`rekey_module_env/4` → also move def keys + `certified`; `classify/2` reused as-is — it is shape-generic over `%{name => owners}`)

**Interfaces:**
- Produces: `rekey_module_env(env, module_id, owned_family_names, shadowed_ctor_names, owned_def_names)` (new 5th arg, defaulted `MapSet.new()` so existing callers/tests are unaffected), which additionally: adds `owned_def_names ∩ collision set` to `amap`, moves those `defs` KEYS via the amap, and rebuilds `certified` membership through the amap.

- [ ] **Step 1:** In `program.ex`, add `owned_def_names/1` next to `owned_family_names/1` (`:489`), extracting fn names from the module source the same way `owned_family_names` extracts family names (mirror its parse/scan mechanism exactly; exclude nothing — `@group` is a decorator now, and `__group__` no longer exists).
- [ ] **Step 2:** In `shadow_resolved_imports/1`, build `def_owners` exactly parallel to `family_owners` (same transitive walk — do it in the SAME `Enum.reduce` pass to avoid re-walking), classify against `MapSet.new(local_def_names(ast))`, union the def losers into the per-slice re-key call (pass as the new 5th arg), and union def collisions into the residual-cleanup set ONLY if a `drop_bare_def` analog proves necessary (first try without it; the family `drop_bare_family` exists because of seeded builtins — defs have no seeding, so residual bare copies should not arise. If the Task 1 no-collision test fails from residue, add the analog and note it).
- [ ] **Step 3:** In `resolution.ex` `rekey_module_env`, extend `amap` with the owned-and-colliding def names, change `rekey_defs/2` to ALSO move keys present in `amap` (today it only rewrites references inside values — keep that, add the key move), and add `certified: rekey_certified(env.certified, amap)` to the returned struct (`MapSet` map-through). Update the moduledoc sentence "Functions keep their bare `defs` keys." — it becomes false.
- [ ] **Step 4:** Run the Task 1 file. Expected: qualified/no-collision/local tests move toward green (qualified resolution may already work via `resolve_qualified(:value)` — verify it consults re-keyed def atoms; if not, extend it here, it is part of re-keying's contract). The two ambiguity tests stay red (resolution sites not wired yet).
- [ ] **Step 5:** Commit: `feat(elab): re-key colliding global defs across module slices (Approach B)`

### Task 3: Ambiguity trichotomy at both resolution sites + E089

**Files:**
- Modify: `lib/cure/elab/resolution.ex` (`ambiguous_modules/2` consults defs too; `resolve_bare_shadowed/2` returns the unique re-keyed def when exactly one import provides it)
- Modify: `lib/cure/elab/elaborator.ex` (`elaborate_named_call/5` — the existing R7 check now fires for defs via the generalized `ambiguous_modules`; `resolve_free/2` — add the same check + unique-import mapping before the `{:global, atom}` fallthrough)
- Modify: `lib/cure/compiler/errors.ex` (E089 `format_error` clause + catalog entry for `{:ambiguous_name, name, modules}`)
- Test: `test/cure/compiler/dep_graph_errors_format_test.exs`-style new file NOT needed — add the formatter test into `test/cure/elab/global_namespace_soundness_test.exs` describe, asserting `Errors.format_error({:ambiguous_name, :helper, ["Std.CollA", "Std.CollB"]}, "x.cure")` mentions `E089`, both modules, and the qualified-form hint.

- [ ] **Step 1:** Generalize `ambiguous_modules/2`: same suffix scan over `Map.keys(env.defs)` unioned with the existing families scan (still `[]` when the bare key exists in EITHER map — a winner exists). Keep the spec `@doc` honest about both namespaces.
- [ ] **Step 2:** `resolve_bare_shadowed/2` (`resolution.ex:224`): extend to defs — when `bare` is absent from `defs` but exactly ONE `Mod#bare` def key exists, return `{:ok, that_key}` (mirrors the family/ctor unique-loser rule; read the existing clauses first and follow their exact precedence).
- [ ] **Step 3:** `resolve_free/2` in `elaborator.ex`: before the final fallthrough, mirror the trichotomy:

```elixir
  defp resolve_free(name, env) do
    atom = String.to_atom(name)

    cond do
      Inductive.get_ctor(env, atom) -> {:ok, {:ctor, atom, []}}
      Inductive.family?(env, atom) -> {:ok, {:data, atom, [], []}}
      length(Cure.Elab.Resolution.ambiguous_modules(env, atom)) >= 2 ->
        {:error, {:ambiguous_name, atom, Cure.Elab.Resolution.ambiguous_modules(env, atom)}}
      true ->
        case Cure.Elab.Resolution.resolve_bare_shadowed(env, atom) do
          {:ok, key} -> {:ok, {:global, key}}
          _ -> {:ok, {:global, atom}}
        end
    end
  end
```

CAUTION: `resolve_free/2` callers may pattern-match `{:ok, _}` only — grep every caller and thread the new `{:error, _}` return through each (this is the same widening discipline as the codegen 3-tuple migration; enumerate the callers in your report).
- [ ] **Step 4:** E089 in errors.ex: `format_diagnostic("error", "ambiguous name (E089)", file, 1, "…'#{name}' is provided by #{Enum.join(modules, " and ")}; qualify the call (e.g. #{hd(modules)}.#{name}(...)) or define a local #{name} to shadow them.")` + catalog `"E089"` entry in neighboring prose style.
- [ ] **Step 5:** Run the Task 1 test file → ALL green now. Then the formatter test → green.
- [ ] **Step 6:** Commit: `feat(elab): E089 ambiguous-name trichotomy at call and bare-value resolution (defs join families)`

### Task 4: Certificate survival + full gate

**Files:**
- Modify: `test/cure/elab/global_namespace_soundness_test.exs` (append the certificate test, spec §4.3)

- [ ] **Step 1:** Append: a colliding def that is certified total (structure it so the fixture module's def gets a certificate — mirror how existing totality/conversion tests arrange certification) and whose UNFOLDING is required for a conversion to succeed in the importing module via its QUALIFIED name. Assert `{:ok, _}`. Red check: temporarily assert against current behavior only if the test can be written red-first (if re-keying already carries certified from Task 2, this is regression cover — say so rather than manufacturing a fake red).
- [ ] **Step 2:** Full gate, sequential: `mix test 2>&1 | tail -5` (expect 0 failures), `mix cure.check.examples 2>&1 | tail -2` (expect 44 passed).
- [ ] **Step 3:** Commit: `test(elab): certificate survives global-def re-keying + gate`

## Self-review notes

- Spec §2.1 → Task 2 (incl. the certified MapSet step the spec calls out); §2.2 rules 1-3 both sites → Task 3; §2.2 rule 4 (qualified) → Task 2 Step 4 verification; §3 table → Tasks 2/3; §4.1-4.5 → Tasks 1/3/4; §4.6 → Task 4.
- The `{:ambiguous_name, name, mods}` tuple shape is IDENTICAL to the existing family R7 error — one concept, one formatter (E089), zero new tuple shapes.
- Unknowns deliberately surfaced to the implementer instead of guessed: the cross-module fixture mechanism (Task 1 Step 1 reads it), `resolve_free` caller widening (Task 3 Step 3 caution), residual-cleanup necessity (Task 2 Step 2).
