# Antigen V5 — Totality-Closure Soundness — Design

**Status:** design (Stage 0, autopilot Phase 4) · **Date:** 2026-07-03 · **Branch:** `autopilot/antigen-tier-b`
**Umbrella:** `2026-07-03-antigen-untrusted-machinery-design.md` §V5 · **Predecessors:** V3 (elab), V1 (normalizer), V2 (unifier)

## 1. Goal

Extend Antigen to the **untrusted totality-closure driver**
`Cure.Elab.TotalityClosure` — the module that decides *which* type-level functions
must be certified total, and submits each to the trusted kernel. Type-level
non-termination is a **logical-inconsistency** hole: if the type-checker δ-unfolds a
function it relies on for convertibility and that function does not terminate,
Normalise loops (or a mis-certified diverging function admits a false type
equality). The kernel re-checks each *certificate* (`Kernel.validate_certificate`,
trusted); what it does **not** do — the untrusted half of design §7 — is decide the
**closure**: the set of functions reachable from a type position that must be
submitted at all.

**What is already covered vs. what is new.** The existing
`Antigen.Assays.Totality` (`totality/diverging` + `totality/terminating`) tests the
per-function *decision procedure* `Cure.Core.Certificate.terminating?/3`. V5 does
**not** duplicate that. V5's target is the **driver** around it:

- `type_level_fns/1` — the untrusted transitive-closure walk over type positions.
- `certify_type_level/1` — the end-to-end driver that folds `validate_certificate`
  over that closure.

## 2. Target (verified against source: `lib/cure/elab/totality_closure.ex`)

- `type_level_fns(%Env{}) :: MapSet.t(atom())` — every global reachable from a
  **type position**, transitively. Type positions (verified): family
  `params`/`indices` telescopes, constructor `args` telescope, constructor
  `result_indices`; transitive callees via each reached def's `body`. Uses private
  `seed_globals/1`, `tele_globals/1`, `close/3`, `collect/1`.
- `certify_type_level(%Env{}) :: {:ok, Env.t()} | {:error, {:totality_required, atom()}}`
  — `type_level_fns |> Enum.reduce_while({:ok, env}, …)` calling
  `Kernel.validate_certificate(acc, name)` for each; the first `{:error, _}` halts
  with `{:error, {:totality_required, name}}`.
- **The moduledoc's own safety claim** (to test, not assume): "a function this walk
  misses simply stays uncertified (opaque to δ) — never a soundness hole." V5b puts
  a number on the walk's completeness against an independent oracle; a *missed*
  type-level function is at minimum a violation of the closure's stated
  transitive-closure contract (§7), and the whole opacity-safety argument rests on
  the walk actually being the closure it claims.
- **Trusted boundary:** `Kernel.validate_certificate/2` (kernel.ex:379, "re-run the
  totality decision procedure on a registered, type-checked global") is TCB and
  re-derives totality — so it needs no pre-attached certificate. V5 treats it as
  the trusted re-check and does **not** test it directly (that is the kernel's own
  Antigen coverage); V5 tests the untrusted driver that feeds it.

## 3. Properties (two families)

### V5a — certification soundness (end-to-end, adversarial; oracle = known label)

Reusing the `totality/*` known-label construction: a **by-construction diverging**
function placed in a **type position** (so `type_level_fns` reaches it) must be
**rejected** by the whole driver. Correct behavior returns `:ok`; a wrongful
certification is the infection:

- `certify_type_level(env)` on a diverging-in-type-position env **must** return
  `{:error, {:totality_required, _}}`. If it returns `{:ok, _}`, the diverging
  function was certified (or, more insidiously, was *missed* by the closure so it
  was never submitted and the env passed vacuously) →
  `{:violation, {:diverging_certified, env_id}}`.

This is strictly stronger than the existing `totality/diverging` assay: that one
calls `Certificate.terminating?` **directly** on the focus def; V5a exercises the
**closure-reachability + submission** path — the diverging function is only found if
`type_level_fns` reaches it and only rejected if the driver actually submits it. A
closure that under-approximates (misses the diverging function in the type
position) turns a soundness rejection into a silent `{:ok}` — exactly the driver
bug V5a exists to catch.

### V5b — closure completeness (intrinsic; independent reachability oracle)

`type_level_fns(env)` must be a **superset** of an Antigen-owned, independently
written re-derivation of type-position reachability over the same env (walking
family `params`/`indices`, ctor `args`/`result_indices`, transitively via def
bodies — the §7 contract, re-implemented in the assay, independent of
`TotalityClosure`'s private `collect`/`close`, the V1/V2 independent-oracle tactic):

- a global that the independent walk reaches from a type position but that is
  **absent** from `type_level_fns(env)` is `{:violation, {:closure_missed, name}}`.

The independent walk is deliberately a *superset-or-equal* oracle: V5b asserts
`independent ⊆ closure` (the closure misses nothing the contract requires). It does
**not** assert equality — the closure legitimately including *more* (a conservative
over-approximation) is not a soundness problem.

## 4. Assay & injectable seam

New module `Antigen.Assays.TotalityClosureAssay` (name avoids colliding with
`Cure.Elab.TotalityClosure`) with `run/1` → `run/2` (op-map seam), mirroring
`Antigen.Assays.{Elab,Normalizer,Unifier}`. Two assay ids:

| id | property | oracle |
|---|---|---|
| `totality_closure/soundness` | diverging-in-type-position ⟹ rejected | known label |
| `totality_closure/completeness` | `type_level_fns ⊇` independent reachability | independent walk |

No `@assay_fuel`/`Conv` needed — `certify_type_level` and `type_level_fns` are
static structural walks that terminate on their own (per the existing
`Antigen.Assays.Totality` moduledoc: "the certifier is a static structural analysis
that terminates on its own, so no fuel is needed"); the diverging *function's*
non-termination is by-construction (never actually run — the certifier rejects it
structurally).

**Op-map** (`@real`), injecting the **code-under-test** at the assay boundary:

```elixir
%{
  certify: &Cure.Elab.TotalityClosure.certify_type_level/1,
  type_level_fns: &Cure.Elab.TotalityClosure.type_level_fns/1
}
```

Negative controls prove each assay load-bearing:
- `totality_closure/soundness`: a `certify` stub returning `{:ok, env}`
  unconditionally → `{:diverging_certified,…}` on the diverging-in-type-position env.
- `totality_closure/completeness`: a `type_level_fns` stub returning
  `MapSet.new()` (or one dropping a known-reachable name) → `{:closure_missed,…}`.

## 5. Generator

New module `Antigen.Generators.ClosureEnv` producing **fixed catalogs** (the
established fixed-catalog reconciliation — no Corpus/Coverage surgery; reuse the
existing `:def_group` challenge kind if its payload fits, else a lightweight
`:closure_env` kind, typespec-only, wired via `assay_module/1` + a dedicated test):

- `soundness_challenges/0` — envs each carrying a by-construction diverging
  type-level function referenced from a **type position** (a family index telescope
  or a ctor `result_indices` mentioning `{:global, :loop}`), plus its definition.
  Reuse `Antigen.Generators.Totality`'s diverging-def construction for the loop body
  where possible; the **new** generator work is the *env wiring* that places the
  global in a family/ctor type position (open item #1). Include a small all-total
  control env (every type-level function certifies) to show the rejection is
  specific to divergence, not a blanket `{:error}`.
- `completeness_challenges/0` — envs with globals genuinely in type positions
  (direct + one transitive-callee case: a type-position global whose body calls a
  second global), for which the independent walk and `type_level_fns` must agree
  (⊆).

## 6. Invariants (what must never regress)

- No `Cure.Core.*`, `Cure.Elab.*` edits — the driver reached read-only through the
  op-map. No `:meck`, no new dependency.
- `Antigen.Assays.TotalityClosureAssay` contains no literal `StreamData` token
  (the `architecture_test` grep — banked from V1's Stage-5 trip; comments too).
- Assay `run/1,2` returns only `:ok | {:violation, term()}` (matches the `@spec` and
  `Runner.replay_one/1`/`explore/1`'s no-catch-all dispatch). V5's incompleteness
  direction (a genuinely-total function the closure refuses, or the closure
  *over*-approximating) is out of scope — not surfaced as a third outcome.
- The whole clean catalog re-checks `:ok` under the real ops (a real infection ⟹
  STOP and report; do not weaken a test). In particular, if the real
  `certify_type_level` **fails to reject** a diverging-in-type-position env, that is
  a genuine V5a soundness finding — report it, do not adjust the catalog.

## 7. Non-goals

- No fix to the closure driver (V5 *finds*; a surfaced infection is reported, not
  patched, without separate authorization).
- No duplication of the existing `totality/diverging` + `totality/terminating`
  assays (which cover `Certificate.terminating?` directly) — V5 is strictly the
  driver around them.
- No test of `Kernel.validate_certificate` (trusted TCB; the kernel's own coverage).
- No random env fuzzer — a curated fixed catalog (elab pattern). A
  generator-expansion follow-on could widen coverage.
- No SMT (that is V6).

## 8. Open items (for the plan / review to pin)

1. **Env construction placing a global in a type position.** The plan must pin the
   exact `%Env{}` shape (families/ctors/defs maps) such that `type_level_fns`
   reaches `{:global, :loop}` via a family index or ctor `result_indices`, reusing
   `Antigen.Generators.Totality.env_of`/def-construction for the diverging body.
   Confirm `Env.get_def/2`, the `families`/`ctors` field shapes
   (`%{name => %{params, indices}}`, `%{name => %{args, result_indices}}`), and
   whether a family/ctor with a `{:global, :loop}` index is a well-formed enough
   env for `certify_type_level` to run without unrelated errors.
2. **Does the real `certify_type_level` actually reject a diverging-in-type-position
   env?** Confirm by tracing `validate_certificate(env, :loop)` on a by-construction
   diverging `:loop` returns `{:error, _}` (it re-derives via `Certificate`),
   so V5a's baseline `{:error, {:totality_required, :loop}}` holds under real ops.
   If it does NOT reject, that is either a real soundness finding (report) or a sign
   the env wiring didn't actually reach `:loop` (fix the generator, not the assay).
3. **Independent reachability walk fidelity.** The V5b oracle must match
   `TotalityClosure`'s type-position contract exactly (family params+indices, ctor
   args+result_indices, transitive via def bodies) — the plan supplies the walk and
   a checklist mapping each `collect/1` term clause so the oracle neither
   under- nor over-shoots the contract.
4. **Challenge kind.** Decide `:def_group` reuse vs a new `:closure_env` kind by
   whether the existing payload (`%{focus, …}` + `Generators.Totality.env_of`) can
   carry a full pre-built `%Env{}`; if not, add `:closure_env` (typespec-only, like
   `:surface_expr`/`:unify_problem`).

## 9. Test catalog (for the plan — §5 of the plan will expand each)

1. V5a soundness baseline: diverging `:loop` in a family index → `certify` rejects → `:ok`.
2. V5a soundness baseline: diverging `:loop` in a ctor `result_indices` → rejects → `:ok`.
3. V5a all-total control env: `certify` returns `{:ok, _}` → `:ok` (rejection is divergence-specific).
4. V5a negative control: unconditional-`{:ok}` `certify` stub → `{:diverging_certified,…}`.
5. V5b completeness baseline: direct type-position global present in `type_level_fns` → `:ok`.
6. V5b completeness baseline: transitive-callee global present → `:ok`.
7. V5b negative control: empty `type_level_fns` stub → `{:closure_missed,…}`.
8. V5b negative control: `type_level_fns` stub dropping the transitive callee → `{:closure_missed,…}`.
9. Generator+wiring: each catalog non-empty & correctly tagged; `Runner.replay_one/1`
   dispatches both `totality_closure/…` ids and the whole clean catalog is `:ok`.

## 10. Next (umbrella roadmap)

After V5: **V4 erasure/relevance**, then **V6 SMT lint**. **No auto-merge.**
