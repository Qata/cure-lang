# Antigen V3 — Elaborator Soundness (Phase 1) Design

**Status:** approved (design gate, 2026-07-03). First phase of the
untrusted-machinery initiative ([umbrella spec](2026-07-03-antigen-untrusted-machinery-design.md),
task #66); V3 leads per the operator's resolution of open-question #1.

## 1. Problem

Antigen today property-tests the **trusted kernel** (`Cure.Core.*`). The
`Cure.Elab.*` elaborator is **untrusted**: it lowers surface syntax to core
terms. Nothing re-validates that emitted core. The existing `elab/completeness`
assay (`Antigen.Assays.Elab`) reads only the **accept/reject bit** from
`Program.elaborate/1` — it trusts the elaborator's self-reported `{:ok, env}`.

So this soundness hole is invisible today: an elaborator that **accepts** a
surface program but emits a core term that is **ill-typed** — a wrong de Bruijn
index, a mis-inserted implicit, a body annotated with a type it does not have —
is caught by neither Antigen nor the kernel. The kernel only ever sees core it is
asked to check; if the elaborator never asks, the bad core ships. This is the
single highest-value untrusted-machinery gap, and the cheapest to close: it needs
**no new generator** — only a new assay over the existing elaborator-program
generators.

## 2. The property (differential; kernel is the oracle)

> **Elaborator soundness.** For a construction-guaranteed well-typed surface
> program `src`, if `Program.elaborate(src) = {:ok, env}`, then **every function
> definition the elaborator emitted** — each `{name, %{type: ty, body: core}}` in
> `env.defs` — must be **independently accepted by the trusted kernel at its
> emitted type**: the kernel re-derives the type of `core` and confirms it is
> convertible to `ty`.

Decision procedure per def:

1. Build the checking context/signature from `env` (the kernel's own context, so
   sibling defs and builtins are in scope — a def body may reference other
   globals by `{:global, name}`).
2. `Kernel.infer(ctx, core)`:
   - `{:error, e}` → **infection** `{:core_ill_typed, name, e}` — the elaborator
     emitted a core term the kernel rejects outright.
   - `{:ok, inferred}` → evaluate the emitted type `ty` to a value `ty_v` in the
     same context and check `Conv.conv_values?(inferred, ty_v, depth, sig)`:
     - not convertible → **infection** `{:type_annotation_wrong, name,
       %{inferred: inferred, declared: ty}}` — the elaborator emitted a *type
       lie*: the body is checkable but not at the type it was annotated with.
     - convertible → this def is sound; continue.
3. All defs sound → `:ok`.

**Why infer + Conv, not a bare `Kernel.check(ctx, core, ty_v)`:** `check` alone
verifies the body is checkable *at the declared type*, but a body that is
checkable at that type yet was **also** derivable at a different (correct) type
would still pass — `check` cannot surface an annotation that is wrong-but-still-
satisfiable. Infer-then-Conv re-derives the type independently and compares,
catching both "emitted ill-typed core" and "emitted a wrong type annotation."
(An implementation that finds `infer` insufficient for some former may fall back
to `check` for that former — see §7 open items — but infer+Conv is the default.)

### 2.1 Which defs are checked

The assay re-checks **every** function def in `env.defs`. `env.defs` after
`Program.elaborate/1` holds the program's local defs **plus** imported/prelude
function defs merged in (`merge_env`). Imported and prelude defs are themselves
well-typed, so they pass the kernel re-check and do not produce infections — the
program's own (under-test) defs are the effective target. Checking all defs is
therefore **sound** (no false infection from prelude) and needs no access to the
private `Program.local_def_names/1` (which requires the surface AST the assay
does not hold). Restricting to local defs is a possible later optimization
(§7), not a correctness requirement.

Builtin *type families* (`Bool`, `Nat`) are seeded into the inductive registry,
not `env.defs`, so they are not (and need not be) re-checked here — positivity of
the builtins is the kernel/Positivity assay's job, not V3's.

### 2.2 Holes

A def body may contain `{:hole, _}` (the kernel accepts holes: `check`'s hole
clause returns `:ok`). A hole-bearing body is a *legitimately incomplete*
program, not an unsound elaboration, so it must **not** infect. `infer` on a hole
is undefined in general, so before checking, the assay treats a body for which
`Erase.has_hole?/1` is true as **not under test** (skipped), exactly as
`Program.hole_goals/1` and `check_codegen_ready/1` already special-case holes.
The `elab_complete` generators produce complete (hole-free) programs, so in
practice no def is skipped; the guard is defensive.

## 3. Components

### 3.1 New assay clause — `Antigen.Assays.Elab`, id `elab/soundness`

Added to the existing `Antigen.Assays.Elab` module (it already owns the
`:elab_program` kind). Signature mirrors the module's other clauses:

```
run(%Challenge{kind: :elab_program, assay: "elab/soundness", payload: p}) ::
  :ok | {:violation, term()}
```

- Elaborate `p.src` through the same crash-normalizing wrapper the module already
  uses (`{:ok, env} | {:error, e} | {:raise, e}`). A `{:error, _}` here is **not**
  a V3 infection — an *unsound reject* is the `elab/completeness` assay's
  concern, and re-reporting it under `elab/soundness` would double-count. V3 only
  fires when the elaborator **accepted** (`{:ok, env}`) and the emitted core fails
  the kernel re-check. A `{:raise, _}` (elaborator crash) **is** a V3 infection
  class `{:elaborator_raised, p.id, e}` (a crash mid-elaboration is a real defect
  regardless of vertical).
- On `{:ok, env}`: fold over `env.defs`, apply the §2 decision procedure, return
  the first infection (deterministic — `env.defs` iterated in a fixed key order)
  or `:ok`.

### 3.2 Injectable oracle seam — `run/2`

Following Run C's sensitivity pattern, add a `run/2` arity taking an injectable
kernel-op map `k` (`%{infer: …, conv: …, eval: …}`), with `run/1` delegating
through a private `@real_kernel` map so existing behavior is byte-identical. This
seam exists **solely** to let the negative-control test (§5) inject a broken
elaborator/kernel without touching the TCB or using `:meck`.

### 3.3 Generator — `elab/soundness`-tagged challenges

Reuse the existing `elab_complete.ex` surface-program construction (the same
generator that feeds `elab/completeness`). Emit challenges tagged
`assay: "elab/soundness"` carrying the same `%{id, src}` payload. Two wiring
options (plan decides; both are pure additions):

- **(a)** a thin generator variant in `elab_complete.ex` that re-tags each
  generated program with `elab/soundness` (its own `Antigen.Gen` entry), or
- **(b)** a shared program generator both assay ids draw from.

Either way, **no new surface-program construction logic** — V3's whole economy is
that it reuses the completeness generator's well-typed programs. Wire the new gen
into `Mix.Tasks.Antigen.default_gen/0` (weight 1) and the assay id into the
runner's assay registry (`assay_module/1`), so `mix antigen` exercises it.

## 4. Data flow

```
elab_complete generator ──▶ Challenge{kind: :elab_program,
                                       assay: "elab/soundness",
                                       payload: %{id, src}, label: :well_typed}
        │
        ▼ (runner dispatch: assay_module("elab/soundness") = Antigen.Assays.Elab)
Program.elaborate(src)
        │  {:ok, env}
        ▼
for {name, %{type: ty, body: core}} <- env.defs, not has_hole?(core):
        Kernel.infer(ctx_of(env), core)
          ├─ {:error, e} ──────────────────▶ {:violation, {:core_ill_typed, name, e}}
          └─ {:ok, inferred}
                 Conv.conv_values?(inferred, eval(ty), depth, sig)
                   ├─ false ────────────────▶ {:violation, {:type_annotation_wrong, name, …}}
                   └─ true  ── continue
        │
        ▼ all defs sound
       :ok
```

On infection the runner minimizes via the Run D triage (`elab_program` is a
triage no-op for term-shrink, but the pipeline is unchanged) and banks the
antibody. The C2 record round-trips `p.src`, so replay is generator-independent.

## 5. Testing strategy

Behavioral, immutable tests (strict TDD). New file
`test/antigen/assays/elab_soundness_test.exs`.

1. **Baseline soundness (real kernel).** A representative `elab_complete` program
   whose elaboration is genuinely well-typed → `run/1` returns `:ok`. Pins that
   the assay does not false-positive on correct elaboration.
2. **Negative control — ill-typed core (load-bearing).** Via the `run/2` seam,
   inject a kernel/elaborator stub whose emitted `env.defs` contains a def whose
   `body` does not have its `type` (e.g. body `{:ctor, :S, [{:ctor, :Z, []}]}`
   annotated as `Bool`). The assay MUST return
   `{:violation, {:core_ill_typed | :type_annotation_wrong, …}}`. Without this a
   green run would be vacuous — this proves the kernel re-check is load-bearing.
3. **Reject is NOT a V3 infection.** A surface program the elaborator *rejects*
   (`{:error, _}`) → `run/1` returns `:ok` under `elab/soundness` (that failure
   is `elab/completeness`'s to report; V3 must not double-count).
4. **Elaborator crash is an infection.** A `src` that makes `elaborate` raise →
   `{:violation, {:elaborator_raised, …}}` (reusing the module's existing
   crash-normalizing wrapper).
5. **Hole-bearing def is skipped, not infected.** An `env.defs` entry whose body
   contains `{:hole, _}` → not treated as an infection (defensive; the real
   generators produce hole-free programs).
6. **Runner wiring.** `elab/soundness` resolves through `assay_module/1` and a
   generated `elab/soundness` challenge flows through `explore/1`'s infection
   branch identically to any other kind (a short `Runner.explore` with an
   injected always-sound assay bank nothing; determinism preserved).
7. **Determinism / regression.** `run/2` with `@real_kernel` is byte-identical to
   `run/1`; the existing `elab/completeness`, `elab/metamorphic`, `elab/erasure`
   clauses are untouched (their tests stay green).

## 6. Invariants

- **Read-only TCB.** `Cure.Core.*` unchanged; the kernel (`infer`/`Conv`/`eval`)
  is the oracle, reached only through the assay's `@real_kernel` map.
- **Deterministic + banked + replayable.** Fixed iteration order over `env.defs`;
  no RNG/clock in the assay. Fuel for any normalization uses the same committed
  `@assay_fuel` floor as the term assays (500_000), so a banked antibody replays
  identically.
- **StreamData quarantine.** The assay lives under `lib/antigen/assays/` and the
  generator under `lib/antigen/generators/` — inside the quarantined glob, so the
  generator may use `StreamData` and the assay may not (unchanged from the
  existing Elab module).
- **No new dependency, no `:meck`.** The `run/2` seam is the only injection path.
- **Known-label + negative control.** Every generated `elab/soundness` challenge
  is `label: :well_typed` (a positive control — must stay sound); test #2 is the
  negative control (a deliberately-broken emission must be caught).

## 7. Open items (for the plan / review to pin — not blockers)

1. **`infer` vs `check` per former.** Default is `Kernel.infer` + `Conv`. If a
   Core former the elaborator emits is not directly inferable (only checkable),
   the plan pins a `check(ctx, core, eval(ty))` fallback for that former, keeping
   the annotation-mismatch catch where infer is available.
2. **Exact `ctx`/`sig` construction from `env`.** The plan pins the precise call
   (mirroring how `Kernel`/`Conv` are invoked elsewhere with an elaborated env —
   e.g. `Context`/signature builders already used by the term assays).
3. **Type stored as Term vs Value in `env.defs`.** If `ty` is already a value, the
   `eval` step is skipped; if a term, it is evaluated once. The plan pins which,
   from the elaborator's def-storage convention.
4. **Local-def restriction (optimization).** Re-checking imported prelude defs on
   every challenge is redundant (they always pass). A later optimization may
   restrict to local defs via a re-exposed seam; not required for correctness.

## 8. Non-goals (Phase 1)

- No V1 (normalizer), V2 (unifier), V4/V5/V6 — those are later phases in the
  umbrella roadmap.
- No new surface-program generator logic (reuse `elab_complete`).
- No elaborator *fix*: V3 **finds** unsound elaboration; fixing any infection it
  banks is separate follow-up work.
- No git-bisect / kernel-weakening sensitivity matrix (that was Run C's scope);
  V3's single negative control (§5.2) is the load-bearing proof for this vertical.
