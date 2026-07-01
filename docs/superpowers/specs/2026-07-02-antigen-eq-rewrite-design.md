# Antigen Eq/rewrite vertical — design

**Date:** 2026-07-02
**Status:** approved design (operator gate passed); this is the ③ sub-project of
the Eq/rewrite–case-refinement work. It ships FIRST as the audit net for ②
(the case-refinement pattern-fragment unifier).

## 1. Goal

A deep-cut Antigen soundness vertical that probes the kernel's **propositional
equality** surface — `{:eq}` / `{:refl}` / `{:rewrite}` in `Cure.Core.Kernel` —
known-label by construction, structurally mirroring the existing indexed-case
vertical (`Antigen.{Generators,Assays}.Indexed`). It is the **safety net** for
the forthcoming ② initiative: ② reworks `case`-refinement into a pattern-fragment
unifier and deliberately keeps `rewrite` as the *propositional escape hatch*, so
`rewrite`/`Eq` soundness must be pinned down by an automated net before ② touches
that region of the TCB.

## 2. Why

- The Antigen audit left "a proper Eq/rewrite obligation probing the reworked
  `{:rewrite,…}` normalization" explicitly on file (locked decision, Antigen
  memory). This is that obligation.
- ② is a trusted-kernel refactor. Per the locked decision it must be done "with
  the Antigen suite green as the net." Case-refinement (definitional) and
  `rewrite` (propositional) are **complementary**, not identical: unification
  discharges constructor-form equations and impossible branches; `rewrite`
  transports along an opaque proof `p : a = b`. ② keeps `rewrite` as the escape
  hatch — this vertical guards it.

## 3. Kernel surface under test (facts established by reading the code)

- `infer({:eq, ty, a, b})` — Eq formation: `ty` must be a sort; `a`, `b` must
  both `check` at `ty`; result `{:vtype, level}` (kernel.ex:96).
- `infer({:refl, a})` — `refl a : Eq A a a` where `A = infer(a)` (kernel.ex:105).
- `check({:refl, a}, {:veq, ty, av, bv})` — accepts **iff** `a : ty` AND
  `conv(av, bv)` AND `conv(eval a, av)` (kernel.ex:260). This is the audit's fix:
  the old checker accepted any atom as an equality proof. **This guard is what
  makes the proof-erasing computation rule sound** and is a primary probe target.
- `infer({:rewrite, proof, motive, body})` — `proof : Eq A a b`; `body` must
  `check` at `apply(M, a)`; result `apply(M, b)` (kernel.ex:112). Body mismatch →
  `:rewrite_premise`; non-equality proof → error via `ensure_eq`.
- **Computation rule:** `eval({:rewrite, _p, _m, body}) = eval(body)` (eval.ex:63)
  — transport is proof-erasing at the value level; only the *type* moves
  `M a → M b`. Consequence: a naive "normalize the body then re-check" assay
  would MISLABEL (the erased body has type `M a`, not the def's declared `M b`).
  **All obligations here are therefore stated as typing obligations**, never as
  value-reduction stability.

## 4. Obligations (known-label; run each def through `Kernel.check_def/2`)

Each builder emits a `Challenge` (kind `:rewrite_eq`) whose `:well_typed` /
`:ill_typed` label is correct by construction. The assay's oracle is the label:
the kernel must accept iff `:well_typed`. `:ill_typed` accepted = **soundness
infection** (antibody + red-green kernel fix); `:well_typed` rejected =
incompleteness (reported per criterion §5, patched only if cheap and sound).

### 4.1 Eq formation
`Eq A a b : Type` requires `a, b : A`.
- well-typed: `Eq Dec Causal Dcoupled` in a context where both are `: Dec`.
- ill-typed: an endpoint at the wrong type (e.g. `Eq Dec Causal MkFoo` with
  `MkFoo : Foo`) → rejected.

### 4.2 refl typing + reflexive-conversion guard (audit-fixed clause)
- well-typed: `refl a : Eq A a a`; and `refl a : Eq A a a'` where `a ≡ a'`
  definitionally (endpoints convertible but not syntactically identical — a
  redex/normalization case) → accepted (completeness of the conv check).
- ill-typed (**soundness**): `refl a` checked against `Eq A a b` with `a`, `b`
  **not** convertible → rejected (`:not_definitionally_equal`). This is the
  guard that keeps proof-erasing transport sound; its failure is the classic
  "any-atom-is-a-proof" hole.

### 4.3 rewrite premise discipline
`rewrite (p : Eq A a b) (M) (body : M a) : M b`.
- well-typed: `body : M a` → accepted.
- ill-typed (**soundness**): `proof` is not an equality (e.g. a plain ctor) →
  rejected (`ensure_eq`).
- ill-typed (**soundness**): `body` does not check at `M a` → rejected
  (`:rewrite_premise`).

### 4.4 transport result-type correctness (+ refl coherence)
The kernel must assign the **transported** type `M b`, not the source `M a`.
- well-typed: a def declared `: M b` with body `rewrite (p:a=b) M (body:M a)` →
  accepted.
- ill-typed (**soundness**): the SAME body declared at a non-convertible source
  type `M a` (with `a ≢ b`) → rejected. Accepting it would prove the kernel left
  the type at `M a` (no transport) — an unsoundness given `M a ≢ M b`.
- refl coherence: `rewrite (refl a) M (body : M a) : M a` (b = a) → accepted; the
  transport is vacuous, the def declared `: M a` typechecks.

## 5. Reporting criteria (same as prior verticals)

- **Infection** = kernel accepts an `:ill_typed` challenge, or rejects a
  `:well_typed` one ⇒ the assay returns `{:violation, …}` ⇒ **red** suite.
- A confirmed **soundness** hole (ill-typed accepted) ⇒ fix red-green in the
  kernel AND bank the counterexample as a never-pruned antibody in
  `test/antigen/corpus.sexp`.
- A pure **incompleteness** (well-typed rejected, no unsoundness) ⇒ reported;
  patched only if the fix is cheap and obviously sound, else documented (the
  indexed-case 4.3 precedent).

## 6. Architecture (mirror the indexed-case vertical)

- `Antigen.Generators.Rewrite` — one builder per obligation, each taking
  `:well_typed | :ill_typed` and returning `Challenge.t()` with kind
  `:rewrite_eq` and payload `%{families, def_name, def_type, def_body}`. Reuse
  the `env_of/1` + private `challenge/6` helper shape from `Generators.Indexed`.
  Shared families: `Dec` (`Dcoupled`/`Causal`), `Foo` (`MkFoo`) for wrong-type
  endpoints, and a tiny index family for the motive `M` in 4.3/4.4.
- `Antigen.Assays.Rewrite` — `run(%Challenge{kind: :rewrite_eq})`: rebuild env
  via `Generators.Rewrite.env_of/1`, `Kernel.check_def`, return `:ok` iff
  acceptance matches the label, else `{:violation, {:wrongly_accepted|:wrongly_rejected, …}}`.
- `Antigen.Challenge` — add kind `:rewrite_eq`; encode/decode uses the same
  tab-delimited base64 `Serialize` envelope + `@known_atoms` interning as
  `:indexed_case` (the payload shape is identical, so this is additive).
- `Antigen.Runner` — register the `:rewrite_eq` generators in the explorer sweep;
  register the assay in the replay registry so `mix test` statically replays any
  banked `:rewrite_eq` antibodies.
- `Antigen.Coverage` / seeds — bank coverage-deduped seeds for each obligation.
- **Arch rule (enforced):** nothing under `Antigen.Generators.*` /
  `Antigen.Assays.*` may import StreamData (existing architecture test).

## 7. Tests (TDD, mirror `test/antigen/{generators,assays}/…`)

For each obligation:
1. **Generator self-test** — the `:well_typed` builder's rebuilt env + def
   actually `check_def == :ok`; the `:ill_typed` builder's `check_def` returns
   `{:error, _}`. This proves the label is correct by construction (guards
   against a vacuous-green generator).
2. **Assay test** — `Assays.Rewrite.run/1` returns `:ok` on a correctly-labelled
   challenge and `{:violation, _}` on a deliberately mislabelled one.
3. **Wiring** — `:rewrite_eq` round-trips through `Challenge` encode/decode; the
   replay registry resolves the assay; a banked seed replays statically.
4. **Coverage/seed** — one seed per obligation lands in `seeds.sexp`.

## 8. Invariants (carried from the Antigen design bible)

- Known-label by construction; **no** term generator, **no** external oracle.
- Pure verdicts (infection ⇒ red; no xfail/open); non-halting explorer;
  read-only replayer.
- `corpus.sexp` / `seeds.sexp` are append-only and **never pruned**.
- Kernel edits happen **only** if an obligation surfaces a confirmed soundness
  hole, and then only red-green with a banked antibody (indexed-case 4.1
  protocol). Absent a hole, this vertical adds **zero** TCB change.
- Generators/Assays must not import StreamData.

## 9. Net role for ②

This suite is the acceptance net for the ② case-refinement unifier. ② keeps
`rewrite` as the propositional transport; any ② change that regresses `Eq` /
`refl` / `rewrite` soundness turns this suite red. ② is scheduled only once this
vertical is green and banked.
