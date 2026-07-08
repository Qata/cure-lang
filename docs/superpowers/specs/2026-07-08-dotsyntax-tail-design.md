# Dot-syntax tail — close ledger row #5's named-implicit caveats

**Date:** 2026-07-08
**Status:** Approved (operator batch authorization: parity-queue initiative C,
item 1 of 3 — "dp01/dp02 dot syntax (#5 tail)"; match-embedded ctor guards and
Nat→Int erasure follow as their own chains)
**Topic:** dotsyntax-tail

## 1. Problem — three documented caveats keep row #5 at 🟡

The explicit dot-pattern / named-implicit machinery itself landed on
2026-07-04 (`5409184`; ledger row #5): `{k = .e}` on a constructor pattern
asserts the forced erased index `k` is convertible to `e`, wrong dots reject
with `{:forced_pattern_mismatch,…}`, oracle `dotpat` (dp01/dp01b/dp02/dp03
accept + dp06 reject) and `nidot` (ni01 accept + ni02 reject) all `same`. The
row stays 🟡 because of three caveats written into it, all re-verified against
the current worktree (branch `autopilot/kernel-parity-batch`):

- **C-a (missed check on the carried-eq path).** `elaborate_matched_branch/10`
  dispatches `_solved_or_trivial when carried != nil` to
  `elaborate_carried_eq_branch/10` (`lib/cure/elab/elaborator.ex:3181`,
  `:3357`), which receives neither the surface pattern nor the verdict
  substitution and never calls `check_named_implicits/7`. A named-implicit
  annotation on such a branch is **silently discarded** — a *wrong* dot is
  accepted where Idris rejects. Not a soundness hole (the annotation binds
  nothing; the kernel still checks the branch), but a faithfulness bug and a
  false sense of a checked assertion.
- **C-b (spurious error when the body references the scrutinee).**
  `refine_scrutinee_in_body/5` (`elaborator.ex:3533`) substitutes the raw
  surface pattern into the branch body via `subst_surface_var`. If the pattern
  carries a `{:named_implicit_pat,…}` argument, that non-expression node lands
  in expression position and elaboration fails with
  `{:named_implicit_not_in_pattern,…}` (`elaborator.ex:82`) — a spurious
  reject of a program Idris accepts.
- **C-c (unforced named implicit: reject vs bind).** Cure rejects any named
  implicit whose telescope position was not pinned by index inversion
  (`{:named_implicit_unforced, name}`, `elaborator.ex:3269`). Idris **binds**
  it as a quantity-0 pattern variable. Probe evidence (idris2 `--check`,
  2026-07-08, scratchpad `nidot-probe/`): existential
  `MkP : {0 k : Nat2} -> Vec k -> P` — `f (MkP {k = kk} v) = Z` **accepts**
  (binding, erased-only use); `g (MkP {k = kk} v) = kk` **rejects** ("kk is
  not accessible in this context"). Cure rejecting the *binding itself* is a
  genuine cure-stricter divergence with no soundness rationale.

## 2. Design — three scoped fixes, E-layer only

No kernel change anywhere in this chain. The named-implicit machinery is
check-and-discard (C-a, C-b) or a naming-of-an-existing-binder concern (C-c);
`{:case}` terms, motives, and the index unifier are untouched.

### 2.1 C-a: run the forced check on the carried-eq path

Thread the surface `pattern` and the verdict's solved substitution into
`elaborate_carried_eq_branch` and call the existing `check_named_implicits/7`
with the same inputs the plain path uses, in the pre-proof branch frame
(`branch_ctx0 = extend_context(ctx, telescope, scrut_param_vals)`
specialized by the same subst — exactly the frame `forced_check_probe/7`
documents). The verdict is already in scope at the dispatch site
(`{:solved, s}` / `:trivial` → `%{}`); today it is simply not passed down.
Failure propagates identically to the plain path
(`{:forced_pattern_mismatch,…}` rejects the branch).

### 2.2 C-b: strip annotations before body substitution

Named-implicit arguments are annotations, not expression material. In
`refine_scrutinee_in_body` (or immediately before its `subst_surface_var`
call), rewrite the pattern to its positional-only form (drop
`{:named_implicit_pat,…}` args — the same filter `constructor_pattern`
already applies via `named_implicit_arg?/1` at `elaborator.ex:3609`) so the
substituted body sees the constructor expression Idris/Lean would substitute.
The annotation is still checked by `check_named_implicits` on its own path;
nothing is lost.

### 2.3 C-c: bind unforced variable-form named implicits at quantity 0

For `{k = <inner>}` where `named_implicit_forced_value/4` reports unforced:

- **`inner` is a bare variable** (surface `{:variable,…,name}`; not a dot
  form): bind it. The erased telescope slot already exists in `branch_ctx` —
  it is anonymized in `branch_names` today (`branch_scope(quantities,
  pattern_vars)` names only present positions). The fix names that slot with
  the written variable. Quantity stays `0`; the existing relevance layer
  polices usage exactly as Idris does (erased-position use accepts,
  relevant use rejects with the standing `{:erased_used_relevantly,…}`).
  Shadowing an existing name follows the ordinary innermost-wins rule the
  branch scope already implements.
- **`inner` is a dot form `.e` or any non-variable**: keep the
  `{:named_implicit_unforced, name}` error. A dot asserts agreement with a
  unification-pinned value; when nothing was pinned there is nothing to check
  (and Idris's equivalent — a non-variable pattern for an unforced erased
  implicit — is first-class matching Cure does not do on erased positions).
  The error text gains a hint distinguishing "use a variable to bind" from
  the old blanket message.
- On a **forced** position, a bare-variable inner keeps today's semantics
  (convertibility check against the pinned value — Idris's `{w = a}` with
  `a` in scope behaves the same way there).

## 3. What is NOT changed

- **Kernel/TCB untouched** — no new Core forms, no conv/normalise change.
- Erasure/emit untouched: C-c names an existing erased binder; it never
  becomes present (`quantities` unchanged), so `emit.ex` anonymization and
  the zero-footprint guarantee hold.
- Bare positional `.e` stays parse-level-guarded groundwork (ledger: proven
  structurally inexpressible for Cure's erased-implicit indices; no dead
  syntax gets elaboration).
- The classic pipeline (`lib/cure/compiler/*`, `lib/cure/types/*`) is not
  touched — this is all dependent-elaborator work.

## 4. Oracle probes (differential, cluster `nidot`)

New paired fixtures, each run through `mix cure.oracle nidot` (destructive —
restore `verdicts.json` via `git checkout` before investigating any drift):

| Fixture | Shape | Expected |
|---|---|---|
| `ni03_carried_wrong_dot_neg` | carried-eq branch (sibling arg's type mentions the carried index, per `detect_carried_index`) + wrong dot `{k = .(S(m))}` | reject/reject `same` (today: Cure accepts — the C-a red) |
| `ni04_body_scrutinee_ref` | named implicit + branch body referencing the scrutinee name | accept/accept `same` (today: Cure rejects — the C-b red) |
| `ni05_unforced_bind_erased` | existential ctor, `{k = kk}` bound, `kk` used only in an erased position (e.g. a type annotation / erased implicit argument) | accept/accept `same` (today: Cure rejects — the C-c red) |
| `ni06_unforced_bind_relevant_neg` | same binding, `kk` returned relevantly | reject/reject `same` (guards the quantity-0 discipline both sides) |
| `ni07_carried_right_dot` | carried-eq branch + correct dot | accept/accept `same` (guards C-a against over-rejection) |

Idris sides mirror the probe programs from §1's evidence. If Idris rejects
`ni07`'s carried shape for an unrelated reason, simplify the shape until both
sides express the same program — never hand-write a verdict.

## 5. Testing (TDD; red first, immutable once green)

1. **Red unit tests** per caveat in `test/cure/elab/` (new
   `named_implicit_tail_test.exs`): C-a wrong-dot-on-carried rejects; C-b
   scrutinee-in-body accepts; C-c bind-erased accepts / bind-relevant rejects
   with `{:erased_used_relevantly,…}` / dot-on-unforced still errors.
2. Existing pins stay green untouched: `dotpat`/`nidot` current fixtures,
   `dot_pattern_parse_test.exs`, `carried_index_sibling_test`,
   forced-check Antigen vertical (#24, `forced_check_probe` shim — extend
   with a carried-frame case mirroring C-a).
3. Oracle: add §4 fixtures, run `mix cure.oracle nidot` (and `dotpat`
   untouched byte-identical), replay test green.
4. Gate (sequential, one at a time): full Antigen → full `mix test` →
   `mix cure.check.examples` → oracle replay.
5. Ledger row #5 graduates 🟡 → ✅ (all three caveats closed; the row's
   remaining text records C-c's variable-bind semantics and the kept
   dot-on-unforced error).

## 6. Out of scope

- Match-embedded constructor guards and Nat→Int erasure (next chains in
  initiative C).
- First-class matching on erased positions (non-variable patterns for
  unforced implicits) — Idris feature with no Cure counterpart; recorded, not
  built.
- `{:named_implicit_pat,…}` in nested (non-outermost) pattern positions:
  whatever the current parser/`desugar_nested_arms` support is, it is
  preserved, not extended.
