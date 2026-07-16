# Follow-up work order — OTP metatheory in Cure (open items)

*2026-07-16. Branch `otp-metatheory` (off `feature/idris-parity` HEAD `70a39780`).
The two frontier obligations are discharged and the full suite is green (4190
passed, 1 skipped; Antigen 318/318). This lists everything still open or restricted,
with exact locations, the diagnosis, and the fix approach already worked out. Each
item is independent. Read `2026-07-16-spike-findings-obligation1.md` and
`2026-07-16-let-linearity-soundness-fix.md` first for context.*

## Non-negotiable constraints (same as the parent brief)

- **Ghost-authored commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`,
  no `Co-Authored-By`, no Claude signature.
- **Explicit pathspec on every `git add`/`commit`** (`git add -- <path>`); a
  concurrent agent may share the worktree.
- **TCB = `lib/cure/core/**`.** Changes there are HARD-STOP-and-review: red-green + a
  new Antigen antibody + full Antigen + full suite. TCB changes pre-approved *iff*
  aligned with Idris/Agda/Lean, but still run the full gate.
- **One full `mix test` at a time** (a past concurrent full run caused a kernel
  panic). Prefer scoped `mix test <file>`; run the full suite once, alone, at the gate.
- **Differential oracle:** `mix cure.oracle <cluster>` (live; needs `idris2` at
  `~/Develop/Idris2/build/exec/idris2`), `mix test test/oracle_replay_test.exs`
  (offline replay). Author paired `.cure`/`.idr` under `test/oracle/<cluster>/`.
  For a one-off Idris check use `Cure.Oracle.idris_verdict(Cure.Oracle.default_idris_bin(), path)`.
- **Drive a scratch `.cure` at the elaborator** with
  `Cure.Elab.Program.elaborate(File.read!(path))` → `{:ok, env} | {:error, reason}`.
- The dependent machinery is ONLY in `lib/cure/elab/*` + `lib/cure/core/*`. IGNORE
  `lib/cure/compiler/*` and `lib/cure/types/*` (non-dependent lowering/checker;
  same-named functions are decoys) — EXCEPT the parser (`compiler/parser.ex`) for
  item F.

---

## A. Lift the SINGLE-SIBLING restriction on motive-generalization  ✅ DONE

**Status:** DONE. `elaborate_with_motivegen_branch(es)` and the guard
(`family.indices == [] and proof_name == nil and siblings != []`) now handle m
siblings: motive `λw. Π(s₁: H₁[e↦w]) … Π(sₘ: Hₘ[e↦w]). G[e↦w]` (domain j shifted
+(j-1), G shifted +m), branches `λs₁'.…λsₘ'. body`, case applied to all siblings in
Π-order. The relevance convoy rule already handled n-ary convoys. Verified: a
two-linear-sibling `with` handler accepts, dropping/dup'ing a sibling rejects, all
`rel=same` vs Idris (`test/oracle/otp/ob1_two_sib*`), tests in
`linear_sibling_refinement_test.exs`. NOTE (not a bug): combining two linear
consumptions in an ω-field ctor (`MkPair(use1(c1), use2(c2))`) is rejected by BOTH
Cure and Idris — ω fields force ω-usage; consume to a value via a linear-slotted
function or `let`-bind first.

(Original text follows for history.) The most valuable extension. Restricted
deliberately when landed.

**What works now:** a `with r` handler with EXACTLY ONE scrutinee-dependent sibling
and no user `proof` refines that sibling by motive-generalization and keeps it linear
(e.g. `with r … reply(cap, …)`). See `test/cure/elab/linear_sibling_refinement_test.exs`
and oracle `test/oracle/otp/ob1_branching*`.

**What's restricted:** the guard in `elaborate_with_value`
(`lib/cure/elab/elaborator.ex`) is
`family.indices == [] and proof_name == nil and match?([_], siblings)`. TWO+ siblings,
or a `proof` clause, fall through to the OLD Eq-transport path
(`elaborate_with_eq_branch`), which is linear-hostile (item B). So a `with` with two
linear siblings over-rejects.

**Fix approach (already designed):** generalize `elaborate_with_motivegen_branch` /
`elaborate_with_motivegen_branches` (in `elaborator.ex`, right after
`elaborate_with_eq_branch`) from 1 sibling to m. Build the motive
`λw. Π(h₁: H₁[e↦w]) … Π(hₘ: Hₘ[e↦w]). G[e↦w]` and each branch `λh₁'.…λhₘ'. body`,
apply the case to the original siblings `((case e …) h₁) … hₘ`. `collect_with_siblings`
already rejects sibling-references-sibling, so siblings are independent. **de Bruijn
care:** the sibling j's abstracted type `Hⱼ_abs` (from `abstract_term(Hⱼ_ctx, e, 0)`,
w=var0) sits at Π-position j and must be shifted `+(j-1)`; `G_abs` at the innermost
must be shifted `+m`. The relevance CONVOY rule (`walk_convoy` in `relevance.ex`)
ALREADY handles n-ary convoys (`peel_lambdas`, `x_levels = [depth+arity+j …]`), so no
relevance change is needed — verify with the multi-sibling gates below.

**Red gates:** two-linear-sibling `with` handler ACCEPTS; dropping/dup'ing EITHER
sibling in a branch REJECTS. Mirror in Idris (`test/oracle/otp/`, native `match`
refines multiple siblings for free) → `rel=same`.

**Risk:** medium. E-layer only (kernel re-checks). The de Bruijn shifts are the trap.

## B. `with … proof` clause + multi-sibling still use the linear-hostile Eq-transport

**Status:** open; largely subsumed by A. The Eq-transport encoding
(`elaborate_with_eq_branch`, `eq_arrow_motive`, `collect_with_siblings` in
`elaborator.ex`) wraps a sibling as `transport_case(prf) applied to cap` — a
collapsible `:case` that erases to identity but which relevance ω-scales pre-erasure
(over-counts a dup; masks a drop if naively counted once). A LINEAR sibling under a
`with … proof` therefore over-rejects.

**Fix approach:** after A lands multi-sibling motive-gen, the ONLY remaining user of
Eq-transport is the `proof`-clause case (the user wants the `prf : Eq(T,e,pat)`
binding). Options: (1) keep Eq-transport but make relevance treat the collapsible
transport `{:app, transport_case, cap}` as TRANSPARENT (arg passes at grade 1, since
it erases to identity) AND treat the `λprf`/`λh'` beta-redexes as one-shot — but the
drop-masking issue makes this delicate (see the findings doc's analysis); (2) build
the motive with BOTH the sibling Π-domains AND the Eq-arrow, combining A's motive-gen
with the proof binding. (2) is cleaner. Low priority unless someone writes a
linear-sibling `with … proof`.

## C. Plain `match r` refines siblings  ✅ MOSTLY DONE (one edge remains)

**Status:** MOSTLY DONE. `elaborate_match` (`elaborator.ex`) now, when its STANDARD
path fails on a non-indexed family matched on a VARIABLE with scrutinee-dependent
siblings (`collect_with_siblings`), retries via the shared
`elaborate_motivegen_case` helper (same machinery as item A / `with r`). So the
ergonomic OTP handler works with plain `match r` — no `with` needed:

    fn handle(r: Req, cap :linear ReplyCap(r)) -> Replied = match r
      GetCount() -> reply(cap, R0)  …

Accepts; drop/dup in a branch reject (tests in `linear_sibling_refinement_test.exs`).
The obligation-(1) reach-pin in `pi_grade_source_test.exs` flipped to `{:ok, _}`.

**Why FALLBACK (not proactive):** the retry fires ONLY when the standard path fails,
so working matches are untouched — provably non-regressing on a hot path.

**REMAINING EDGE:** the retry keys on the standard path returning `{:error, _}`. When
a branch body is a bare sibling VARIABLE returned directly (`use_it(r, w: ReplyOf(r))
= match r | GetCount() -> w | …`), the standard path SUCCEEDS building a term and the
KERNEL rejects it later (`:branch_type`) — outside `elaborate_match`, so the retry
never fires. The call-argument shape (`reply(cap, …)`) fails DURING elaboration
(`:index_mismatch`), so it retries fine. To close the edge: gate a `Kernel.check` on
the standard `{:ok}` term when siblings are present and retry motive-gen on failure
(adds a kernel call + a `collect_with_siblings` on every non-indexed var match — weigh
the cost). Repro: `spike7` / `docs/.../spike/spike7_sibling_refine.cure`.

## D. CBV-vs-CBN `let` linearity divergence from Idris

**Status:** intentional, documented; decide whether to "fix". After the soundness fix
(`relevance.ex` `:let` `:not_join`), Cure ACCEPTS `let x = consume(c) in Done` (c
linear, consumed once, result discarded) where Idris REJECTS it (Idris counts `let` by
substitution, so an unused binder makes the value's resources vanish). Cure's accept is
sound under the BEAM's call-by-value semantics. This is why the `let_linear` oracle
cluster OMITS that case rather than marking it `same`. If the project wants strict
Idris parity, change the rule to pure scale-by-binder-usage — but that REJECTS valid
CBV programs (`let _ = consume(linear) in …`) and is a completeness loss. Recommend
leaving as-is; it's a defensible semantic choice, not a bug. See
`2026-07-16-let-linearity-soundness-fix.md`.

## E. Reify gap for INDEX-bearing families in a motive domain

**Status:** pre-existing, reach-pinned (not introduced here). `Quote.reify`
(`lib/cure/core/quote.ex:57`, `split_data_args`) collapses `{:vdata, name, params ++
indices}`; `resplit_data` (`elaborator.ex:~2266`) restores the split via
`Inductive.param_count`. For a PARAM-ONLY family (`ReplyCap(m)`), no misclassification
— which is why motive-gen (A) works for the OTP case. But a motive domain over an
INDEX-bearing family (`Π(w: SNat(k))`, the doc's example at `elaborator.ex:~2593`) can
still trip the split if reified without `resplit_data` applied. This blocks
generalizing motive-gen (A/C) to INDEXED scrutinee siblings. Fix = ensure every motive
domain passes through `resplit_data`, or teach `reify`/the kernel `:data` rule to
carry the split. TCB-adjacent — review carefully.

## F. Formal spec/plan docs for the capability expansions (process debt)

**Status:** open (paperwork). Two non-trivial capabilities landed with red-green +
findings docs but no formal spec→plan (the parent brief asked for "spec → plan if
non-trivial"): (1) higher-order constructor fields (parser, `parse_paren_arrow_tail` /
`collect_paren_arrow` in `lib/cure/compiler/parser.ex`); (2) motive-generalization
sibling refinement (item A/the landed single-sibling version). Everything is green and
documented in the findings docs; write retroactive specs only if the paper-trail is
wanted. No code risk.

## G. Obligation (2) effect-honesty (scoped out by the parent brief)

**Status:** intentionally out of scope. `Std.Otp.Proof`'s `spawn_actor`/`post` are
PURE (no `Effect`) — faithful to NVLang (which has no effect tracking) and to the
message-type-safety focus. If someone wants the send algebra to also track effects,
`spawn`/`post` would return `Effect(…)` and the client would thread `let … <- …`. The
parent brief explicitly deferred this (§9 "out of scope"). Not a roadblock.

---

## Where things live (quick map)

| Path | What |
|------|------|
| `lib/std/otp_proof.cure` | `Std.Otp.Proof` — both obligations, kernel-checked |
| `lib/cure/elab/elaborator.ex` | `elaborate_with_value` (guard for A), `elaborate_with_motivegen_branch(es)`, `elaborate_with_eq_branch` (B), `collect_with_siblings`, `eq_arrow_motive`, `abstract_term`, `resplit_data` (E) |
| `lib/cure/elab/relevance.ex` | `:let` `:not_join` (D), `walk_convoy`/`walk_convoy_branches`/`peel_lambdas`/`scale_by_uses`/`lambda_depth` (convoy rule) |
| `lib/cure/compiler/parser.ex` | `parse_type_atom` `:lparen`, `parse_paren_arrow_tail`, `collect_paren_arrow` (F) |
| `lib/cure/core/quote.ex` | `reify`/`split_data_args` (E) |
| `test/oracle/otp/`, `test/oracle/let_linear/` | differential clusters (accept + negatives) |
| `test/cure/elab/{linear_sibling_refinement,let_linear_soundness,higher_order_ctor_field,pi_grade_source}_test.exs` | behavioral tests |
| `docs/research/process-types/2026-07-16-*.md` | brief, findings, soundness-fix, this work order |

**Suggested order:** A (unblocks B/C machinery) → C → B → E (only if indexed siblings
needed). D, F, G are decisions/paperwork, not code roadblocks.
