# Neutral-Application Sort Inference (Sigma D1 kernel enabler) — Design

**Status:** approved design (operator standing batch authorization; TCB change pre-approved under the Agda/Lean-alignment blanket — this rule is exactly how both kernels type neutral type-valued applications — with the FULL verification gate mandatory).
**Layer:** K (TCB, `lib/cure/core/kernel.ex` — one new clause + nothing else) + tests/Antigen/oracle.
**Batch:** task #13 part D1, worktree `kernel-parity-batch`, branch `autopilot/kernel-parity-batch`. D2 (primitive-Sigma retirement) is a separate, chained spec that depends on this landing.

## §0 The gap (verified in this worktree, 2026-07-08)

`infer_type_value_sort/2` (`lib/cure/core/kernel.ex:606-665`) classifies motive-body values in `check_motive_wf/4` (`kernel.ex:591-604`). Its clauses: `{:vtype,_}` (606), `{:vneutral, {:nvar,_}}` (613 — bare variable only), `{:vint_type}`/`{:vfloat_type}` (622-623), `{:vdata,_,_}` (625), `{:vpi,…}` (643), `{:vsigma,…}` (654), fallthrough `{:error, :not_a_type_value}` (665). There is **no clause for a neutral APPLICATION** `{:vneutral, {:napp, …}}`.

Consequence: a dependent eliminator whose motive applies a type-family *variable* — the canonical case being Sigma's second projection, `second : (p: MySigma(a, b)) -> b(first(p))` with `b : (a) -> Type` — evaluates its motive body to `{:vneutral, {:napp, …}}`, hits the fallthrough, and `check_motive_wf` maps it to `{:error, :bad_motive}` (`kernel.ex:600-602`). This blocks ALL user-defined dependent eliminators into `b(x)`-shaped types, not just Sigma's — probe-verified earlier (the MySigma stdlib probe: family + `mk_pair` + `first` all elaborate; `second` alone fails `:bad_motive`).

A load-bearing fact that dictates the design (verified at `kernel.ex:197-224`): the `:case` rule **never checks the motive as a term** — `motive_value = Eval.eval(motive, …)` (207) straight into `check_motive_wf` (209). The sort walk is the motive's ONLY validation. The new clause therefore may not trust anything about the application (the untrusted elaborator built it); it must fully validate, including the spine arguments.

**Stale-scout warning for reviewers/planners:** an earlier scoping report for this task read the MAIN repo checkout, not this worktree, and reported pre-batch facts (live `{:eq}`/`{:veq}` primitives, a `{:veq}` clause in this very function). Those are false here — the identity-type retirement IS complete in this tree (`ccbe2d0`, `727a673`, `11ea830`; validator `no_eq_node: :reject`). Every anchor in this spec was re-verified against the worktree; re-verify anything else against `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/kernel-parity-batch`, never the parent checkout.

## §1 Goal

`check_motive_wf` accepts a motive whose body is a neutral type-valued application — `b(x)`, `b(first(p))`, `F(n)` for a global type-family def — with the sort the head's Pi codomain assigns, while rejecting exactly as before: applications of non-type-valued heads (`g(x)` with `g : (a) -> Nat`), ill-typed arguments, and anything the kernel cannot fully validate. The MySigma `second` probe elaborates end-to-end; Idris agrees (differential probe).

## §2 Design — one clause: reify the neutral, run the trusted term-level `infer/2`

```elixir
# A neutral APPLICATION is a valid type iff the kernel's own term-level
# judgement says so: reify the spine back to a term and infer it. `infer/2`'s
# `{:app, f, a}` rule (kernel.ex:155-161) resolves the head's type (ctx var or
# signature global), CHECKS each argument against the instantiated Pi domain,
# and returns the codomain — full validation, nothing trusted from the
# (untrusted) elaborator that assembled the motive. Accept only a `{:vtype, l}`
# result: `b(first(p))` with `b : (a) -> Type` sorts at `l`; `g(x)` with a
# non-type codomain infers to something else and stays `:not_a_type_value`.
defp infer_type_value_sort(ctx, {:vneutral, {:napp, _, _} = neutral}) do
  term = Quote.reify_neutral(neutral, Context.length(ctx))

  case infer(ctx, term) do
    {:ok, {:vtype, level}} -> {:ok, level}
    _ -> {:error, :not_a_type_value}
  end
end
```

Placed with the other `infer_type_value_sort` clauses (after the `{:nvar}` clause at 613). Exact `Quote.reify_neutral` arity/name is verified at plan time against `lib/cure/core/quote.ex` (~101-108: it handles `{:nvar}`, `{:napp}`, and projections; the plan pins the real signature — if it is not public or takes different args, reify via `Quote.reify({:vneutral, neutral}, depth)` instead; same semantics).

### §2.1 Why reify+infer, not a head-codomain spine walk

The tempting lighter design — walk the spine to the head `{:nvar, level}`, look up its Pi in `ctx`, apply closures down the args, sort the final codomain — **does not validate the arguments**. Because the motive term is never term-checked (§0), unchecked arguments would flow into the case's result type (`apply_motive`, kernel.ex:223) and outward. Term-level `infer/2` is the kernel's already-trusted validator and does head resolution + argument checking in one move; reusing it makes the clause sound by construction rather than by a new argument. This mirrors Lean's `inferType` on `App` and Agda's sort inference on applied neutrals: head's Pi, arguments checked, instantiated codomain.

### §2.2 The known-lossy reify corner is conservative-only

`Quote.reify` collapses `{:vdata, name, args}` to `{:data, name, args, []}` (no param/index split — the documented warning at `kernel.ex:632-642`, which is exactly why the Π/Σ clauses recurse on values). For THIS clause the reified thing is the neutral application itself; the corner fires only when a spine **argument** is itself an indexed-family *type value* (e.g. `F(Vec(a, n))` with `F : Type -> Type`), where re-inference of the collapsed `{:data,…}` can fail `:arg_arity` → a **false rejection**, never a false acceptance. That is the same failure direction as today (today ALL napps reject), strictly smaller. Documented as a future lift, not fixed here — the motivating class (`b(first(p))`, `b(x)`, `F(n)` over non-type args) reifies losslessly.

### §2.3 What the clause newly accepts, precisely

Neutral applications whose reified term `infer`s to `{:vtype, l}`: variable heads bound at Pi-into-Type (the Sigma motive), global heads whose declared/inferred type is Pi-into-Type (type-level function defs — accepted automatically by the same judgement; no special casing), projection heads if `reify_neutral` supports them and `infer` types them. Everything else keeps rejecting with the same tags. No other kernel judgement changes; conversion, normalisation, coverage, and branch checking are untouched.

## §3 TCB gate (mandatory, blanket-approval conditions)

This is a kernel change. The blanket approval applies (Agda/Lean-aligned per §2.1), which waives the per-diff operator review but NOT the gate:

1. Strict red-green (the probe below fails `:bad_motive` today).
2. **New Antigen antibody** (`lib/antigen/` + `test/antigen/`): (i) an accepting seed — a motive applying a type-family variable must pass `check_motive_wf` (the D1 shape); (ii) a rejecting seed — a motive applying a non-type-valued head (`g : (a) -> Nat`) must still reject `:bad_motive`; (iii) the standard no-defeq-collapse/termination obligations for a TCB change: run the full Antigen suite — the existing conv/nf idempotence and substitution-law families exercise the new value shape via the enlarged accept set.
3. Full Antigen suite + full test suite, zero failures.
4. **Differential oracle probe**: a new `sg` cluster pair — `sg01_dependent_second.cure` (the MySigma family with `first`/`second`) and the faithful `.idr` transliteration (Idris: a custom `MySigma` record/data with dependent `second : (p : MySigma a b) -> b (first p)`; `%default total`, no module line) — expected relation `same` (both accept). The executor runs `mix cure.oracle sg` ONCE (alone; it regenerates only that cluster's verdicts.json — the standing destructive-command caution is about accidental regeneration of OTHER clusters; adding a new cluster is its intended use), then the replay test must be green. Any divergence (Cure accepts / Idris rejects or vice versa) is a STOP-and-report, per the oracle contract.

## §4 Tests

- **Unit (`test/cure/elab/dependent_eliminator_test.exs`, new):**
  - The MySigma probe program (family with function-typed param `b`, `mk_pair` GADT ctor, `first` by match, `second : (p: MySigma(a, b)) -> b(first(p))` by match) elaborates `{:ok, _}` — red today with `:bad_motive`.
  - `second(mk_pair(x, y))` reduces/runs correctly (BEAM execution of a monomorphic instance; also pins the `first(mk_pair(x,y)) → x` ι-reduction inside branch checking, which requires `first` to be δ-certified — structurally recursive, auto-certified).
  - Negative: the same shape with `b : (a) -> Nat` (non-type codomain) still rejects (`:bad_motive` — the `{:error, :not_a_type_value}` path preserved).
  - Negative: an ill-typed argument in the motive position (e.g. `b(w)` where `w`'s type doesn't match `b`'s domain) still rejects — the argument-checking half of §2.1 is observable.
- **Antigen antibody** per §3.2.
- **Oracle pair** per §3.4.
- Existing pins: full suite green; no existing test asserts `:bad_motive` for a *well-typed* neutral-app motive (they couldn't — the feature never worked), so no pin flips.

## §5 Non-goals

- D2 (primitive-Sigma retirement to `@builtin(:sigma)`) — separate chained spec; NOTE for its author: the prior scout's D2 inventory (site anchors, `:eq`-status claims) came from the stale parent checkout and must be re-swept in-worktree.
- The §2.2 lossy corner (type-constructor applied to an indexed-family type as a spine argument) — future lift with its own reify-fidelity work.
- Any change to `conv.ex`, `normalise.ex`, `eval.ex`, coverage, or branch checking.
- Surface syntax work (the MySigma probe uses existing surface forms only).

## §6 Acceptance criteria

1. The `second` probe elaborates and runs; red→green documented.
2. Both §4 negatives still reject with today's tags.
3. Antigen: new antibody green; FULL Antigen suite green.
4. Oracle: `sg` cluster `same`/`same`; replay green.
5. Full `mix test` green; `git diff` shows exactly one new clause in `kernel.ex` (plus tests/Antigen/oracle fixtures) — no other `lib/cure/core/` change.
