# Antigen value-level post-shrink — design

**Status:** scheduled (Tier-1 of the shrinking work). This is the cheaper minimizer
the `ChoiceSeq` reference spec (`2026-07-02-antigen-choiceseq-backend-design.md` §9)
gates itself behind: build `ChoiceSeq` **only if** this proves insufficient on real
deep counterexamples. Expectation stands that `ChoiceSeq` stays shelved for terms.

**Parity ledger:** Tier-B report §"Reach left open" → the value-level post-shrink
bundled-with-shrinking item. Closes the "banked antibody is a depth-12 monster"
problem for the antibodies we can actually produce.

**One-liner:** when an assay fires, greedily rewrite the reified `Challenge`
artifact into a *minimal* witness before banking it — so antibodies are minimal by
construction. The rewriter is **purely structural (untyped)**; the caller's
predicate ("same assay still violates") is the sole validity gate.

---

## 1. Problem

`Antigen.Runner.explore/1` banks the **raw** artifact on an infection
(`runner.ex:31`: `Corpus.append(corpus_path, c, dedup_key(c, :antibody))`) with zero
minimization. The generator is now lazy (`@max_size` 3→12), so a real infection
would bank a deep, mostly-irrelevant term. A banked antibody should be the *smallest*
term that still trips the bug — easier to read, to regression-test, and to dedupe.

**Reality check (why this is Tier-1, not `ChoiceSeq`).** The generator finds **0
organic infections** today (A and B both closed at `survivors=0`; banked mutation/
conversion seeds are hand-built minimal). So shrinking has no organic input yet.
This is infrastructure: it makes future organic counterexamples minimal, and it is
validated now against *manufactured* violations (§6). It is the cheap tier; the
expensive internal shrinker (`ChoiceSeq`) stays gated behind it.

---

## 2. Core insight — the predicate is the only validity gate

The rewriter performs **purely structural, untyped edits** on the artifact. A
candidate edit is accepted iff a caller-supplied predicate `pred.(candidate)` still
holds, where `pred` = "the same assay still returns `{:violation, _}`".

- For a `:typed_term` artifact the assay runs `Kernel.infer`/`check`, so any edit
  that breaks well-typedness makes the assay stop firing → the candidate is
  rejected. Well-typedness is preserved *for free*.
- For a `:mutant_term` artifact the predicate is "the (possibly buggy) `infer`
  still wrongly accepts this ill-typed term" — so edits that destroy the triggering
  structure are rejected.

Thus the rewriter needs **no type inference, no bidirectional walk, no per-rule
re-typecheck**. This is the `ChoiceSeq` spec's "validity is free" property, obtained
here through the predicate rather than through interleaved generation. The rewriter
is a dumb structural search; all semantics live in `pred`.

The only structural obligations (so `pred` doesn't crash on garbage): a candidate
must be a well-formed, **de-Bruijn-closed** Core term w.r.t. its context. The Runner
already has `well_formed?/1` for exactly this; the shrinker reuses it as a pre-gate,
and additionally rescues any exception from `pred` (→ reject candidate).

---

## 3. Module & interface

New module `Antigen.Shrink` at `lib/antigen/shrink.ex`. It is **not** under
`generators/` or `assays/`, so it may call the kernel freely and is unaffected by
the StreamData quarantine (it uses neither StreamData nor `ChoiceSeq`).

```elixir
@type pred :: (Challenge.t() -> boolean())
@spec minimize(Challenge.t(), pred(), non_neg_integer()) :: Challenge.t()
def minimize(challenge, pred, budget)
```

- Returns a `Challenge` with the **same** `kind`/`assay`/`label`/`fault`/`sig`, a
  minimized `payload` (`ctx`/`type`/`term`), and `seed` recomputed.
- `budget` is a **step budget** (max candidate evaluations, i.e. `pred` calls). No
  wall-clock — the shrink must be deterministic and reproducible. On exhaustion,
  return the best (smallest accepted) artifact so far.
- **Precondition:** `pred.(challenge)` is already true (the Runner only calls
  `minimize` on a confirmed infection). `minimize` never returns an artifact for
  which `pred` is false; if no edit is accepted it returns the input unchanged.

---

## 4. Rewrite rules

Each rule is a **candidate generator**: `(artifact) -> [artifact]`, producing
strictly-smaller structural variants. All edits are untyped; `pred` filters. Rules,
cheapest/highest-impact first:

1. **subterm → minimal-atom.** For each subterm position, replace the subtree with a
   minimal closed inhabitant from the fixed menu set
   `[{:ctor,:Z,[]}, {:ctor,:vnil,[]}, {:ctor,:T,[]}, {:type,0}]`. Collapses deep
   filler to a leaf. (No type inference — `pred` rejects the type-wrong ones.) Skip
   positions already equal to the replacement.
2. **numeral shrink.** For each `Sᵏ Z` (k≥1), try `Sᵏ⁻¹ Z` … toward `Z`. Lowers Vec
   indices, `conv_depth`, and any Nat magnitude.
3. **context drop.** For each `ctx` entry `i` with no `{:var, i}` occurrence in
   `term`/`type`, delete it and **shift** every `{:var, j>i}` down by one (and any
   index in remaining ctx entry types). The one rule that manipulates de Bruijn
   indices; it must keep the term closed (a reference to `i` would forbid the drop).
4. **structural unwrap.** Replace a compound (`{:app,_,_}`, `{:ctor,_,args}`,
   `{:case,scrut,_,_}`, `{:lam,_,body}`, `{:fst,p}`/`{:snd,p}`, `{:pair,a,b}`) with
   one of its immediate sub-terms. The generic, provenance-free form of "peel a
   wrapper" — it undoes A's `deepen` layers and B's carriers without knowing they
   exist.

**Search discipline.** Deterministic enumeration: positions left-to-right (pre-order),
rules in the order above. Greedy: apply the **first** accepted candidate, then restart
the sweep from the top. **Fixpoint** when a full sweep accepts nothing, or the step
budget is hit. Each accepted step strictly decreases `size` (§5), so termination is
guaranteed independent of the budget; the budget only caps *cost*.

**Acceptance gate for a candidate `k`:** `Runner.well_formed?(k)` AND (rescue
`pred.(k)` → `false` on exception) AND `pred.(k)`. First candidate passing is taken.

---

## 5. Size measure & guarantees

`size(artifact) = term_node_count(term) + length(ctx) + sum_of_numeral_magnitudes(term)`.

- **Monotone:** every accepted edit strictly decreases `size` (rules 1–4 each remove
  nodes, lower a numeral, or drop a ctx entry). Asserted in tests.
- **Idempotent fixpoint:** re-`minimize`-ing an already-minimal artifact (same
  `pred`) is a no-op. Asserted.
- **Deterministic:** same `(artifact, pred, budget)` ⇒ same output (fixed
  enumeration; no clock, no RNG). Asserted — this is what makes minimized antibodies
  reproducible.

---

## 6. Runner integration

At the infection branch (`runner.ex:28`), before writing the report/banking, build
the predicate from the **same dispatch the Runner already uses** and minimize:

```elixir
{:violation, _} = v ->
  assay = opts[:assay] || assay_module(c.assay)
  pred = fn ch -> match?({:violation, _}, apply(assay, :run, [ch])) end
  c_min = Antigen.Shrink.minimize(c, pred, shrink_budget(opts))
  {:ok, path} = Report.write_infection(opts[:report_dir], c_min, v, summarize(acc, count))
  IO.puts(Report.breadcrumb(c_min, path))
  Corpus.append(opts[:corpus_path], c_min, Corpus.dedup_key(c_min, :antibody))
  %{acc | infections: acc.infections + 1}
```

- Reusing `opts[:assay] || assay_module(c.assay)` means the predicate carries any
  **injected assay/infer override** verbatim — which is exactly the seam the
  end-to-end test (§7.5) uses to manufacture a buggy `infer`.
- `shrink_budget(opts)` reads `opts[:shrink_budget]`, default `@shrink_budget` (e.g.
  `2000` steps). Budget exhaustion banks best-so-far (still a valid antibody) — never
  a non-violating artifact (§3 precondition holds throughout).
- The report and the banked antibody both use `c_min`.
- **Cost in normal runs is ~zero** — the branch only runs on an infection, of which
  there are currently none.

---

## 7. Testing (TDD; artifact is executable code)

1. **Determinism** — same `(artifact, pred, budget)` ⇒ identical minimized output.
2. **Monotone + idempotent** — `size(minimize(a)) ≤ size(a)`; `minimize(minimize(a)) ==
   minimize(a)`.
3. **De-Bruijn closure (per-rule property)** — over sampled terms, every candidate a
   rule proposes is de-Bruijn-closed w.r.t. its ctx (esp. rule 3's shift); no rule
   ever introduces an out-of-scope `{:var,_}`.
4. **Synthetic-predicate machinery** — take a deep well-typed term (from
   `Term.gen_term`) and shrink under `pred = fn ch -> infer_ok?(ch) and contains?(ch,
   :vcons) end`; assert the result is minimal (a single `vcons` at minimal-atom args,
   empty/relevant ctx) and still satisfies `pred`. Tests the rewriter + de Bruijn
   handling without any real assay.
5. **Buggy-infer end-to-end** — inject (via `opts[:assay]`) an assay wrapper that
   runs `Assays.Mutation.run(c, buggy_infer)` where `buggy_infer` wrongly ACCEPTS the
   `:head_swap` family. Grow a deep `:mutant_term` carrying a `head_swap` fault (wrap
   with `Mutation.deepen` + a padded ctx). Run the Runner infection→shrink→bank path;
   assert the banked antibody's **term/ctx** are structurally bare (no `deepen`
   wrappers, no dead ctx entries) and that it still trips the buggy assay. Assert on
   `payload.term`/`payload.ctx` only — NOT on `fault.depth`/`wrap_path`, which are
   kept verbatim as injection provenance (§9) and may not match the minimized term.
6. **Budget bound** — with `budget: 1`, `minimize` performs at most one accepted edit
   and returns a valid (still-violating) artifact; the run terminates.
7. **Backward compatibility** — full suite green; with 0 organic infections the
   Runner change is inert on every existing corpus; banked seeds unchanged.

---

## 8. Architecture & constraints

- `lib/antigen/shrink.ex` (`minimize/3`, the 4 rule generators, `size/1`,
  de-Bruijn `shift`). Reuses `Runner.well_formed?/1` (expose if private) and
  `Cure.Core` term structure; no new kernel code.
- `lib/antigen/runner.ex` — the infection-branch change + `@shrink_budget` +
  `shrink_budget/1`.
- `test/antigen/shrink_test.exs`.
- **Determinism/reproducibility non-negotiable:** no clock, no RNG in `minimize`
  (mirrors the banked-seed replay contract). Step-budget only.
- **Ghost-authored commits; one full build/test run at a time; StreamData
  quarantine** (Shrink is outside `generators/`/`assays/` and uses neither backend).
- No changes to `Gen`, the assays, the challenge model, or the corpus format.

---

## 9. Non-goals (YAGNI)

- **`ChoiceSeq` / internal buffer shrinking** — deferred; this spec is the Tier-1
  gate. Reassess `ChoiceSeq` only if a real deep antibody stays visibly non-minimal
  after this.
- **Provenance-guided peeling** — the generic rule 4 subsumes undoing `deepen`/conv
  carriers without fault metadata; no separate provenance path.
- **Shrinking the `fault` provenance map** — kept verbatim; it documents the original
  injection, not the minimized term. Consequence: a shrunk mutant's `fault.depth`/
  `wrap_path`/conv indices may no longer match its (smaller) term. Accepted: `fault`
  is human-facing provenance, and banked *antibodies* (`corpus_path`) are never scored
  by the depth/wrapper metrics — those read `fault.depth` only over the banked *seed*
  corpus (`seeds.sexp`), which this path never writes. If a future need arises,
  recompute the structural fault fields post-shrink; out of scope for v1.
- **Multi-objective / global-optimum minimization** — greedy local fixpoint is
  sufficient for the antibody-readability goal.
- **Shrinking type-check performance** — infections are rare; a step budget bounds
  worst case. No caching of kernel calls in v1.
