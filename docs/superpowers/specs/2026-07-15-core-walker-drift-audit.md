# Core Walker Drift — Defect Audit

**Status:** LIVE. Findings are being added as audit agents complete.
**Date:** 2026-07-15
**Scope:** `lib/cure/elab/*` (E) and `lib/cure/core/*` (K). The non-dependent
`lib/cure/compiler/{codegen,pattern_compiler}.ex` and `lib/cure/types/*` are out of scope
and any finding located there is void.

**Provenance.** Eight parallel audit agents, one lens each, each candidate finding then
attacked by two independent skeptics instructed to refute it. Every defect recorded below
under §4 has additionally been **re-verified by hand against the source** — the agents
supplied leads, not facts. Claims still resting only on an agent's word are marked
`UNVERIFIED` and quarantined in §7.

---

## 1. Thesis

This audit was commissioned after two latent elaborator defects shipped
(`12cb6163`, `a8b4e7e9`), on the suspicion that they were instances of a class rather
than accidents. They were.

**The class:** Cure's Core has 24 term formers. Ten of them are *compound* (they carry
subterms). Roughly 25 hand-written walkers traverse Core terms across E and K. Almost none
of them enumerate all ten. That would be merely untidy — except that most of these walkers,
on meeting a former they do not know, **return it unchanged and report success**. They treat
an unknown compound former as a **leaf**. They do not crash. They quietly do nothing, and
their caller cannot tell the difference between "walked it, nothing to do" and "never looked
inside."

This is not twelve independent mistakes. It is **one missing invariant, instantiated twelve
times**, and it is *generated* by the way the language grew: every former added to
`Core.Term` after a walker was written silently invalidates that walker, and nothing in the
build catches it. `:let` (the 7th former), the QTT grades on binders, and the `Effect` family
all landed recently. Every walker predating them is incomplete **by construction**.

The evidence that this is systemic rather than incidental is in the codebase's own comments.
At `lib/cure/elab/program.ex:831-834` someone hit this exact bug, fixed it, and left a note:

> The `:let` binder is the seventh Core former. Without this clause it fell through to the
> catch-all below, and every global referenced only inside a `let` vanished from
> `reachable_def_names/2` — co-emitting such a closure produced a module that called a
> function it never defined.

That is a precise diagnosis of the bug class. It was applied to **one former in one walker**,
and no sweep followed. The `Effect` family reintroduces the identical bug in the identical
function today (§4.6).

---

## 1b. Bottom line

Twenty-five Core walkers screened. Twelve fail open. **Six are live, six are inert** — and the
thing that separates them is not fail-open-ness at all, it is whether the walker traverses
**values** or only **types** (§3a). Triage on that axis first.

| # | defect | severity | live? |
|---|---|---|---|
| §4.0 | `Subst` skips `effect_pure`/`effect_bind` → erasure fails to strengthen outer vars → **wrong BEAM code, never re-checked** | **CRITICAL** | ✅ live, hand-verified |
| §4.1 | `has_meta?` blind to `:case`/`:let`/`Effect` → unsolved metavariable can reach the kernel | **CRITICAL** | ✅ live (trigger needs a probe) |
| §4.2 | `Subst` **discards every QTT grade**, resetting erased binders to ω | **HIGH** | ✅ live |
| §4.4 | TCB: `subst_params` / `replace_branch_vars` fail open on `:let`/`Effect` | **HIGH** ¹ | ✅ live |
| §4.7 | `count_level` returns 0 for `Effect` → `{0,ω}` gate **permits** an unsafe optimisation | **HIGH** | ✅ live |
| §4.6 | `global_refs` misses `Effect` → emitted module calls a function it never defines | **MEDIUM** | ✅ live |
| §4.5 | `mabs` skips `:let`/`Effect` | — | ⬜ inert (types only) |
| §4.8 | `has_hole?` skips `Effect` | — | ⬜ inert (holes unreachable in effects) |
| §4.9 | dead retry on the dotted-qualified path | LOW | ✅ live, waste only |
| §8 | `totality_closure` certifying a non-total function; `Validator` missing effects; `Relevance.walk` on `Effect(T)` | — | ❌ **refuted** |

¹ severity pending a probe — it is in the TCB and the direction of failure is argued, not proven.

The two CRITICALs are independent and neither is the bug we shipped last week. Both are
**silent**: one emits wrong code, one hands the kernel a term with a hole in it.

---

## 2. The invariant that is missing

> **Every traversal of a Core term must be total over `Core.Term.t()`, and where it cannot
> be, its catch-all must fail CLOSED.**

The codebase already knows this. `lib/cure/elab/unify.ex:389-401` states it exactly, and is
the *only* walker that gets it right on purpose:

> This walker is FAIL-CLOSED: its catch-all answers `true` (escapes). […] Refusing to solve a
> metavariable is soundly incomplete; solving it out of scope is not.
>
> Note a generic structural tuple-walk would NOT be a correct catch-all here, the way it is
> for `Inductive.occurs?`: binder-introducing nodes must bump `local`, and walking a branch
> body without bumping it *under*-estimates the free index […] So every binder is enumerated
> explicitly, every leaf is enumerated explicitly, and anything unknown is assumed to escape.

The audit's job was to find every walker that does **neither** of the two safe things.

---

## 3. Taxonomy of catch-alls

The coverage matrix (§5) cannot by itself distinguish a bug from a correct omission. What
separates them is the **polarity of the catch-all**. Three classes:

### Class A — generic structural descent (SAFE, self-healing)
Catch-all is `when is_tuple(t) -> descend into every element`. A new former is handled
automatically the day it is added. Correct **iff** the operation does not need to track
binder depth (`Effect` nodes bind nothing, so they are safe under this catch-all).

- `core/validator.ex:163` `children`
- `core/term.ex:240` `has_free_var?`
- `elab/totality_closure.ex:105` `collect`
- `elab/elaborator.ex:2183` `abstract_term`, `:2212` `free_indices`, `:987` `occurs_below?`

**These are not defects.** In particular the nightmare hypothesis — *a recursive call hidden
inside an `Effect` node that `totality_closure` never sees, certifying a non-total function
as total* — **is refuted**: `collect/1` descends generically through any tuple, so it sees
into `effect_bind`. Recording this explicitly because it was the single highest-severity
thing the audit was looking for, and it is not there.

### Class B — fail-closed (SAFE, soundly incomplete)
Catch-all answers with the conservative verdict; an unknown former degrades to *rejection*,
never to silent acceptance.

- `elab/unify.ex:435` `escapes?` → `true` ("assume it escapes; refuse to solve")
- `core/meta_check.ex:63` `canonical_head?` → `false`
- `core/kernel.ex:1470` `rigid_index?` → `false`

**Not defects.** They may cost completeness on `let`/`Effect`-bearing terms; that is a
tolerable, and *loud*, failure mode.

### Class C — fail-open leaf assumption (THE DEFECT CLASS)
Catch-all returns the node **unchanged**, or a zero-value (`false` / `0` / `[]`), thereby
asserting "this former has no interesting content." For a compound former that assertion is
**false**, and the caller has no way to detect it.

Every finding in §4 is Class C.

---

## 3a. The discriminator: does this walker see TYPES, or VALUES?

**This is the most useful thing the audit produced, and it did not come from a finder — it
came from two skeptics refuting findings.** It cuts the twelve Class C walkers cleanly into
"inert" and "live", and it is the reason a raw fail-open count is a bad triage signal.

`:let`, `effect_pure`, and `effect_bind` **cannot appear in a type**. Two independent
choke-points enforce this, and the skeptics traced both exhaustively:

1. **Every declared type** funnels through exactly one grammar, `idx_to_core`
   (`declarations.ex:1658-1805`) — reached from all 9 type-elaboration entry points. Its
   clause list is closed (`:variable`, `:function_call`, `:sigma_type`, `:tuple_type`,
   `:pi_type`, `:attribute_access`, `:union_type`) with an explicit
   `{:error, {:unsupported_index_expr, other}}` catch-all. `let`/do-block surface syntax is
   **rejected outright**.
2. **Every inferred type** arrives via `Quote.reify` of a `Cure.Core.Value.t()`
   (`value.ex:56-74`), which has **no `:vlet` form at all** — `let` evaluates away by
   substitution during NbE, so there is nothing to reify back into a `{:let, …}`.

**Therefore:**

- A walker that only ever traverses **type-level** terms **cannot** meet these formers. Its
  fail-open gap is **inert today** — real hygiene debt, zero live blast radius. This covers
  `mabs` and everything else downstream of `Unify.unify`, whose 12 call sites in
  `elaborator.ex` were enumerated one by one and shown to unify **types only** (an argument's
  inferred type via `Quote.reify`, a codomain, a domain instantiation) — **never an argument's
  value.**
- A walker that traverses **value-level** terms — definition bodies, chosen arguments, branch
  bodies — **does** meet them, because that is exactly where `do`-blocks and `let`-chains live.
  Its fail-open gap is **live**.

Triage every walker by which side of that line it sits on **before** assigning severity. A
gap that cannot be reached is not a bug; saying otherwise is how an audit loses the reader's
trust. It is also the reason the `derive_actor` shadowing bug went unnoticed for so long: `let`
appears only in *values*, and the value-side walkers are the under-maintained ones.

---

## 3b. Severity is decided by position relative to the kernel check

The audit surfaced an ordering principle that was not obvious going in, and it governs every
severity below. **A fail-open walker's blast radius depends on whether anything re-checks its
output.**

- **Walkers that run *before* or *during* kernel checking** (`unify`, `has_meta?`, the
  kernel's own `subst_params`) produce a term that the kernel then judges. A corruption here
  is *usually* caught — as a conversion failure or a validator rejection. The damage is
  **completeness** (a good program mysteriously rejected) and the failure is at least *loud*.

- **Walkers that run *after* kernel checking — `Erase`, `emit` — have nothing downstream to
  catch them.** `emit.ex:354` feeds `Erase.erase/2`'s output straight into codegen. Erasure
  output is **never re-verified by the trusted kernel**. A de Bruijn index corrupted at this
  stage does not get rejected; it either crashes emit on an unbound index, or — worse —
  **silently resolves to the wrong bound variable and generates wrong code.**

`relevance.ex:4-7` states the invariant that governs this half of the pipeline:

> `Erase.erase` produces [a term that] never references a binding that no longer exists.

The top finding below is a direct violation of that stated invariant. **Post-kernel walkers
are where silent miscompilation lives, and they should be fixed first.**

---

## 4. Confirmed defects

All hand-verified. Ordered by severity.

### 4.0 `Subst` skips `effect_pure`/`effect_bind` → **silent miscompilation** · **CRITICAL**
`lib/cure/elab/subst.ex:75` and `:115`

*(This subsumes what was filed as §4.3 in the first draft; the adversarial pass established
reachability and it escalated past everything else.)*

`replace/4` and `shift/3` have an explicit clause for `{:effect_type, inner}` (`:64`, `:104`)
but **none for `{:effect_pure, t}` or `{:effect_bind, e, k}`**. Both fall to the catch-all
(`do: other`) and are returned **byte-identical, with zero recursion into their subterms**.

**What it silently does.** `instantiate/2` is documented to replace a telescope's binders and
*strengthen every free variable past the telescope*. Any `{:var, i}` nested inside an
`effect_pure`/`effect_bind` is neither substituted nor strengthened. When the surrounding
binders are peeled away, that variable is left **pointing at the wrong binder, or at one that
no longer exists.** No error is raised.

**Reachability — HAND-VERIFIED. Read this carefully, because one skeptic refuted a
*different* route to the same function and the distinction matters.**

*The refuted route (do not chase it):* a do-block becoming a **metavariable's solution**, later
corrupted by `force_d`'s `Subst.shift`. **Dead.** Per §3a, `Unify.unify`'s operands are
type-level terms exclusively — an argument's *value* is appended to `chosen` and never unified.
Effect values never reach `force_d`.

*The live route (this is the bug), verified by reading `erase.ex:146-154` directly:*

```elixir
def erase(env, {:case, s, m, [{cname, arity, body}] = branches}) do
  if collapsible_ctor?(env, cname, arity) do
    body
    |> Cure.Elab.Subst.instantiate(List.duplicate({:ctor, :cure_erased, []}, arity))
    |> then(&erase(env, &1))
```

`body` is a **branch body — a value-level term.** It can absolutely contain effect nodes; we
know this for certain because `erase/2`'s *own* clauses eight lines below explicitly handle
`{:effect_pure, _}` / `{:effect_bind, _, _}`, with a comment insisting they must never be
dropped.

**The corruption is in the *strengthening*, not the placeholder substitution.** This is the
part the finder got fuzzy and it is worth stating precisely. `instantiate/2` does two jobs:

1. replace `{:var, i}` for `i < arity` (the branch's erased pattern binders) with the
   placeholder — *harmless, those binders are surface-inaccessible*; and
2. **strengthen every outer reference**: `{:var, i}` for `i >= arity` becomes `{:var, i - arity}`,
   because collapsing the case **deletes those `arity` binders from the context.**

Job (2) is the one that matters, and it is precisely what gets skipped. An outer variable
sitting inside an `effect_bind`/`effect_pure` is returned **unchanged** by the catch-all, so it
still counts past `arity` binders **that no longer exist**. It does not dangle — it **silently
resolves to the wrong enclosing binder.**

**Consequences, in order:**

1. Erasure runs **strictly after** kernel typechecking and **its output is never re-verified**
   (§3b); `emit.ex:354` hands it straight to `peel_params`/`lower`.
2. So the wrong-variable reference is **never caught**. It emits wrong BEAM code, or crashes
   emit on an out-of-range index. There is no third outcome.
3. `relevance.ex:4-7` states the invariant this breaks in as many words: *"`Erase.erase`
   produces [a term that] never references a binding that no longer exists."*

**Trigger.** A collapsible family is single-constructor with all fields erased and `arity ≥ 1`
— the code's own comment names `Equivalent`'s `reflexive`, i.e. **the identity type**, and the
identity-type-as-inductive work is active. So: *an effect-returning function that pattern-matches
an equality proof and then references one of its own parameters inside a `do` block.*

```cure
fn f(x: Int, p: Equivalent(x, y)) -> Effect(Unit) =
  match p
    reflexive -> do
      print(x)      # <-- {:var, N} inside an effect_bind; never strengthened
      pure(unit)
```

That is not an exotic shape. It is dependent types plus BEAM effects — the two things the
language exists to combine.

**Why this is provably an oversight and not a design decision.** Three *other* walkers get
this right, including one in the TCB:

- the **kernel's own** `Term.shift`/`Term.subst` (`core/term.ex:204-206`, `:293-295`) — handle both;
- `declarations.ex:2007-2011` `beta_substitute` — handles both;
- `erase.ex:160-166` `erase/2` itself — handles both, with a comment that reads like a warning
  written by someone who had just been bitten: *"Effect nodes are NEVER dropped… Without these
  they hit the identity catch-all."*

The author of `erase/2` was alert to exactly this hazard — and the `Subst.instantiate` call
**eight lines above it, on the same body**, was not given the same treatment.

**Fix.** Two clauses per function. `effect_type`/`effect_pure` are congruence; `effect_bind`
recurses into both subterms **at the same depth** — the node itself binds nothing (the binder
lives in the `lam` it contains), exactly like `:app`.

---

### 4.1 `has_meta?` — an unsolved metavariable can reach the kernel  · **CRITICAL**
`lib/cure/elab/elaborator.ex:7344-7350`

```elixir
defp has_meta?({:meta, _}), do: true
defp has_meta?({:data, _n, ps, is}), do: Enum.any?(ps ++ is, &has_meta?/1)
defp has_meta?({:ctor, _n, args}), do: Enum.any?(args, &has_meta?/1)
defp has_meta?({:app, f, x}), do: has_meta?(f) or has_meta?(x)
defp has_meta?({:pi, _g, d, c}), do: has_meta?(d) or has_meta?(c)
defp has_meta?({:lam, _g, d, b}), do: has_meta?(d) or has_meta?(b)
defp has_meta?(_), do: false          # <-- :case, :let, :effect_* ALL land here
```

Handles 5 of 10 compound formers. **Missing `:case`, `:let`, `:effect_type`,
`:effect_pure`, `:effect_bind`.**

**What it silently does.** This function *is* the gate enforcing the invariant that
`Cure.Elab.Subst`'s own moduledoc declares: *"metavariables never reach the kernel."* At
`:7332` its verdict decides between `{:error, {:unsolved_metavariables, name}}` and handing
the term to `Kernel.check/3`. A residual `{:meta, id}` nested inside a `case` branch, a `let`
body, or an effect node makes `has_meta?` answer **`false`** — indistinguishable from "fully
solved" — and the elaborator then submits a term **with a hole in it** to the trusted kernel.

`{:meta, _}` is not a `Core.Term.t()`. The kernel is being asked to judge a term outside its
own grammar. Whether that surfaces as a crash, a `Validator` rejection, or something worse
depends on which kernel path receives it, and **that is exactly the question that must not be
left to chance.** Severity is CRITICAL on the strength of the broken invariant alone.

**Trigger (to be confirmed by probe):** any call whose implicit argument is only ever
determined inside a `case`/`let`/`do`-block subterm — i.e. precisely the shapes the recent
`:let` and `Effect` work introduced.

**Fix:** enumerate all ten compound formers, or replace with a generic tuple-descent
catch-all (Class A is correct here — `has_meta?` tracks no depth).

---

### 4.2 `Cure.Elab.Subst` destroys every QTT grade it touches  · **HIGH**
`lib/cure/elab/subst.ex:47-56` (`replace`) and `:87-96` (`shift`)

```elixir
defp replace({:pi, _g, d, c}, env, k, depth),
  do: {:pi, Cure.Core.Grade.unrestricted(), replace(d, ...), replace(c, ...)}
#           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ incoming grade DISCARDED
```

Every binder clause in both functions — `:pi`, `:lam`, `:let`, in `replace` **and** in
`shift` — pattern-matches the grade as `_g` and then **hardcodes
`Grade.unrestricted()`** in the reconstruction.

**What it silently does.** It rewrites erasure information. A grade-`0` (erased) binder that
passes through *any* elaborator substitution or shift comes out grade-`ω` (runtime-relevant).
Nothing reports this; the term looks well-formed.

**Why this is not cosmetic.** Two facts make it live:

1. The **kernel's own** `Term.shift`/`Term.subst` (`core/term.ex:187-191`, `:271-278`)
   correctly thread `g` through. So the elaborator's meta-aware copy is not merely a
   specialisation of the kernel's — it *disagrees with it* on the semantics of a binder.
2. **`Conv` compares grades by equality**, deliberately (`core/conv.ex:77-79`: *"Grades are
   compared by EQUALITY, never by `Grade.leq/2`"*).

So a λ whose grade was reset to ω, checked against a Π that legitimately says `0`, is
**rejected by the kernel** on a grade mismatch — surfacing as an inscrutable conversion
failure far from the cause. `Subst.shift` is called on *solved metavariable solutions* every
time one is read back across a binder (`unify.ex:146-153`), so these grade-mangled terms are
embedded in the final Core the kernel judges.

The reverse direction is the one to worry about and is **not yet ruled out**: if an ω-ified
*type* reaches the `{0,ω}` relevance check, that check would see a relevant binder where the
real signature says erased, and would **not** enforce the erasure discipline — accepting a
program that scrutinises an erased value. Whether `relevance.ex` reads a `Subst`-processed
type is **OPEN** (§7.1). If it does, this is CRITICAL, not HIGH.

**Fix:** thread `g`. One-character-per-clause change, six clauses. It is difficult to see
this as anything but a copy-paste from a pre-QTT version of the file.

---

### 4.3 — *(promoted to §4.0 after adversarial verification established reachability)*

---

### 4.4 TCB · `subst_params` and `replace_branch_vars` fail open inside the kernel  · **HIGH** (severity pending probe)
`lib/cure/core/kernel.ex:1244` and `:1561`

```elixir
defp subst_params(other, _pmap, _depth), do: other          # :1244
defp replace_branch_vars(other, _subst), do: other          # :1561
```

Both are **in the trusted kernel**. Both enumerate `:pi :lam :app :data :ctor :case` and
**omit `:let` and the entire `Effect` family**, then fail open.

These two implement dependent pattern matching's index refinement: `replace_branch_vars`
applies the substitution derived from GADT index unification to a branch body
(`:1523`, `:1535`, `:1572`), and `subst_params` substitutes data-type parameters (`:1201`).

**What it silently does.** A branch body containing a `let` or an effect node has the
refinement substitution applied to *everything except* the interior of that node. The
interior keeps its pre-refinement variables. Because the branch binders still exist (arity is
unchanged), those variables still *resolve* — to the **un-refined** value. The kernel then
checks the body against a motive in which the index **has** been refined.

**Direction of failure — argued, not yet proven.** Refinement makes types *more* specific, so
skipping it should leave the body *more general* and cause a **conversion failure**
(completeness bug: a good program rejected, mysteriously). I can construct no case where
skipping a refinement makes an ill-typed program check. **But this is the TCB, and "I could
not construct one" is not a proof.** A discriminating probe is mandatory before this severity
is settled (§7.2). Under the standing rule, any TCB change here needs an Antigen antibody, the
full Antigen suite, and the full gate.

---

### 4.5 `mabs/5` — Miller-pattern abstraction skips `:let` and `Effect`  · **LATENT, not live**
`lib/cure/elab/unify.ex:269` · catch-all `do: leaf`

The gap is real: `mabs` abstracts pattern variables out of a term when solving `?F(x̄) := t`,
and a `{:var, k}` inside a `:let` or effect node would be neither abstracted nor shifted,
producing a misnumbered solution.

**But it cannot be reached today, and the skeptic proved it via §3a**: all 12 `Unify.unify`
call sites unify **type-level terms only**, and `:let`/`effect_pure`/`effect_bind` are
structurally excluded from types (closed `idx_to_core` grammar; no `:vlet` in `Value.t()`).
Nothing can hand `mabs` one of these formers.

Worth fixing anyway — as **insurance**, not as a bug. The moment `idx_to_core` is extended to
accept `let`/do-block syntax at the type level (a plausible extension), this becomes live and
silent. The tell is that its sibling **twelve lines away**, `escapes?`, was *already patched to
fail closed against this exact hazard* (`unify.ex:385-401, :435`) and carries a comment
explaining why. Same file, same author, same week — one walker learned the lesson and the one
next to it did not. Flip `mabs`'s catch-all to fail closed and the asymmetry disappears.

---

### 4.6 `global_refs` — the `:let` reachability bug, reintroduced for `Effect`  · **MEDIUM**
`lib/cure/elab/program.ex:838` · catch-all `do: []`

The most instructive finding in the audit, because the fix for its twin is **three lines
above it** (quoted in §1). `global_refs` now handles `:let`. It does **not** handle
`effect_type` / `effect_pure` / `effect_bind`.

**What it silently does.** A def whose body sequences effects — `x <- helper(); pure(x)`,
elaborating to `{:effect_bind, {:global, :helper}, {:lam, …}}` — reports **no global
references at all** for the effectful spine. `reachable_def_names/2` therefore omits
`helper`, and, in the words of the existing comment about the identical `:let` failure,
*"co-emitting such a closure produced a module that called a function it never defined."*

Given the effect surface **is** the concurrency surface (fsm/actor/sup), this is squarely on
the path the language is built for.

---

### 4.7 `count_level` — the `{0,ω}` un-join safety gate is blind to `Effect`  · **HIGH**
*(raised from MEDIUM: two independent lenses found it and both skeptics graded it real, one at
HIGH, on the grounds that its polarity is permit-too-much rather than reject-too-much.)*
`lib/cure/elab/relevance.ex:451` · catch-all `do: 0`

`count_level` answers "how many times does variable `t` occur here?" and `join_binder_safe?`
consumes it as a **safety gate**, whose contract (moduledoc `:403-413`) requires a branch to
be *provably free* of the join binder before the un-join optimisation may fire.

**What it silently does.** For any `Effect`-wrapped subterm it returns **`0`** — "the variable
does not occur" — which is indistinguishable from a genuine absence. An occurrence **hidden
inside an effect node** therefore reads as absent, and the gate **authorises an optimisation
it is supposed to forbid**.

Note the polarity: this is not a gate that rejects too much. It is a gate that **permits too
much**, on the basis of an answer it did not actually compute. That is the same shape as
`escapes?` returning `false` for an unenumerated form — the very thing `escapes?`'s comment
says must never happen.

---

### 4.8 `has_hole?` — a hole inside an effect is invisible  · **LATENT, not live**
`lib/cure/elab/erase.ex:200` · catch-all `do: false`

Handles `:let` (swept) but not the `Effect` family, while its sibling `erase/2` immediately
above (`:160-166`) handles all three. So the walker **is** incomplete.

**But the bad state is unreachable today, and the skeptic proved it.** A surface hole cannot
currently get inside an effect node: `elaborate_declared_body` (`declarations.ex:600-606`)
tests `effect_goal?` **first** and routes effect-typed bodies to `elaborate_effect_branch`,
which — like `elaborate_expr_checked` and `elaborate_expr_typed` — has **no `{:hole, …}`
clause at all** and hard-errors instead. Such a definition therefore fails to elaborate and
never reaches `Env.defs`, so `hole_goals/1` can never be asked about it. The only Core hole
that lands in `Env.defs` is the bare top-level one, which `has_hole?`'s **first** clause
already handles.

Recorded as **latent hygiene**, not a live defect: it becomes a real bug the moment anyone
adds a route for holes inside effectful bodies — which is a plausible near-term change. Fix it
while fixing §4.0 (same file, same trio of clauses); do not claim it as a bug found.

*This is the audit working as intended. The lens found a genuine structural gap; the skeptic
established that nothing can currently drive it. Both facts are worth having, and conflating
them would have been the easy, wrong outcome.*

---

### 4.9 Dead retry on the dotted-qualified call path  · **LOW** (`UNVERIFIED` — agent lead)
`lib/cure/elab/elaborator.ex:269`

Reported as a sibling of the dead retry deleted in `a8b4e7e9`: a lambda-bearing
dotted-qualified call retries the identical `elaborate_implicit_app_bidirectional` call that
has just failed, and so can only fail again. Behaviour-preserving waste, not a wrong answer.
**Not yet hand-verified** — pending §7.3.

---

## 5. Coverage matrix

Mechanically derived: for each walker, which of the ten *compound* formers it explicitly
matches. `--` = falls to the catch-all. Read **only** with §3 in hand — a `--` in a Class A or
Class B walker is not a defect.

| walker | pi | lam | let | app | data | ctor | case | eff_type | eff_pure | eff_bind | class |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `core/kernel.ex subst_params` | OK | OK | -- | OK | OK | OK | OK | -- | -- | -- | **C** |
| `core/kernel.ex replace_branch_vars` | OK | OK | -- | OK | OK | OK | OK | -- | -- | -- | **C** |
| `core/kernel.ex rigid_index?` | OK | -- | -- | -- | OK | OK | -- | -- | -- | -- | B |
| `core/meta_check.ex canonical_head?` | OK | OK | -- | -- | OK | OK | -- | OK | OK | OK | B |
| `core/term.ex has_free_var?` | OK | OK | OK | -- | -- | -- | OK | -- | -- | -- | A |
| `core/validator.ex children` | OK | OK | OK | OK | OK | OK | OK | -- | -- | -- | A |
| `core/printer.ex print` | OK | OK | OK | OK | OK | OK | OK | -- | -- | -- | C (cosmetic) |
| `elab/subst.ex replace` | OK | OK | OK | OK | OK | OK | OK | OK | -- | -- | **C** |
| `elab/subst.ex shift` | OK | OK | OK | OK | OK | OK | OK | OK | -- | -- | **C** |
| `elab/elaborator.ex has_meta?` | OK | OK | -- | OK | OK | OK | -- | -- | -- | -- | **C** |
| `elab/elaborator.ex generalize` | OK | OK | -- | OK | OK | OK | OK | -- | -- | -- | **C** |
| `elab/elaborator.ex replace_branch_vars` | OK | OK | -- | OK | OK | OK | OK | -- | -- | -- | **C** |
| `elab/elaborator.ex abstract_term` | OK | OK | -- | -- | -- | -- | OK | -- | -- | -- | A |
| `elab/elaborator.ex free_indices` | OK | OK | -- | -- | -- | -- | OK | -- | -- | -- | A |
| `elab/elaborator.ex occurs_below?` | OK | OK | -- | -- | -- | -- | OK | -- | -- | -- | A |
| `elab/unify.ex mabs` | OK | OK | -- | OK | OK | OK | OK | -- | -- | -- | **C** |
| `elab/unify.ex escapes?` | OK | OK | -- | OK | OK | OK | OK | -- | -- | -- | B |
| `elab/unify.ex do_unify_struct` | OK | OK | -- | OK | OK | OK | -- | OK | -- | -- | (see §7.4) |
| `elab/erase.ex has_hole?` | OK | OK | OK | OK | OK | OK | OK | -- | -- | -- | **C** |
| `elab/program.ex global_refs` | OK | OK | OK | OK | OK | OK | OK | -- | -- | -- | **C** |
| `elab/relevance.ex count_level` | OK | OK | OK | OK | OK | OK | OK | -- | -- | -- | **C** |
| `elab/resolution.ex rekey_term` | OK | OK | -- | OK | OK | OK | OK | -- | -- | -- | **C** (owned elsewhere) |
| `elab/totality_closure.ex collect` | OK | OK | -- | OK | OK | OK | OK | -- | -- | -- | A |

**Formers missing across the 25 walkers:** `effect_pure` **24**, `effect_bind` **24**,
`effect_type` **21**, `:let` **15**, `:app` 6, `:data` 5, `:ctor` 5, `:case` 4, `:lam` 1,
`:pi` 0.

The gradient is the audit's whole story: **the older the former, the better covered.** `:pi`
is universal; `:let` is missing from 60% of walkers; the `Effect` family from ~95%. Coverage
is a direct function of *how long the former has existed*, which is precisely what "drift"
means and precisely what a type system is supposed to prevent.

---

## 6. The systemic fix

Patching twelve walkers by hand fixes today's formers and guarantees this recurs at former 25.
The recurrence is the defect. Options, in ascending order of strength:

1. **Sweep + regression test.** Fix the twelve; add a test that enumerates
   `Core.Term.t()`'s formers and asserts each Class C walker handles every compound one.
   Cheap; catches the next former **only if someone remembers to extend the enumeration**.

2. **Make the catch-alls fail closed.** Convert Class C catch-alls to raise on an unrecognised
   compound former. The next former added breaks the build loudly at every site that must be
   updated. This is the `escapes?` doctrine applied uniformly, and it converts a silent
   wrongness class into a compile-time error class. **Recommended.**

3. **Derive the traversals.** A single generic fold over `Core.Term` (a `Traversable`/
   `children`+`rebuild` pair — `Validator.children/1` is already 80% of it), with walkers
   expressed as folds. Eliminates the class by construction. Bigger change; the depth-tracking
   walkers (§3's caveat: binder nodes must bump `depth`, so a naive tuple-fold is *wrong* for
   them) need the fold to carry binder arity per former — which is exactly the information
   `Core.Term` should be publishing anyway.

(2) and (3) compose: fail closed now, derive later.

**Note on TCB scope.** §4.4 is a kernel change and is gated accordingly. Everything else in
§4 is E-layer and carries no TCB risk. §4.2's grade threading is arguably *restoring* the TCB
contract the kernel already implements in `core/term.ex`, not changing it.

---

## 7. Open questions / pending verification

Nothing below is settled. Each is a **probe**, not an argument — the audit's own house rule is
that "I could not construct a counterexample" is not a proof, and every one of these is a place
where I currently have only an argument.

1. **§4.0 — write the red test first.** The `Equivalent`/`reflexive` + `do`-block shape in
   §4.0 should fail *today*, at emit, with a wrong or unbound variable. Confirm the failure
   before fixing, and keep it as the regression test. **This is the highest-value single
   action in this document.**
2. **§4.1 trigger.** Construct a program in which an unsolved metavariable is genuinely
   nested inside a `:case`/`:let`/effect subterm of a chosen argument, and observe what the
   kernel does with `{:meta, id}` — crash, validator rejection, or worse. The severity is
   CRITICAL on the broken invariant alone, but the *consequence* is unknown, and that is not
   an acceptable place to leave it.
3. **§4.2 severity.** Does any `Subst`-processed (hence ω-ified) **type** reach the `{0,ω}`
   relevance check? If yes → the erasure discipline is not enforced on substituted types →
   **CRITICAL, soundness**. If no → HIGH, completeness (a conversion failure, since
   `conv.ex:77` compares grades by equality). **Must be settled.**
4. **§4.4 direction.** TCB. Can skipping index refinement inside a `let`/effect in a branch
   body ever make an ill-typed program *check*, or only make a well-typed one fail? Settle by
   probe. Any fix here needs an Antigen antibody + the full gate, per standing rule.
5. **§4.9** unverified; hand-check the retry guard for subsumption.
6. **`do_unify_struct`** fits none of the three classes — its fallthrough (`unify.ex:316`)
   attempts δ-conversion rather than returning a verdict. Given §3a it is probably inert, but
   it has not been read.
7. **Antigen — the real indictment.** None of these twelve were caught. The shape-coverage
   manifest reports **318/318 cells**, and that number is *true* and *useless here*: it
   measures **kernel** shapes, and every live defect in this document is in an **E-layer
   walker** that no cell exercises. A coverage cell per **(walker × former)** — mechanically
   enumerable from `Core.Term.t()` — would have caught all twelve on the day each former
   landed. **The metric was green while the bug class was wide open, which is the most
   important thing the audit found.**

---

## 8. Findings NOT confirmed (recorded so they are not re-litigated)

Kept deliberately, with the refuting argument, so nobody "rediscovers" them.

- **`totality_closure.collect` skipping recursive calls inside `Effect` nodes** — the audit's
  worst-case hypothesis (**a non-total function certified total**). **REFUTED**: `collect/1` is
  Class A (generic tuple descent, `:105`) and does see into effect nodes. This was the single
  highest-severity thing the audit went looking for, and it is not there.

- **`Validator.children/1` missing the effect formers** — **REFUTED**. `validator.ex:384-387`
  has explicit `eff_children` clauses for all three. The codegen release gate is sound; only
  the *diagnostic* `has_hole?` (§4.8) is blind, and that is unreachable anyway.

- **`Relevance.walk` treating `Effect(T)`'s payload as runtime-relevant** (`relevance.ex:373`)
  — reported as a completeness bug falsely rejecting erased type-level uses. **REFUTED on
  reachability, with a thorough trace**: `{:effect_type, _}` can never occur in a `body_term`
  that `Relevance.check` walks. The *only* site in the entire elaborator that recognises the
  surface name `Effect` is `idx_to_core` (`declarations.ex:1696`, `:1807-1821`), which is
  exclusively the **type/index-position** lowerer — never called from body/value elaboration.
  `Effect` is deliberately not registered as a family, global, or constructor, so `Effect(a)`
  in a body position fails name resolution outright. The one construct that *does* put
  `{:effect_type, …}` into a stored def body — `elaborate_typealias` — never calls
  `Relevance.check`. Dead code, not a live rejection.

- **`Erase.has_hole?` under-reporting holes** — **REFUTED as live**; retained as latent hygiene.
  See §4.8 for the reachability argument.
