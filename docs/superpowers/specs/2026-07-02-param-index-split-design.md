# Parameter/Index Split for Indexed Types — Design

**Status:** approved design (brainstorm complete 2026-07-02), pre-implementation.
**Branch/worktree:** continues on `autopilot/case-index-unification`
(`.claude/worktrees/case-index-unification`), on top of the 4.3 index-unification
fix (`5646c63`). This change sits *underneath* that work — the 4.3 refinement
keeps working unchanged once params are removed from unification.

## 1. Problem

Cure conflates datatype **parameters** and **indices**. Every `indexed type` is
declared through `Inductive.family(name, [], index_tele, level)`
(`lib/cure/elab/declarations.ex:405`) — an **empty parameter telescope**, with
*every* declared argument dumped into the index telescope. So for
`Vector(a: Type, n: Nat)`, the uniform type parameter `a` is carried as an index.

This is a genuine design error, not a cosmetic one:

- A **parameter** is uniform across all constructors and is *never refined by
  matching*. That invariant is what lets `a` be erased, never unified, and stay
  consistent across a function like `Std.Vector.append`.
- Because Cure treats `a` as an index, `a` enters the branch-index unifier as a
  bare-variable pair. The 4.3 work had to add — then remove — a var-vs-var
  "tie-break" precisely because a uniform parameter was being fed into
  unification. Removing the tie-break (`5646c63`) made the *orientation* harmless,
  but the root cause remains: **params should never reach the unifier at all.**

The kernel is *already built* for the correct design — the term form
`{:data, name, params, indices}` has separate slots; `infer` checks params against
a param telescope then indices against an index telescope (kernel.ex:160-167);
`check_family`/`check_ctor` scope indices and constructor arguments under the
params (kernel.ex:330, 347); `Inductive.param_telescope/2` exists; and
`infer({:ctor,…})` even carries a standing TODO: *"Slice-1 families are
parameter-free; prepend evaluated params here when parameters are introduced."*
The **only** thing collapsing the distinction is the elaborator. This design
finishes the seam the kernel authors left open.

## 2. Goal

Give Cure a real parameter/index distinction, so that a declared parameter is
**structurally never matched or refined** — fixing the design at the root and
retiring the tie-break saga (params never enter unification, so there is no
orientation to pick). Non-goals: runtime erasure changes (Cure erases type
machinery at compile time already; params are gone before BEAM), and parameter
*inference* (see §9, recorded as a future extension).

## 3. Surface syntax

Replace the `indexed type NAME(args…) where` form with:

```
type Vector(a: Type) indices (n: Nat)
  empty   : Vector(a, Z)
  prepend : a -> Vector(a, n) -> Vector(a, S(n))
```

- Head-paren arguments (`a: Type`) are **parameters**.
- The `indices (…)` clause arguments (`n: Nat`) are **indices**.
- The constructor block is delimited by **indentation** (as `fn` bodies and
  modules already are). No `indexed` keyword, no `where` keyword.
- A **parameter-free** family omits the head parens:
  `type Length indices (n: Nat)` (the `examples/length_indexed.cure` case).
- Constructors **restate the parameter** in their result type (`Vector(a, …)`),
  matching Agda/Idris/Lean; the elaborator checks it is uniformly the family's
  own parameter variable (§5).

`where` and `indexed` are removed from this construct. `where` is used *nowhere
else* in Cure's surface syntax (every other occurrence in the tree is English
prose in comments/docstrings), so removing it collides with nothing. Only two
declarations exist to migrate: `lib/std/vector.cure` and
`examples/length_indexed.cure`.

### 3.1 Disambiguation

`type` now heads both ordinary ADTs and indexed families; the parser
disambiguates on what follows the head:

- `type Option(a) = Some(a) | None` → ordinary ADT (an `=` follows).
- `type Vector(a: Type) indices (n: Nat)` + indented constructor block → indexed
  family (an `indices` clause and/or a typed-constructor block follows).

For this change, the `indices (…)` clause is **required** for the family form —
a `type NAME(...)` with an indented typed-constructor block but no `indices`
clause and no `=` is a parse error (revisit later if a param-only/GADT-syntax
ADT is wanted; see §9). A parameter-free family still writes the clause:
`type Length indices (n: Nat)`.

## 4. Architecture

Four layers change. Each is independently testable.

### 4.1 Parser (`lib/cure/compiler/parser.ex`)

Replace `parse_indexed_type` (which consumes `indexed` `type` then requires
`where`) with a `type`-headed path that:

1. Parses the family name.
2. Parses the optional head-paren parameter telescope (`parse_typed_params`).
3. Requires the `indices (…)` clause and parses its telescope
   (`parse_typed_params`).
4. Parses the indentation-delimited constructor-signature block
   (`parse_gadt_ctors`, unchanged — each ctor is a `{:gadt_ctor, …}` node).

Emit the same node shape the elaborator consumes, extended to carry the split:
`{:indexed_type, [name: …, params: <param telescope>, indices: <index
telescope>, line, col], ctors}`. (Today the meta key is `index_params` holding
everything; it becomes two keys, `params` and `indices`.)

The `indices` keyword must be added to the lexer/keyword set if it is not already
a recognized keyword; confirm and add if missing. It must not break existing code
— there are no identifiers named `indices` in `lib/` or `examples/` (verify in
the plan's first task; if any exist, they are in comments/strings only).

### 4.2 Elaborator (`lib/cure/elab/declarations.ex`)

- Read the split `params`/`indices` telescopes from the node meta (instead of
  the single `index_params`).
- Elaborate the parameter telescope, then the index telescope **in scope of the
  parameters** (indices may mention params; params may not mention indices).
- For each constructor: elaborate its result type, and **split the applied
  argument vector into its parameter prefix and index suffix** by the family's
  parameter arity. Store `result_params` (the parameter-position terms) and
  `result_indices` (the index-position terms) separately on the ctor.
- Call `Inductive.family(name, param_tele, index_tele, level)` with the real
  parameter telescope (the `[]` at declarations.ex:405 becomes `param_tele`), and
  declare constructors carrying both `result_params` and `result_indices`.

### 4.3 Inductive registry (`lib/cure/core/inductive.ex`)

- `family/4` already accepts a param telescope; no signature change. Confirm
  `param_telescope/2` and `index_telescope/2` both work with a populated param
  telescope.
- Extend the constructor record to carry `result_params` alongside the existing
  `result_indices`. Provide an accessor for the family's **parameter arity**
  (`param_count`), used by the kernel case path (§4.4).
- `ctor/…` constructor-builder gains the `result_params` field; existing
  parameter-free callers (all kernel unit tests using
  `Inductive.ctor(name, args, result_indices)`) must keep working — default
  `result_params` to `[]` when omitted, so a family with no parameters is
  unaffected.

### 4.4 Kernel (`lib/cure/core/kernel.ex`, `eval.ex`)

The value representation and every motive/unification site must agree on one
rule: **`{:vdata}` carries `params ++ indices`; the motive and the branch-index
unifier range over indices only; parameters are fixed context.**

- **`eval({:data, name, params, indices})`** → `{:vdata, name, params ++
  indices}`. **Unchanged** — this is already the behavior (eval.ex:39) and is
  required for type equality (`Vector(Int, 3)` ≠ `Vector(Bool, 3)` because their
  `vdata` param slots differ). Do **not** drop params from `vdata`.

- **`infer({:ctor, name, args})`** (kernel.ex ~180-190): implement the standing
  TODO. Build `vdata = eval(result_params) ++ eval(result_indices)` (both over
  `arg_env`), so a constructor-built value carries `params ++ indices`,
  consistent with `eval`. Today it builds indices-only; add the param prefix.

- **`check_ctor`** (kernel.ex ~347): check the constructor's `result_params`
  against the family's parameter telescope **and** verify uniformity (§5);
  check `result_indices` against the index telescope (existing
  `check_result_indices`). The count check for result indices is now against the
  *index* arity, not the full arity.

- **`check_motive_wf`** (kernel.ex): currently builds `data_value = {:vdata,
  dname, index_vals}` from `index_tele` only and applies the motive to
  `index_vals ++ [scrutinee]`. After the split, the scrutinee's `vdata` is
  `param_vals ++ index_vals`, so the constructed `data_value` must be `{:vdata,
  dname, scrut_param_vals ++ index_vals}` using the **scrutinee's actual
  parameters**. The motive still ranges over **indices + scrutinee only** (params
  are not abstracted by the motive). This requires passing the scrutinee's actual
  parameter values into `check_motive_wf` (split from `scrut_indices`, see
  below). Verdict on ill-formed motive is unchanged (`{:error, :bad_motive}`).

- **`infer({:case, …})`** (kernel.ex ~199-208): the scrutinee infers to
  `{:vdata, dname, scrut_args}` where `scrut_args = params ++ indices`. Split it
  by the family's `param_count` into `scrut_params` and `scrut_idx`. Then:
  - Pass `scrut_params` to `check_motive_wf` (for the reconciled `data_value`).
  - Pass `scrut_idx` (index portion only) to `check_case_branches`.
  - Result type: `apply_motive(motive_value, scrut_idx ++ [scrut_value])`
    (index portion only — the motive abstracts indices, not params).

- **`check_case_branches`** (kernel.ex): receives the index-only `scrut_idx`.
  A constructor's `result_indices` are now index-only, so `unify_indices(ctx,
  result_indices, scrut_idx, arity)` operates purely on indices — **parameters
  never enter unification.** `s_values = eval(result_indices)` (index-only), and
  `apply_motive(motive_value, s_values ++ [ctor_value])` (index-only), matching
  the motive's arity. `ctor_value = {:vctor, cname, arg_vals}` is unchanged.

- **`infer({:data, name, params, indices})`** (kernel.ex:160-167): already checks
  params against the param telescope then indices against the index telescope in
  scope of the param values. No change required beyond confirming it now
  exercises a non-empty param telescope.

- **`serialize.ex` / `Term`**: `{:data, name, params, indices}` is already the
  encoded shape; confirm round-trip with non-empty params (add a serialize test
  if the plan finds coverage missing).

The tie-break is **retired**: since params are sliced off before
`unify_indices`, the unifier only ever sees genuine indices. The
already-removed tie-break clause stays removed; no orientation decision exists.

## 5. Uniformity check (reject non-uniform parameters)

A constructor's result type must apply the family to the **family's own parameter
variables**, in order, in the parameter positions. `prepend : a -> Vector(a, n)
-> Vector(a, S(n))` is uniform (param slot is `a`); `oddball : Vector(Bool, Z)`
or `wrap : a -> Vector(List(a), Z)` are **non-uniform** (param slot is `Bool` /
`List(a)`, not the parameter variable `a`).

Non-uniform parameters are **rejected** at elaboration/kernel-check with a
dedicated diagnostic. This matches Agda (parameters left of the colon must be
applied uniformly; a constructor returning `Vec Bool …` is an error) and is the
only sound choice under explicit declaration: a parameter that varied per
constructor would have to be *refined* by matching, which is index behavior — the
exact unsoundness this change removes.

- The check compares each constructor's `result_params` against the family
  parameter telescope's bound variables (the de Bruijn variables standing for the
  parameters within the constructor's telescope). Equality is the kernel's
  structural term equality.
- Diagnostic: a canonical code/label (e.g. `non_uniform_parameter`) naming the
  family, the constructor, the offending parameter position, and guidance ("a
  parameter must be applied uniformly; make this position an index if it should
  vary"). Follow the existing diagnostic-code conventions in the elaborator (the
  repo has canonical diagnostic codes, cf. recent `duplicate_graph_id` /
  `value_constructor_tag` work). The plan pins the exact code and phase.
- The check lives where the constructor result is available with the family in
  scope: `check_ctor` in the kernel (authoritative, TCB) is the primary site;
  the elaborator may surface a friendlier message but the kernel check is the
  guarantee.

## 6. Migration

- `lib/std/vector.cure`: `indexed type Vector(a: Type, n: Nat) where` →
  `type Vector(a: Type) indices (n: Nat)`. Constructor bodies unchanged
  (`empty : Vector(a, Z)`, `prepend : a -> Vector(a, n) -> Vector(a, S(n))`).
  The `append` function body is **unchanged** — surface `match` infers its
  motive, which is not written by hand.
- `examples/length_indexed.cure`: `indexed type Length(n: Nat) where` →
  `type Length indices (n: Nat)` (parameter-free; head parens omitted).

## 7. Testing strategy

Red-green TDD, one build/test run at a time (never concurrent — a past concurrent
full-suite run caused a kernel panic).

Kernel-level (`test/cure/core/…`, using `Inductive.family/ctor` directly with a
non-empty param telescope):

1. **Parameter not matched.** A family `P(a: Type) indices (n: Dec)` with a
   constructor whose result index is ground; matching refines the *index* but the
   *parameter* stays the outer `a` — a body reusing an `a`-typed hypothesis in the
   branch type-checks. (This is the `Vector.append` regression, reduced to the
   kernel: the parameter must survive matching unchanged.)
2. **Uniformity rejected.** A family with a constructor whose `result_params`
   are not the family parameters → `check_ctor` returns the non-uniform-parameter
   error.
3. **Motive/vdata reconciliation.** A case on a param-bearing family checks a
   motive that mentions both the parameter (from context) and the index (bound by
   the motive); `check_motive_wf` accepts it, and a wrong-arity/parameter-leaking
   motive is rejected.
4. **Parameter-free family unaffected.** An existing index-only family
   (Dec/Ix/Box style, `result_params = []`) behaves exactly as before — regression
   guard that the split is a no-op when there are no parameters.
5. **Constructor value carries params.** `infer({:ctor,…})` of a param-bearing
   constructor yields `{:vdata, fam, param_vals ++ index_vals}` (the TODO is
   implemented) — asserted via the inferred type.

Surface/integration:

6. `Std.Vector` compiles under the new syntax and `append` type-checks, with the
   parameter provably never entering unification (the reduced kernel Test 1 is the
   authoritative guard; the surface compile is the end-to-end confirmation).
7. Parser: the new `type … indices (…)` form parses; the old `indexed type …
   where` form is gone (or explicitly errors with a migration hint — plan
   decides); `examples/length_indexed.cure` parses.

Regression: the **entire existing suite stays green**, including all 4.3
kernel/Antigen tests (`test/cure/core/case_soundness_index_test.exs`,
`test/antigen/…`) — this change sits underneath them. Full suite baseline before
this work: 2137 passing.

## 8. Invariants (soundness obligations)

1. **Parameter fixity.** For any well-formed family, every constructor's
   `result_params` equal the family's parameter variables (enforced by §5). Hence
   a parameter's value in any `vdata` of that family is determined solely by the
   family application, never by which constructor built it.
2. **Parameters excluded from refinement.** `unify_indices` is only ever called
   with index vectors (params sliced off in `infer({:case})`). No substitution
   binding can target or originate from a parameter position.
3. **vdata consistency.** For every family value, `eval({:data,…})` and
   `infer({:ctor,…})` produce `vdata` lists of identical length and shape
   (`params ++ indices`); the case path splits them by `param_count` identically.
4. **Motive arity.** The motive of a case abstracts exactly `index_arity + 1`
   arguments (indices + scrutinee); `check_motive_wf`, `infer({:case})` result
   type, and `check_case_branches` all apply the motive to index-only vectors
   plus the scrutinee.
5. **Backward compatibility.** For any family with `param_count = 0`, every code
   path is behaviorally identical to pre-change (params-empty slices are no-ops),
   so all existing param-free families and their tests are unaffected.

## 9. Future extension (recorded, out of scope)

**Optional parameter inference.** Idris-style inference (classify an argument as
a parameter iff it is uniform across all constructors) buys refactoring
robustness and annotation-free generated datatypes, but trades away locality
(whether `a` is a parameter becomes a non-local property of all constructors) —
which cuts against Cure's soundness-clarity ethos and Antigen's remit. Because
today's **reject** rule fires *only on an explicitly declared parameter*, it is
forward-compatible with a later **infer-when-omitted** mode: make the split
optional — check it when written (reject non-uniform), infer it when omitted.
This is purely additive and requires no reversal of this design. Defer until
generated indexed families or refactoring churn make it pay.

Also deferred: a param-only / GADT-syntax ADT (`type X(a) where …` with no
`indices` clause), and the case-index-unification run's own **Task 2**
(impossible-branch discharge), which resumes on top of this change.
