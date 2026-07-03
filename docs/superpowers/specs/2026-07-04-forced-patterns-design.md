# Forced / Dot Patterns + Forced-Argument Erasure — Design (roadmap #5)

**Date:** 2026-07-04
**Roadmap row:** §2 #5 — "Forced/dot patterns + forced-argument erasure" (P+E+C, additive).
**Layers touched:** K (kernel `unify_indices`), P (parser dot-pattern syntax), E (elaborator dot-pattern elaboration), C (codegen forced-argument erasure).
**Verification:** differential oracle (`mix cure.oracle dotpat` vs `idris2 --check`) for the type-level behaviour; a codegen/run test for erasure (not oracle-measurable). Kernel change carries the **mandatory TCB gate** (new Antigen antibody + full Antigen suite + full test suite).

---

## 1. Goal

Make Cure accept the class of dependent matches where **matching a constructor forces an
equation between the scrutinee's index variables**, exactly as Idris2/Agda/Lean do, and give
the surface language the tools to express and optimise it:

- **K** — teach the kernel's index unifier the *Solution* step so a forced equation
  (`b := a`) is produced instead of a spurious `:impossible`.
- **P** — accept explicit `.e` dot-pattern syntax so a user can *write* the forced value.
- **E** — elaborate dot patterns: check the written forced value agrees with what
  unification determined; mark forced positions.
- **C** — erase forced constructor arguments at runtime (they are recoverable from an
  already-matched position, so they need not be scrutinised or stored).

### 1.1 The characterised gap (oracle probe `dp01`, this session)

```cure
mod Dp01
  type Nat = Z | S(Nat)
  type MyEq(a: Type) indices (x: a, y: a)
    mrefl : MyEq(a, w, w)
  fn congS({a: Nat}, {b: Nat}, p: MyEq(Nat, a, b)) -> MyEq(Nat, S(a), S(b)) = match p
    mrefl() -> mrefl()
end
```

Idris `--check` **accepts** the equivalent program; Cure **rejects** with
`{:conversion_failure, {:var,1}, {:var,0}}`. Matching `mrefl` should force `b = a` in the
branch (so the body `mrefl() : MyEq(S(a), S(a))` satisfies the goal `MyEq(S(a), S(b))`), but
Cure never derives that equation.

This is **not** covered by the landed #6 (`with`-abstraction) or #26 (inline `match`).

---

## 2. Background — how Cure unifies indices today, and why it fails

### 2.1 The index unifier lives in the KERNEL

When the kernel type-checks a `{:case, scrut, motive, branches}` term
(`lib/cure/core/kernel.ex:208`, `infer/2`), it independently unifies each constructor's
result indices against the scrutinee's indices in `check_case_branches`
(`kernel.ex:703-745`):

```elixir
case unify_indices(ctx, result_indices, scrut_indices, arity) do
  :impossible -> {:cont, :ok}         # branch treated as unreachable; body NOT checked
  verdict ->
    subst = case verdict do {:solved, s} -> s; :trivial -> %{} end
    ctx_branch = specialize_branch_context(extend_with_telescope(...), subst)
    # expected = motive applied at (result_indices ++ [ctor_value])
    ...
end
```

`unify_indices/4` returns `{:solved, subst} | :trivial | :impossible` (`kernel.ex:756`). The
same routine is exposed as `branch_unify/4` (`kernel.ex:770`) and reused by the elaborator
(`lib/cure/elab/elaborator.ex:1219, 1701`). **Both the kernel's own case checker and the
elaborator inherit `unify_indices`' verdict** — so there is no elaborator-only fix: a
carried-`Eq` trick in the elaborator is overridden when the kernel re-checks the `{:case}`
and computes `:impossible` itself. (This is the elaborator-hard-stop conclusion: no untrusted
term dodges the blocked judgement, because the kernel runs that judgement during re-check.)

### 2.2 The specific defect in `unify_one`

`unify_indices` walks the two index vectors pairwise via `unify_one` (`kernel.ex:805-833`).
Constructor-scope variables have de Bruijn index `< arity`; outer (scrutinee) variables have
index `>= arity`:

```elixir
defp unify_one({:var, i}, s, arity, subst) when i < arity, do: bind_index(i, s, subst)
defp unify_one(r, {:var, j}, arity, subst) when j >= arity, do: bind_index(j, r, subst)
defp unify_one(r, s, _arity, _subst) do
  if rigid_index?(r) and rigid_index?(s) and head_key(r) != head_key(s),
    do: :impossible, else: :undecided
end
```

For `dp01`, `mrefl`'s `result_indices = [{:var,0}, {:var,0}]` (both the ctor arg `w`), unified
against scrutinee indices `[a, b]`:

1. `unify_one({:var,0}, a)` → `bind_index(0, a)` → `subst = %{0 => a}`.
2. `unify_one({:var,0}, b)` → `bind_index(0, b)` → **key 0 already = `a` ≠ `b` → conflict →
   `:impossible`.**

The unifier never **resolves** the already-bound ctor var `0` (=`a`) and unifies `a =? b`.
Because `a` and `b` are *scrutinee index variables* — the **flexible/solvable** side of a
case-split, not truly rigid — the correct step is to bind `b := a` (a forced equation), not
to fail.

---

## 3. Reference algorithm (Agda `unifyIndices`, Idris2 dot-as-constraint)

Vendored: `reference/agda/.../LHS/Unify.hs` (commit `7273757e5e`), Idris2 `fd405085b`.

- **Agda** runs eager first-class index unification producing a `PatternSubstitution` `sigma`
  and a specialized branch telescope `tel` (`Unify.hs:182-186`, invariant `tel ⊢ sigma :
  varTel`). Forced positions become `DotP`. This is the model to follow — it directly yields
  "context specialized by `b ↦ a`".
- The crux (`Unify.hs:305-372`, `Problem.hs:110-150`): **on a LHS the pattern/index variables
  are the flexible ones.** `x =? t` with `x` flexible ⇒ a **Solution** step (orient +
  substitute). When *both* sides are flexible, `chooseFlex` picks which to eliminate. A
  genuine `NoUnify` (empty branch) only arises from **distinct constructors** (`Conflict`) or
  a **strongly-rigid self-occurrence** (`Cycle`).
- **Idris2** has no substitution object: dot patterns are metavariables + a deferred equality
  constraint (`Core/UnifyState.idr:99`), and impossibility is a *separate* coverage-time
  `clash`/`isEmpty` computation (`Core/Coverage.idr`). We follow **Agda's** substitution model
  because Cure's kernel already threads a `{:solved, subst}` through `specialize_branch_context`.

### 3.1 Minimal sound MGU (reference §4) — what we implement

Three rules over homogeneous index equations:

1. **Solution** — `x =? t` where `x` is a scrutinee index variable and `x ∉ FV(t)` (after
   strengthening): extend the substitution `x ↦ t`, apply it to the remaining equations and
   goal, and mark `x`'s position forced.
2. **Injectivity** — `c ūs =? c v̄s` (same constructor): replace with `ūs =? v̄s` pointwise.
3. **Conflict / Cycle** — `c… =? c'…` (distinct constructors) or `x =? …x…` (strong-rigid
   self-occurrence): this branch is absurd/empty → `:impossible`.

Skip (defer): the higher-dimensional injectivity engine, eta/record/size/literal steps, and
`--without-K` restrictions.

---

## 4. Design by layer

### 4.1 K — forced-equation refinement in `unify_indices` (TCB)

**File:** `lib/cure/core/kernel.ex` (`unify_indices/4`, `unify_one/4`, `bind_index/3`).

Introduce **resolve-before-bind** and the **Solution orientation** for scrutinee variables.
`bind_index(i, s, subst)` currently conflicts when `subst[i]` exists and differs from `s`.
Change it so that, when `subst[i] = v` already:

- unify `v =? s` recursively (`unify_one`), threading the growing `subst`;
- if that yields a **scrutinee-variable = term** equation (`{:var,j}` with `j >= arity` on
  either side), record the **forced substitution** for that scrutinee variable
  (`j ↦ other`), subject to the **occurs guard** (`j ∉ FV(other)`);
- Injectivity for equal-constructor terms; distinct constructors / occurs-cycle → `:impossible`.

The verdict grows from `{:solved, subst}` where `subst` currently only carries **ctor-arg →
term** entries to *also* carry **scrutinee-var → term** (forced) entries. The elaborator and
kernel already apply `subst` to the branch context/goal via `specialize_branch_context(_subst)`
(`kernel.ex:731-732`, `elaborator.ex:1287-1300`) — those consumers must accept forced
scrutinee-var keys (see §4.3).

**Soundness obligations (TCB gate).** A new Antigen antibody must witness that the refined
`unify_indices`:
- **terminates** (the resolve-before-bind recursion is well-founded: each step either
  decreases the multiset of unsolved equation nodes or fails);
- **collapses no distinct normal forms** — a forced `b := a` is only recorded when the
  indices are *provably* equal under the match (both are the same ctor-scope variable's image),
  never equating two independent values;
- preserves the existing `:impossible`/`:trivial`/`{:solved,_}` contract for all currently
  passing cases (no regression in the frozen oracle clusters or the kernel property suite).

This aligns Cure's `unify_indices` with Agda's `unifyIndices` Solution step, so per the
standing TCB policy it is pre-approved *conditional on passing the full gate*.

### 4.2 P — explicit `.e` dot-pattern syntax

**File:** `lib/cure/compiler/parser.ex` (pattern parsing, `parse_pattern`/`parse_match_arm`).

In **pattern position**, a leading `.` introduces a **forced (dot) pattern**: the pattern is
not matched but asserted to equal a given expression.

- Surface: `.x` (simple), `.(expr)` (compound / unambiguous form). The parenthesised form is
  primary and always accepted; bare `.name` / `.<literal>` are the sugar.
- AST: a new pattern node `{:forced_pattern, meta, expr_ast}` (name TBD-in-plan but fixed once
  chosen), where `expr_ast` is an ordinary expression AST parsed in pattern-expression mode.
- Disambiguation: `.` already lexes as `:dot` and is used for dotted module names in
  *expression* position (`Std.String`). In *pattern* position a `:dot` that begins a pattern
  atom is a forced pattern; a `:dot` following a name (module path) is unaffected because module
  paths do not begin a pattern. The plan pins the exact tokenizer/grammar rule and a negative
  test that `Std.String`-style names still parse in the contexts that use them.

### 4.3 E — elaborate dot patterns + accept forced scrutinee-var substitutions

**File:** `lib/cure/elab/elaborator.ex` (branch elaboration, `specialize_branch_context_subst`,
constructor-arm elaboration), possibly `lib/cure/elab/*` pattern lowering.

Two responsibilities:

1. **Consume forced scrutinee-var subst (from §4.1).** `specialize_branch_context_subst/2`
   (`elaborator.ex:1287`) and the branch-goal refinement must apply forced scrutinee-variable
   entries, not only ctor-arg entries. Because the elaborator's `branch_unify` call
   (`elaborator.ex:1219,1701`) is the *same* `unify_indices`, the forced entries appear
   automatically once §4.1 lands; the elaborator work is to **route them into the branch
   context + goal** so the arm body checks against the refined goal (this is what flips `dp01`
   even with **no** explicit dot syntax).
2. **Elaborate `{:forced_pattern, _, expr}`.** When a constructor argument position carries a
   dot pattern, elaborate `expr` to a Core term and **assert it is convertible** to the value
   that index unification determined for that position. Agreement ⇒ accept; disagreement ⇒
   reject (`{:forced_pattern_mismatch, written, determined}`). A forced position binds no new
   pattern variable. The forced Core term is recorded so §4.4 can erase it.

### 4.4 C — forced-argument erasure

**File:** `lib/cure/compiler/codegen.ex` (`compile_pattern_match`), reusing the per-argument
`quantities :: [:erased | :present]` already stored on each constructor
(`lib/cure/core/inductive.ex:110-116`).

A constructor argument whose value is **determined by index unification** (a forced position)
is recoverable at runtime and need not be scrutinised or bound. At code-gen:

- compute the **forced positions** for each constructor pattern (from the same unification /
  the `{:forced_pattern,…}` marks from §4.3);
- lower those positions to a wildcard (no binding, no match test) so the runtime pattern does
  not depend on the forced argument.

Per reference §5 this is a **separable optimisation** keyed off the forced marks; it changes
runtime shape but not typing. It is **not oracle-measurable** (the oracle only sees
`--check`), so it gets its own codegen/run test (§5.2). Erasure must be **conservative**: if a
position's forcedness is not established, keep it present (never erase a genuinely-matched arg).

---

## 5. Test plan

### 5.1 Oracle probes (type-level: K + P + E) — cluster `dotpat`

Each is a faithful `.cure`/`.idr` pair; `.idr` carries `%default total`, no module line.

| Probe | Program | Expected (post-fix) |
|---|---|---|
| `dp01_forced_eq` | `mrefl : MyEq(w,w)` matched vs `MyEq(a,b)`, body needs `a=b` (the base gap) | accept / accept |
| `dp02_explicit_dot` | same, written with an explicit `.a` dot pattern for the forced index | accept / accept |
| `dp03_vect_head` | `vhead : Vec(S(n)) -> a` matching `vcons` (length index forces `S n`) | accept / accept |
| `dp04_absurd_distinct` | a match whose indices force **distinct constructors** ⇒ impossible/absurd branch (empty), Idris accepts via impossibility | accept / accept |
| `dp05_occurs_cycle_neg` | a forced equation `x := …x…` (strong-rigid self-occurrence) | reject / reject |
| `dp06_dot_mismatch_neg` | explicit dot `.c` written where unification determined a **different** value | reject / reject |

`dp01`–`dp03` are the reach flips; `dp04` exercises the Conflict rule; `dp05`/`dp06` are the
soundness guards (must stay `reject`). Frozen in `test/oracle/dotpat/verdicts.json`, replayed
by `test/oracle_replay_test.exs`. **No pre-existing cluster may regress.**

### 5.2 Non-oracle tests

- **Kernel unit tests** for `unify_indices`: Solution (forced `b:=a`), Injectivity, Conflict,
  occurs-cycle rejection, and the existing ctor-arg cases (regression).
- **Antigen antibody** for the refined unifier (termination + no normal-form collapse) — the
  TCB gate; plus the full Antigen suite.
- **Parser unit tests** for `.e` / `.(expr)` and the module-path non-regression.
- **Erasure test (C):** compile a program with a forced constructor argument and assert the
  generated match does not bind/scrutinise the forced position (codegen inspection), and/or a
  `run-on-unix` execution that observes correct behaviour with the arg erased.

---

## 6. Scope boundaries / non-goals

- **In:** Solution + Injectivity + Conflict/Cycle MGU (homogeneous indices); explicit `.e`
  dot syntax; forced-arg erasure keyed off forced marks.
- **Out (deferred):** higher-dimensional injectivity engine; eta/record/size/literal unify
  steps; `--without-K` cycle restrictions; heterogeneous equation stacks. If a probe needs one,
  reach-pin it (an Antigen must-eventually-accept), do not silently widen scope.
- Erasure is conservative and optional to correctness — a forced arg left present is sound.

## 7. Risks

1. **TCB soundness.** The kernel unifier is soundness-critical. Mitigated by the Antigen
   antibody (termination + no normal-form collapse) and the full gate; the change mirrors
   Agda's documented Solution step.
2. **`subst` key overlap.** Forced scrutinee-var keys (`j >= arity`) share the substitution map
   with ctor-arg keys (`i < arity`). The plan must keep the two key spaces disjoint and ensure
   every consumer (`specialize_branch_context`, `specialize_branch_context_subst`, motive
   application) handles both. A red test asserting a branch with *both* a ctor-arg refinement
   and a forced scrutinee-var refinement guards this.
3. **Parser ambiguity.** `.` overloads module-path dotting. Mitigated by restricting forced
   patterns to pattern position and the parenthesised primary form, with a non-regression test.
4. **Erasure over-eagerness.** Erasing a genuinely-matched argument is a runtime bug.
   Mitigated by conservative forcedness (erase only positions unification determined) and the
   codegen test.
```
