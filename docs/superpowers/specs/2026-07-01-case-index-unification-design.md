# Sound first-order index unification for dependent `case` — design

**Status:** approved design (autopilot Stage 0). First of three sub-projects
surfaced from the Antigen indexed-case 4.3 finding; the other two
(`Eq`/`rewrite` application-layer consolidation; a new Antigen `rewrite`/`Eq`
known-label vertical) are out of scope here and listed in §10.

## 1. Goal

Make the kernel's dependent-`case` branch refinement **complete for GADT-style
matching** by replacing the one-directional `branch_index_subst` zip with a
sound **bidirectional first-order unifier** over the scrutinee-vs-constructor
index vectors. This closes the documented 4.3 incompleteness (a ground
constructor result index is dropped, so a hypothesis at the unrefined index is
wrongly rejected) and, using the same unifier, **discharges provably-unreachable
branches** (a constructor whose indices clash with the scrutinee's can never
match, so its body need not type-check).

## 2. Motivation — the confirmed incompleteness

Antigen's `indexed/case` obligation 4.3 (`refinement(:well_typed)`) is currently
rejected by the kernel with `{:violation, {:wrongly_rejected, {:refine,
:branch_type}}}`. The reproducing construction (family `Ix(n:Dec)`, constructor
`wrap : (p:Dec) -> Ix Causal`):

```
def_type = Π(n:Dec). Π(h:Ix n). Π(ix:Ix n). Ix n
motive   = λ(n':Dec). λ(ix':Ix n'). Ix n'
body     = λn. λh. λix. case ix of { wrap p -> h }
```

Inside the `wrap` branch the required type is `Ix Causal` (the motive at the
constructor's own ground result index `Causal`), but `h`'s type stays the
unrefined `Ix n`, so conversion fails. A sound, refinement-complete kernel
accepts this: matching `wrap` forces `n := Causal` in that branch, and `h : Ix n`
is then literally `h : Ix Causal`.

The cause is `branch_index_subst/4` (`lib/cure/core/kernel.ex`):

```elixir
defp branch_index_subst(ctx, result_indices, scrut_indices, arity) do
  depth = Context.length(ctx)
  result_indices
  |> Enum.zip(scrut_indices)
  |> Enum.reduce(%{}, fn
    {{:var, i}, scrut_value}, acc ->          # ctor result index is a bare var → solve ctor arg i
      replacement = scrut_value |> Quote.reify(depth) |> Term.shift(arity, 0)
      Map.put(acc, i, replacement)
    {_other, _scrut_value}, acc -> acc         # DROPS every other pair (the bug)
  end)
end
```

It is a one-directional positional zip: it fires only when the *constructor's*
result index is a bare `{:var, i}` (solving a constructor argument), and drops
every other pair — including the case where the constructor's result index is a
**ground/compound term** (`Causal`) and the **scrutinee's** index is a variable
`n` (which should solve `n := Causal`).

## 3. Reference algorithm (Idris 2, verified in the local clone)

Idris has no bespoke "index refinement" pass; it falls out of **symmetric
first-order unification of the two type heads' argument vectors** (verified in
`/Users/ch/Develop/Idris2`):

- `unifyNoEta` on two `NTCon` heads decomposes to `unifyArgs` over the index
  vectors (`src/Core/Unify.idr:1168`) — `Ix Causal ~ Ix n` becomes `Causal ~ n`.
- Each pair is solved whichever side is the unknown; `unifyApp` orients the
  solvable head via a `swap` flag (`convertErrorS`, `:185`), so "scrutinee-index
  var := constructor's ground index" and "constructor-arg var := scrutinee term"
  are the *same* code path.
- `occursCheck` (`:366`) refuses cyclic solutions.
- A rigid/constructor **clash** with no solution yields `convertError`
  (`unifyApp`, `:927`) / `impossibleOK` True (`src/TTImp/ProcessDef.idr:97`) —
  the branch is dropped as **impossible**.

We adopt the *algorithm* but keep Cure's elimination-style application: Cure's
scrutinee index is a rigid de Bruijn variable + an explicit motive (Coq/Lean
idiom), not a clause metavariable, so "solve `n := Causal`" is recorded as a
local context specialization (the existing `specialize_branch_context`), **not**
Idris-style global hole instantiation. No metavariable store, no postponement.

## 4. Design

### 4.1 One new function, existing consumers unchanged

Replace `branch_index_subst/4` with:

```
unify_indices(ctx, result_indices, scrut_indices, arity)
  :: {:solved, subst} | :trivial | :impossible
```

`subst` is the **same** `%{de_bruijn_index => term}` map that
`specialize_branch_context/2`, `specialize_branch_value/3`, and
`replace_branch_vars/2` already consume. The application layer (the syntactic
`replace_branch_vars` substitution) is **not** touched — that consolidation is
sub-project ② and explicitly out of scope (§10). `:trivial` is the empty-subst
case (equivalent to today's empty map).

### 4.2 Integration into `check_case_branches`

`check_case_branches` gains exactly **one new arm**. Today the per-branch body is:

```
subst = branch_index_subst(ctx, result_indices, scrut_indices, arity)
ctx_branch = specialize_branch_context(ctx_branch, subst)
... expected = specialize_branch_value(apply_motive(...), ctx_branch, subst) ...
check(ctx_branch, body, expected)
```

It becomes:

```
case unify_indices(ctx, result_indices, scrut_indices, arity) do
  :impossible ->
    {:cont, :ok}                       # unreachable branch: body NOT checked (vacuous)
  verdict ->                           # {:solved, subst} | :trivial
    subst = subst_of(verdict)          # %{} for :trivial
    ... existing specialize + check(ctx_branch, body, expected) ...
end
```

The family-scoping guard from obligation 4.1 (`{:foreign_ctor, _}`) is unchanged
and still runs **before** unification (a foreign constructor is rejected, not
unified). Arity check unchanged.

### 4.3 The unifier

First-order unification restricted to the constructor-index fragment. Compare
each positional pair `(r, s)` where `r` is a constructor result-index **term**
(over the branch's extended context, i.e. the ctor telescope is in scope) and
`s` is the scrutinee's index **value** (reified to a term at the appropriate
depth). Accumulate a substitution or short-circuit:

- **variable on either side vs any term** — a solvable variable is (a) a
  ctor-telescope de Bruijn index introduced by this branch, or (b) an
  outer-context index variable (a rigid neutral var `{:vneutral, {:nvar, _}}`
  reified to `{:var, k}`). Bind it to the other side after an **occurs-check**
  (the bound variable must not occur in its own solution). Record in `subst`
  keyed by the de Bruijn index, with the shifting discipline of §4.4.
- **matching constructor/data heads** (`{:ctor, C, as}` vs `{:ctor, C, bs}`, or
  `{:data, N, ps, is}` vs `{:data, N, ps', is'}` with equal head/arity) —
  recurse structurally, unifying `as ~ bs` (and `ps ~ ps'`, `is ~ is'`),
  merging substitutions.
- **rigid ground vs rigid ground, definitionally equal** (via the kernel's own
  `Conv`) — contribute no binding (consistent).
- **definite rigid head clash** — two distinct rigid constructor/data heads (or
  a constructor vs a distinct rigid value) that can never be equal → `:impossible`.
- **undecidable** — a stuck neutral application, an unsolved variable against a
  non-matching-but-not-rigidly-clashing term, or any pair the unifier cannot
  confidently classify → contribute **no** binding and do **not** signal
  `:impossible`. The branch then falls through to the existing conversion-based
  body check (today's behavior). This is the conservative escape hatch.

The overall verdict: `:impossible` if any pair clashes; otherwise `{:solved,
subst}` (or `:trivial` if `subst` is empty).

### 4.4 De Bruijn discipline (the main risk)

Constructor-telescope variables and outer-context index variables live at
different depths. The existing `arity`-shift (`Term.shift(arity, 0)` in
`branch_index_subst`) is the template for constructor-side bindings; outer-side
bindings (solving a scrutinee index variable) must be recorded at the correct
outer depth so `replace_branch_vars` (which already `shift_subst`s under
binders) applies them consistently to both `ctx.types` and the expected goal.
The substitution merge across structural recursion must keep a single coherent
index space. This is where correctness risk concentrates; it is covered by
dedicated de Bruijn unit tests (§8).

### 4.5 Coverage unchanged

`check_coverage` is **not** modified: every declared constructor must still have
a branch present. An impossible branch is *present but vacuous* — its body is not
checked. No absurd-pattern surface syntax, no change to exhaustiveness.

## 5. Soundness invariants (the TCB boundary)

1. **Refinement soundness.** Every entry of `subst` is a definitional
   consequence of the scrutinee bearing this constructor in this branch, so
   applying it to context types and the goal is sound (standard dependent
   pattern-match refinement).
2. **Impossible only on definite clash.** `:impossible` fires **only** when two
   rigid constructor/data heads genuinely cannot be equal. Uncertainty (stuck
   terms, undecidable pairs) is **never** `:impossible`, so a body check that was
   actually required is never skipped.
3. **Occurs-check.** A variable is never bound to a term containing itself.
4. **Monotonic degradation.** When the unifier is unsure it produces no binding
   and no `:impossible`; the branch is then checked exactly as today. So the
   change is never *less* sound than the current kernel — it only *adds* accepted
   (well-typed) programs and *discharges* provably-dead branches.

## 6. Files touched

- `lib/cure/core/kernel.ex` — replace `branch_index_subst/4` with
  `unify_indices/4`; add the `:impossible` arm to `check_case_branches`. May add
  small private helpers (structural unify, occurs-check) local to the kernel.
- Reuse existing `Term.shift`, `Quote.reify`, `Conv`, `Inductive`,
  `replace_branch_vars`, `specialize_branch_context/value`. No new modules.

## 7. Non-goals

- No change to the `rewrite`/transport application layer (`replace_branch_vars`
  stays; consolidation is sub-project ②).
- No coverage/exhaustiveness change; no absurd-pattern syntax.
- No new Antigen vertical here (sub-project ③).
- No higher-order/pattern unification, no metavariable store, no constraint
  postponement — first-order only, decided eagerly.

## 8. Testing strategy (TDD, red→green, behavioral & immutable)

The **ready-made red test** is the existing Antigen 4.3 probe: after the fix,
`Antigen.Assays.Indexed.run(Generators.Indexed.refinement(:well_typed))` returns
`:ok` instead of `{:violation, {:wrongly_rejected, _}}`. Its assay test assertion
becomes `assert :ok`, and the challenge is added to the seed bank.

New kernel tests in `test/cure/core/case_soundness_test.exs` (or a sibling):

1. **Positive refinement (4.3 core).** The `h : Ix n` reuse term is accepted by
   `check_def`.
2. **Impossible-branch discharge.** A `case` whose scrutinee's index rigidly
   clashes with a constructor's ground result index accepts even with a
   deliberately ill-typed body in that branch — proving the body is *not* checked.
   A companion test proves a *reachable* branch with the same ill-typed body is
   still **rejected** (so discharge is not a blanket bypass).
3. **Occurs-check.** A constructed pair that would require a cyclic solution is
   not mis-solved (documents the guard; the branch falls through rather than
   binding a cyclic term).
4. **Clash vs undecidable.** A definite head clash yields discharge; a stuck /
   undecidable index does **not** discharge (body still checked) — asserting
   invariant §5.2.
5. **Regressions.** The 4.1 foreign-branch antibody still **rejects**
   (`{:foreign_ctor, _}` path intact); every existing `case_typing_test.exs`
   case (the legit `Dec`/`Box` matches) still passes.

The full `indexed/case` Antigen suite + committed corpus/seeds are the standing
regression net. One `mix test` process at a time (never concurrent).

## 9. Success criteria

1. `unify_indices/4` returns `{:solved, σ} | :trivial | :impossible` and replaces
   `branch_index_subst/4`; all its callers compile.
2. Antigen 4.3 `refinement(:well_typed)` replays `:ok`; the incompleteness
   finding is closed and its challenge seeded.
3. Impossible branches are discharged without body-checking; reachable ill-typed
   branches still rejected.
4. Invariants §5.1–§5.4 hold, each with a test.
5. Full suite green; the 4.1 antibody and all prior Antigen verticals still pass;
   no coverage/exhaustiveness behavior change.

## 10. Deferred sub-projects (not this run)

- **② `Eq`/`rewrite` application-layer consolidation** — collapse
  `replace_branch_vars` (case, syntactic) and `Eval.apply(motive, endpoint)`
  (rewrite, semantic transport) into one shared transport engine. Depends on and
  follows this work; wants ③'s probe as its net.
- **③ Antigen `rewrite`/`Eq` known-label vertical** — a Tier-A-style deep-cut
  probing Codex's merged rewrite normalization; the audit net for ②.
