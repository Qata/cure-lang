# Prim → Delta-Globals (task #15, K2 wave) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Retire the `{:prim, op, args}` Core node (and its `{:nprim}` neutral) in favor of registry-keyed builtin-op GLOBALS with literal acceleration in the certified-δ engine — surface behavior, oracle verdicts, classic-pipeline folding, and emitted runtime code all invariant — spec `docs/superpowers/specs/2026-07-09-prim-delta-globals-design.md` (hardened `8de233b`).

**Architecture:** Three phases (spec §1.7, risk R6): Phase 1 seeds the builtin-op def-kind + compute hook with `{:prim}` fully live (coexistence); Phase 2 flips every producer + retargets GuardLint/emit/Reduce; Phase 3 strips the node, flips `no_prim_node → :reject`, retargets Antigen, flips enumerated pins. K4 (absurd) is CLOSED-AS-LANDED — bookkeeping only, no code.

**Tech Stack:** Elixir, `Cure.Core.{Kernel,Eval,Normalise,Env(inductive.ex),Builtins,Validator}`, `Cure.Elab.{Elaborator,GuardLint,Emit}`, `Cure.Types.{CoreBridge,Reduce}` (carve-out), Antigen.

## Global Constraints (every task implicitly includes these)

- Working dir: `/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/kernel-parity-batch`, branch `autopilot/kernel-parity-batch`. Never the parent checkout.
- Two-pipeline steer: kernel = `lib/cure/core/*`, dependent elaborator = `lib/cure/elab/*`; `lib/cure/types/*`/`lib/cure/compiler/*` are decoys EXCEPT the spec §1.4 carve-out: `lib/cure/types/core_bridge.ex` + `lib/cure/types/reduce.ex` ONLY (Core-grammar consumers, D2 §8 precedent, pre-authorized). Final types/ diff = exactly those two files; compiler/ empty.
- Strict red-green; tests behavioral, immutable once green; pin flips ONLY where enumerated, each with a one-line justification (C-3 discipline); spec-§1.4-pinned classic tests (`reduce_test.exs` assertions) NEVER change.
- ONE `mix` command at a time, ever. Full suites once per phase boundary where the phase says so; final gates alone in Task 4. NO `mix cure.oracle` — replay only; divergence = STOP.
- Ghost commits `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, NO trailers, explicit pathspec. Commit per task (Phase 2 may split into 2 commits: elaborator+lint, then emit+bridge).
- Record `git rev-parse HEAD` at Task 1 Step 0 as `<pre-15-commit>`.
- STOP-and-report = spec §4.7's per-risk list verbatim (R1 registry pin fails; R2 any ReduceTest/EqualityTest assertion change; R3 congruence retarget loses judgement strength; R4 builtin-op def reaches `Eval.eval` bodyless; R5 unenumerated error-shape flip; R6 a phase boundary leaves validator/kernel/emit disagreeing; R7 saturated/unsaturated lowering changes any existing program's runtime behavior) + any surface program newly rejected by type-directed dispatch (spec predicts ZERO) + replay divergence + any pre-existing test failing (except the known one-off Antigen-seed flake, re-run once alone).
- Line anchors are from the 2026-07-09 scout/spec; re-locate by quoted code.

## File Structure

- Phase 1: `lib/cure/core/inductive.ex` (Env builtin-op marker), `lib/cure/core/builtins.ex` (op seeding), `lib/cure/core/eval.ex` (fold made shared/public), `lib/cure/core/normalise.ex` (compute hook); Test: `test/cure/core/builtin_op_test.exs` (NEW).
- Phase 2: `lib/cure/elab/elaborator.ex` (build_binop + literal chain), `lib/cure/elab/guard_lint.ex`, `lib/cure/elab/emit.ex`, `lib/cure/types/core_bridge.ex`, `lib/cure/types/reduce.ex`, `lib/antigen/generators/surface_expr.ex`; Test: additions to builtin_op_test + existing suites as gates.
- Phase 3: strip across core (kernel/eval/value/normalise/conv/quote/term/serialize/validator) + elab walkers (elaborator/subst/unify/resolution/erase) + guard_lint prim clauses + emit prim clauses; validator ratchet; Antigen retargets (`primitive.ex`, `malformed.ex`, `conv_pair.ex`, `serialization.ex`, `dep_match.ex`, `totality.ex`, `equality.ex`, `shrink.ex`, `coverage.ex`); enumerated pin flips; `test/fixtures/core_conformance.txt`; docs drift + K4 ledger line.

---

### Task 1 (Phase 1): builtin-op def-kind + compute hook (coexistence — `{:prim}` untouched)

**Files:** Modify `lib/cure/core/inductive.ex`, `lib/cure/core/builtins.ex`, `lib/cure/core/eval.ex`, `lib/cure/core/normalise.ex`. Test: `test/cure/core/builtin_op_test.exs` (NEW).

**Interfaces produced:** `Env.get_def(env, :int_add)` → `%{…, builtin_op: :add}`; `Builtins.seed/2` also seeds the 24 op defs (11 int binary + int_neg, 10 float binary + float_neg — see the table); `Eval.fold/2` public (`@doc false`); `Normalise` folds saturated literal builtin-op spines under `delta: :certified`.

- [ ] **Step 0:** `git rev-parse HEAD` → `<pre-15-commit>`. Read inductive.ex's Env section (defstruct :12, add_def :33-52, get_def :55, certify/certified? :68-86), builtins.ex in full, eval.ex:38-145, normalise.ex:190-250.
- [ ] **Step 1 (red):** write `test/cure/core/builtin_op_test.exs`:

```elixir
defmodule Cure.Core.BuiltinOpTest do
  @moduledoc """
  Task #15 / K2 wave (spec 2026-07-09-prim-delta-globals): primitive arithmetic
  as registry-keyed builtin-op GLOBALS with literal acceleration in the
  certified-δ engine (Lean reduce_nat / Idris Builtin-op analog). §G.1 rules
  preserved: partial ops stay neutral; open spines stay stuck (congruence).
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Context, Env, Kernel, Normalise}

  defp env, do: Builtins.seed(Env.empty())
  defp ctx, do: Context.empty(env())

  defp app2(g, a, b), do: {:app, {:app, {:global, g}, a}, b}

  test "int_add types as an ordinary global Pi" do
    assert {:ok, _pi} = Kernel.infer(ctx(), {:global, :int_add})
  end

  test "saturated literal spine folds under certified delta: 3 + 5 => 8" do
    v = Normalise.nf(ctx(), app2(:int_add, {:int_lit, 3}, {:int_lit, 5}), delta: :certified)
    assert {:vint, 8} = v
  end

  test "comparison folds to the inductive Bool ctor" do
    v = Normalise.nf(ctx(), app2(:int_lt, {:int_lit, 1}, {:int_lit, 2}), delta: :certified)
    assert {:vctor, :True, []} = v
  end

  test "G.1 rule 1: div/rem by literal zero stays neutral (never crashes)" do
    for g <- [:int_div, :int_rem] do
      v = Normalise.nf(ctx(), app2(g, {:int_lit, 7}, {:int_lit, 0}), delta: :certified)
      assert match?({:vneutral, _}, v)
    end
  end

  test "open spine stays stuck; conversion is spine congruence" do
    # under a binder: int_add x 1 vs int_add x 1 convertible; vs int_add x 2 not
    ctx1 = Context.extend(ctx(), Cure.Core.Eval.eval({:int_type}, []))
    t1 = app2(:int_add, {:var, 0}, {:int_lit, 1})
    t2 = app2(:int_add, {:var, 0}, {:int_lit, 2})
    assert {:ok, _} = Kernel.infer(ctx1, t1)
    v1 = Normalise.nf(ctx1, t1, delta: :certified)
    assert match?({:vneutral, _}, v1)
    refute Cure.Core.Conv.conv?(ctx1, t1, t2)
    assert Cure.Core.Conv.conv?(ctx1, t1, t1)
  end

  test "R1 pin: a user-registered int_add with its OWN body is never builtin-folded" do
    # Register int_add as an ORDINARY def (constant-42 body) in a NON-seeded env:
    # the builtin marker comes only from Builtins.seed, so this def has none.
    ty = {:pi, {:int_type}, {:pi, {:int_type}, {:int_type}}}
    body = {:lam, {:int_type}, {:lam, {:int_type}, {:int_lit, 42}}}
    env = Env.empty() |> Env.add_def(:int_add, ty, body) |> Env.certify(:int_add)
    ctx = Context.empty(env)
    v = Normalise.nf(ctx, app2(:int_add, {:int_lit, 3}, {:int_lit, 5}), delta: :certified)
    assert {:vint, 42} = v
  end
end
```

(Exact `Normalise.nf`/`Conv.conv?` arities and env-certify API: crib from `test/cure/core/stuck_elim_delta_test.exs` / `int_prim_test.exs` — ASSERTIONS immutable, plumbing adjustable. If #10's global-collision protection makes the R1 construction impossible as written, pin the protection's actual behavior instead — the invariant is "never builtin-folded", report the adaptation.)
- [ ] **Step 2 (verify red):** run scoped — all fail (`int_add` unknown global / no folding). Record.
- [ ] **Step 3 (implement):**
  - `inductive.ex` Env: `add_def/5` keeps its shape; add `register_builtin_op(env, name, op_key)` that `Map.update!`s the existing def to add `builtin_op: op_key`, and `builtin_op(env, name)` returning the key or nil (get_def-based). Defs seeded by Builtins carry the marker; user defs never do.
  - `builtins.ex`: add the op table + seeding (after the inductive seeds, so Bool exists for comparison codomains):

```elixir
  @int, @float, @bool as module attrs or inline:
  # {name, op_key, domain, codomain}
  @ops [
    {:int_add, :add, :int, :int}, {:int_sub, :sub, :int, :int},
    {:int_mul, :mul, :int, :int}, {:int_div, :div, :int, :int},
    {:int_rem, :rem, :int, :int},
    {:int_lt, :lt, :int, :bool}, {:int_le, :le, :int, :bool},
    {:int_gt, :gt, :int, :bool}, {:int_ge, :ge, :int, :bool},
    {:int_eq, :eq, :int, :bool}, {:int_ne, :ne, :int, :bool},
    {:float_add, :add, :float, :float}, {:float_sub, :sub, :float, :float},
    {:float_mul, :mul, :float, :float}, {:float_div, :div, :float, :float},
    {:float_lt, :lt, :float, :bool}, {:float_le, :le, :float, :bool},
    {:float_gt, :gt, :float, :bool}, {:float_ge, :ge, :float, :bool},
    {:float_eq, :eq, :float, :bool}, {:float_ne, :ne, :float, :bool}
  ]
  @unops [{:int_neg, :neg, :int}, {:float_neg, :neg, :float}]
```

  Seed each as `Env.add_def(env, name, pi_of(domain, codomain), nil)` + `Env.register_builtin_op(env, name, op_key)`, with a per-name exclude check mirroring `maybe_seed` (a module locally declaring the name wins and gets NO marker — that plus the marker-keyed hook IS the R1 guarantee). Type terms: `{:int_type}`/`{:float_type}`/`{:data, :Bool, [], []}`. NOTE `int_rem`: Int-only (matches infer_prim :1048). Arity check: binary ops 2, neg 1.
  - `eval.ex`: `defp fold` → `@doc false def fold` (same table, byte-identical clauses; Eval's own prim clause keeps calling it).
  - `normalise.ex` `unfold_certified_head`: at the `{:nglobal, name}` arm, dispatch FIRST on the builtin marker (spec §1.2's load-bearing ordering — a bodyless def must never reach the generic `Eval.eval(body, [])` path):

```elixir
      {:nglobal, name} ->
        case Env.get_def(sig, name) do
          %{builtin_op: op} when not is_nil(op) ->
            builtin_op_fold(op, args, sig, opts)

          _ ->
            <the existing with-block, unchanged>
        end
```

```elixir
  # Literal acceleration for builtin-op globals (spec 2026-07-09 §1.2; Lean
  # reduce_nat / Idris Builtin-op analog). Fold ONLY a saturated spine whose
  # arguments all whnf to literals — via the SAME audited table Eval uses
  # (§G.1: div/rem by literal zero returns :stuck and the spine stays neutral).
  # Anything else (open args, wrong arity/overapplication) stays stuck: never
  # unsound, at worst a missed unfold.
  defp builtin_op_fold(op, args, sig, opts) do
    arity = if op == :neg, do: 1, else: 2

    with true <- length(args) == arity,
         vals = Enum.map(args, &whnf_value(&1, sig, opts)),
         true <- Enum.all?(vals, &match?({:vint, _}, &1) or match?({:vfloat, _}, &1)) do
      case Eval.fold(op, vals) do
        :stuck -> :stuck
        value -> {:ok, value}
      end
    else
      _ -> :stuck
    end
  end
```

  (Adjust to `whnf_value`'s real arg shape — spine args may already be values; verify against how the ncase arm treats them, and Eval.fold's exact arg convention (list vs pair) at eval.ex:95-100.)
- [ ] **Step 4 (green + neighborhood):** scoped file 6/6 → `mix test test/cure/core/` all green (coexistence: every prim test untouched and passing).
- [ ] **Step 5: Commit** `feat(kernel): builtin-op def-kind + literal-acceleration delta hook (K2 phase 1; {:prim} coexists)` — pathspec the 4 lib files + test.

---

### Task 2 (Phase 2): flip every producer; retarget GuardLint, emit, core_bridge/Reduce

**Files:** `lib/cure/elab/elaborator.ex`, `lib/cure/elab/guard_lint.ex`, `lib/cure/elab/emit.ex`, `lib/cure/types/core_bridge.ex`, `lib/cure/types/reduce.ex`, `lib/antigen/generators/surface_expr.ex`.

- [ ] **Step 0 (the corpus survey — spec §1.3/§1.4 obligations, read-only):** (a) verify by grep that `==`/`!=` on non-int/float/bool operands appears in NO test/oracle surface program (spec sampled 4 oracle `==` uses, all int-guard; make it exhaustive over `test/oracle/**/*.cure` + `test/**/*.exs` surface fixtures + `examples/`); (b) verify zero live float-typed dependent-index arithmetic reaches core_bridge (grep classic-pipeline tests for float refinement indices). Any counterexample → STOP (spec §4.7).
- [ ] **Step 1 (red):** add to `builtin_op_test.exs` (new describe, or a small elab-side file `test/cure/elab/binop_lowering_test.exs`): elaborating `fn f(x: Int) -> Int = x + 1` yields Core containing `{:app, {:app, {:global, :int_add}, …}` and NO `{:prim,…}`; a float version yields `float_add`; `x == 1` in an Int guard lowers to `int_eq`. Run: red (still prims).
- [ ] **Step 2 (elaborator):** `build_binop` (elaborator.ex:638-655): the `:==`/`:!=` clauses' else-branches and the arithmetic catch-all switch on `primitive_scrut_kind(l_type, sig)` (already threaded, currently discarded by the catch-all — spec §1.3): `:bool` → existing `app2(:eq/:ne,…)` (== only); `:int` → `app2(:"int_#{op}",…)`-style via an explicit op→name map (NO dynamic atom construction — a literal map `%{add: :int_add, …}` per type); `:float` → float map; anything else → `{:error, {:unsupported_operand_type, op_sym}}`. Literal-pattern chain (elaborator.ex:2664): `{:prim, :eq, [scrut, lit]}` → `app2(:int_eq, scrut, lit)` (literal patterns are Int; verify whether float literal patterns exist — if yes, dispatch on the literal's form). `prim_op/1` stays for now (dead after this task, stripped in Phase 3).
- [ ] **Step 3 (GuardLint):** add spine-recognizing clauses ABOVE the prim ones (both live this phase):

```elixir
  # Builtin-op global spine (K2, spec 2026-07-09 §1.6): registry-keyed via the
  # def record — a user def named int_add carries no marker and falls to the
  # sound uninterpreted fallback.
  defp bool_form({:app, {:app, {:global, g}, a}, b}, ctx, st) do
    case Env.builtin_op(Context.signature(ctx), g) do
      op when is_map_key(@cmp, op) -> (the existing comparison body over a/b)
      _ -> :error
    end
  end
```

  and the `int_form` twins for `:add`/`:sub`/`:mul` (mul keeps the literal-multiplicand linearity guard). Only INT-typed forms translate (int_form's var clause already gates on `{:vint_type}`); float ops fall to `:error` → uninterpreted fallback (sound). Verify GuardLint has access to the signature (it holds `ctx`); alias Env if needed.
- [ ] **Step 4 (emit):** per spec §1.5: (a) saturated inline — in the app-spine lowering, when `spine/2` yields head `{:global, g}` with `Inductive.builtin_op(env, g)` = op and exactly-arity args, emit `{:op, @line, erl_binop(op), …}`/unop (registry-keyed, NOT bare-atom); (b) a new clause BEFORE the generic bare-`{:global,…}` clause (emit.ex:270-275): unsaturated builtin-op reference → local `{:fun, @line, {:clauses, [...]}}` wrapper computing the op. Keep the `{:prim,…}` lowering clauses (both live until Phase 3).
- [ ] **Step 5 (carve-out):** `core_bridge.ex` — `to_core` binary_op/unary_op clauses produce builtin-op spines with SHAPE dispatch (either converted operand `{:float_lit,_}` → float_*, else int_*; spec §1.4); STOP producing `and/or/not` prims (those clauses return `:error` → `structural_congruence` + surface `fold_bool_binop` keep Bool folding, the recorded precedent). `from_core` — DEDICATED reverse clauses for builtin-op-headed spines (reverse map to `{:binary_op, [operator: :+], …}` etc.) placed BEFORE the generic `{:app,…}` unwind clause (spec §1.4's mis-render trap); delete the prim reverse clauses in Phase 3, keep this phase. `reduce.ex` `kernel_normalize_via_core` (:97-99): replace `Eval.eval([]) |> Quote.reify()` with kernel normalization over a builtins-seeded env (memoized `Builtins.seed(Env.empty())`; use the `Normalise` entry that accepts an env/context + `delta: :certified` and reify the result — crib the exact call shape from how `test/cure/core/stuck_elim_delta_test.exs` or `nat_int` work drives `Normalise.nf`).
- [ ] **Step 6 (Antigen lockstep):** `surface_expr.ex` :44 encoder emits the builtin-op spine (it differentially pins build_binop's output).
- [ ] **Step 7 (gates):** scoped red file green → `mix test test/cure/elab/` → `mix test test/cure/types/` (ReduceTest/EqualityTest assertions UNCHANGED — R2 STOP otherwise) → `mix test test/cure/e2e/frp_beam_test.exs` + `mix test test/cure/compiler/dependent_surface_codegen_test.exs` (runtime ABI) → `mix test test/antigen/` → `mix test test/oracle_replay_test.exs` (guard clusters sensitive) — one at a time. Expected pin flips HERE (enumerate + justify each): `bool_connective_lowering_test.exs:23-38` ("Int == stays a native :eq prim" — the deliberate anti-pin, flips to int_eq spine), `literal_pattern_test.exs` shape pin, `emit_test.exs` prim-shape rows if they assert producer output, `guard_lint_test.exs:17`-style direct-prim constructions (these may stay green while prim clauses live — flip in Phase 3 if so). Anything else red = STOP.
- [ ] **Step 8: Commit(s):** `feat(elab): lower arithmetic/comparison to builtin-op globals (K2 phase 2a)` and `feat(emit+bridge): builtin-op spine lowering, GuardLint spine recognition, Reduce via kernel normalization (K2 phase 2b)` — explicit pathspecs.

---

### Task 3 (Phase 3): strip `{:prim}`/`{:nprim}`, ratchet, Antigen retargets, pin flips

**Files:** strip list per spec §2 (kernel.ex :69/:998/:1037-1105; eval.ex :47 prim clause — `fold` STAYS, Normalise uses it; value.ex :56; normalise.ex :171-172; conv.ex :123/:161-162; quote.ex :95-96; term.ex :62/:106/:176/:220/:258; serialize.ex :33/:152; validator.ex children :128; elaborator :2053/:3939 + now-dead `prim_op/1`; subst.ex :69/:106; unify.ex :258/:385; resolution.ex :37; erase.ex :139; guard_lint prim clauses; emit :188-194 prim clauses; core_bridge from_core prim reverse clauses); `lib/cure/core/validator.ex` ratchet; Antigen files per spec §3; `test/fixtures/core_conformance.txt`; enumerated test-pin flips; docs (grammar spec §J drift + audit pointer + K4 ledger line + parity-ledger #15 row).

- [ ] **Step 1 (Antigen retargets FIRST, node still live):** `primitive.ex` full retarget to builtin-op spines (fold reachability, stuck paths, div-zero rules — the generator's property tests are the oracle, iterate); `malformed.ex` :53/:56 (unknown-op → an UNREGISTERED global spine `{:app,…{:global,:nosuchop}…}` erroring as unknown global; wrong-operand → int_add on a ctor, erroring as app-domain mismatch — new tags enumerated per R5); `conv_pair.ex` :50 nprim rows → builtin-spine napp congruence rows (pins spec §1.8/R3); `serialization.ex` :23/:95-97 grammar rows re-spell as spines; `dep_match.ex` :105 computed-index row re-spells; `totality.ex` :342; `equality.ex` :150-152; `shrink.ex` :172 child slots; `coverage.ex` :92 former class (prim class retires or re-keys to builtin-op spines — check what the coverage gate pins); `totality_closure_assay.ex` :93 sanity (op names as terminal call-graph nodes). Run `mix test test/antigen/` — green with the retargets while both representations exist.
- [ ] **Step 2 (strip):** remove every listed clause (removal-only; re-locate by quoted code). Keep: `Eval.fold`, the validator `no_prim_node` PREDICATE (:193), emit's erl_binop/erl_unop tables (the inline uses them). `Term.term?` drops `{:prim,…}` — the grammar shrink.
- [ ] **Step 3 (ratchet + docs):** wave0 `no_prim_node: :warn → :reject` with the Phase-C-style comment; ADD `|> Map.put(:no_prim_node, :reject)` to `@release_config` (currently missing — the drift); fix `final-core-grammar-design.md` §J's `:off` claim + add the audit pointer (spec §6.6: pointer, not rewrite); parity-ledger: #15 row done + K4 closed-as-landed line.
- [ ] **Step 4 (pin flips, enumerated):** rewrite `int_prim_test.exs`/`float_prim_test.exs` as builtin-op suites (same §G.1 behaviors, spine spelling — fold/stuck/zero-divisor/defeq/typing; the typing negatives become app-domain errors per R5); `bool_connective_defeq_test.exs:80-92` residual-prim rows (the terms leave the grammar — replace with builtin-spine equivalents or drop with justification); `guard_lint_test.exs` direct-prim constructions → spines; `validator_test.exs` ratchet rows (+ the "only retired primitives reject in Wave 0" meta-pin gains `no_prim_node`); conformance fixture `(prim …)` rows → spine spellings (accept) + serialize negative-decode row (mirror D2's precedent); `term_test`/`serialize_test`/`value_test` grammar rows; the scout's remaining ~20-file list — sweep by grep `{:prim,` over `test/`, flip or re-spell each with justification, NOTHING flipped silently.
- [ ] **Step 5 (gates):** `mix test test/cure/core/` → `mix test test/cure/elab/` → `mix test test/antigen/` → `mix test test/cure/types/` — green, one at a time.
- [ ] **Step 6: Commit** `refactor(kernel)!: strip {:prim}/{:nprim} from Core — builtin-op globals are canonical (K2 phase 3; no_prim_node :reject; K4 closed)` — explicit pathspecs (lib + tests + fixtures + docs).

---

### Task 4: full gate + final verification

- [ ] **Step 1 (alone, in order):** 1. `mix test test/antigen/` (count re-derived vs 499 + retargets). 2. `mix test` — 0 failures; delta vs 3265 fully enumerated (new builtin_op/binop tests + retargeted/rewritten files ± dropped rows). 3. `mix test test/oracle_replay_test.exs` — zero divergence.
- [ ] **Step 2:** from `<pre-15-commit>`: grammar greps — zero `{:prim,`/`{:nprim` constructors under `lib/cure/core/`, `lib/cure/elab/`, `lib/antigen/`, AND `lib/cure/types/core_bridge.ex` (validator predicate + erl tables excepted); `git diff --stat -- lib/cure/types/` = exactly core_bridge.ex + reduce.ex; `lib/cure/compiler/` empty; ghost authors only; the R1 pin green; K4/drift docs landed.
- [ ] **Step 3:** report per the report-back spec; update memory (kernel-primitive-endgame → CLASS CLOSED) per its instructions.

## Self-review notes (spec-coverage map)

- §1.1 registry keying → T1 Step 3 (marker only via seed) + R1 pin + GuardLint/emit registry lookups. §1.2 hook+ordering → T1 Step 3 (dispatch-first shape, bodyless never reaches Eval.eval). §1.3 monomorphic set + type-directed dispatch + corpus survey → T1 table, T2 Steps 0/2. §1.4 carve-out (to_core shape dispatch, from_core ordered reverses, Reduce via kernel normalization, ReduceTest pin) → T2 Step 5. §1.5 emit → T2 Step 4. §1.6 GuardLint → T2 Step 3 + Phase-3 strip. §1.7 phases → task structure; both-live invariants stated per phase. §1.8 congruence → conv_pair retarget (T3 Step 1) + open-spine test (T1). §1.9 error churn → T3 Steps 1/4 enumerations. §4.5 greps incl. core_bridge → T4 Step 2. §4.6 K4+drift → T3 Step 3. §0 decision record → untouched (spec-resident).
- Latitude: exact Normalise/Conv API arities (crib from named test files; assertions immutable); the op→name literal maps' spelling; Antigen retarget shapes (iterate against immutable property tests); pin-flip enumeration contents (each justified); gate recounts. All report-required.
- Known in-task decision points with STOP fallbacks: whnf_value arg convention in the hook; #10-collision interaction with the R1 pin construction; float literal patterns existence; Reduce's exact Normalise entry; coverage.ex former-class retirement shape.
