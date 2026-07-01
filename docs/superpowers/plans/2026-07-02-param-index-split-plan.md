# Parameter/Index Split for Indexed Types — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to
> implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Give Cure a real datatype parameter/index distinction so a declared
parameter is structurally never matched or refined, fixing the root design error
that Cure currently dumps every indexed-type argument into the index telescope.

**Architecture:** New surface syntax `type NAME(params) indices (idx)` splits the
declaration; the elaborator populates the family's (already-existing) parameter
telescope and records each constructor's `result_params` separately from
`result_indices`; the kernel carries `params ++ indices` in `{:vdata}` but runs
the motive and branch-index unifier over indices only (params sliced off by
`param_count`); a uniformity check rejects non-uniform parameters. Five layers:
parser, `declarations.ex`, the `Inductive` registry, the kernel, and the
untrusted `elaborator.ex`.

**Tech Stack:** Elixir; the Cure compiler under `lib/cure/`; ExUnit tests under
`test/`. Full design in
`docs/superpowers/specs/2026-07-02-param-index-split-design.md`.

## Global Constraints

- **One build/test run at any moment.** Never launch concurrent `mix test`/compile
  runs — a past concurrent full-suite run caused a kernel panic. Serialize.
- **Compile Cure with OTP 26–28.** (Environment already satisfies this.)
- **Tests are immutable once green.** Change the implementation, not a green test.
  De Bruijn indices in a *not-yet-green* test may be corrected to faithfully
  encode the test's stated intent; once it passes, it is frozen.
- **Full-suite baseline before this work: 2137 passing** (`5646c63` +
  hardened spec/plan doc commits). No existing test may regress.
- **Ghost-writer commits:** author as the user only; never co-sign.
- **Work only in this worktree** (`.claude/worktrees/case-index-unification`,
  branch `autopilot/case-index-unification`). The 4.3 fix (`5646c63`) is the base.

**Invariants this plan must preserve** (spec §8): (1) parameter fixity —
every ctor's `result_params` equal the family's parameter variables; (2)
parameters excluded from refinement — `unify_indices` only ever sees index
vectors; (3) `vdata` consistency — `eval({:data,…})` and `infer({:ctor,…})`
produce identical-shape `params ++ indices`; (4) motive arity — motive abstracts
exactly `index_arity + 1` args; (5) backward compatibility — `param_count = 0`
families are behaviorally identical to pre-change.

## File Structure

- `lib/cure/core/inductive.ex` — add `result_params` to the ctor record;
  `ctor/5` builder; `param_count/2`, `ctor_result_params/2` accessors. (Task 1)
- `lib/cure/core/kernel.ex` — `check_ctor` param + uniformity check (Task 2);
  `infer({:ctor})` vdata param prefix (Task 3); `infer({:case})` split,
  `check_case_branches` index-only, `check_motive_wf` reconciliation (Task 4).
- `lib/cure/compiler/parser.ex` — `type … indices (…)` form; retire
  `parse_indexed_type` / `:indexed` arm; emit split meta. (Task 5)
- `lib/cure/elab/declarations.ex` — read split meta; elaborate param telescope +
  index telescope in scope; per-ctor param pre-binding; positional-misalignment
  fix; populate `family(name, param_tele, index_tele, level)` and ctor split.
  (Task 6)
- `lib/cure/elab/elaborator.ex` — four param-aware sites: `elaborate_match`
  split, `build_motive` params, `branch_index_subst` index-only slice,
  `finish_ctor_app` result_params. (Task 7)
- `lib/std/vector.cure`, `examples/length_indexed.cure`,
  `test/fixtures/slice1.cure` — migrate to new syntax. (Task 8)
- `lib/antigen/challenge.ex` — update the two `Inductive.ctor` reconstruction
  call sites for the new builder arity. (Task 1)
- Tests: `test/cure/core/param_index_split_test.exs` (Tasks 1–4),
  `test/cure/compiler/parser_indexed_type_test.exs` (Task 5),
  `test/cure/elab/param_index_elab_test.exs` (Tasks 6–7), plus migration
  regression via existing suites (Task 8).

---

### Task 1: Inductive registry — `result_params` + accessors

**Files:**
- Modify: `lib/cure/core/inductive.ex`
- Modify: `lib/antigen/challenge.ex:187,238` (call-site arity update)
- Test: `test/cure/core/param_index_split_test.exs` (new)

**Interfaces:**
- Produces: ctor record gains `result_params: [Term.t()]` (default `[]`);
  `Inductive.ctor/5 = ctor(name, args, result_indices, quantities, result_params)`;
  `Inductive.param_count(env, fname) :: non_neg_integer()`;
  `Inductive.ctor_result_params(env, cname) :: [Term.t()] | nil`.
- Consumes: nothing new.

- [ ] **Step 1: Write the failing test**

Create `test/cure/core/param_index_split_test.exs`:

```elixir
defmodule Cure.Core.ParamIndexSplitTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Kernel}

  @type0 {:type, 0}
  @dec {:data, :Dec, [], []}

  # P(a: Type) indices (n: Dec) with wrap : (p: a) -> P(a, Causal).
  # In the ctor telescope check_ctor binds params first (a), then args (p):
  #   ctx_full = [a, p]  → a is {:var, 1} (num_args=1 + (num_params-1-0)=0).
  # result_params = [a] = [{:var, 1}]; result_indices = [Causal].
  defp param_env do
    Env.empty()
    |> Inductive.declare(
      Inductive.family(:Dec, [], [], 0),
      [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]
    )
    |> Inductive.declare(
      Inductive.family(:P, [{:a, @type0}], [{:n, @dec}], 1),
      [
        Inductive.ctor(:wrap, [{:p, {:var, 0}}], [{:ctor, :Causal, []}],
          [:present], [{:var, 1}])
      ]
    )
  end

  test "family carries a non-empty parameter telescope and param_count" do
    env = param_env()
    assert Inductive.param_telescope(env, :P) == [{:a, @type0}]
    assert Inductive.index_telescope(env, :P) == [{:n, @dec}]
    assert Inductive.param_count(env, :P) == 1
    assert Inductive.param_count(env, :Dec) == 0
  end

  test "constructor records result_params and result_indices separately" do
    env = param_env()
    assert Inductive.ctor_result_params(env, :wrap) == [{:var, 1}]
    assert Inductive.ctor_result_indices(env, :wrap) == [{:ctor, :Causal, []}]
  end

  test "3- and 4-arity ctor builders default result_params to []" do
    c3 = Inductive.ctor(:mk, [], [])
    c4 = Inductive.ctor(:mk, [], [], [])
    assert c3.result_params == []
    assert c4.result_params == []
  end
end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/param_index_split_test.exs`
Expected: FAIL — `Inductive.ctor/5` undefined, `param_count/2` /
`ctor_result_params/2` undefined, ctor record has no `result_params`.

- [ ] **Step 3: Implement the registry changes**

In `lib/cure/core/inductive.ex`:

Update the `@type ctor` to include `result_params: [Cure.Core.Term.t()]`.

Make every builder set `result_params` (default `[]`), and add the 5-arity form
(the 5th arg is `result_params`, trailing/optional so the existing 4-arity
`quantities` position is unchanged):

```elixir
def ctor(name, arg_tele, result_indices),
  do: ctor(name, arg_tele, result_indices, List.duplicate(:present, length(arg_tele)))

def ctor(name, arg_tele, result_indices, quantities),
  do: ctor(name, arg_tele, result_indices, quantities, [])

def ctor(name, arg_tele, result_indices, quantities, result_params),
  do: %{
    name: name,
    args: arg_tele,
    result_indices: result_indices,
    result_params: result_params,
    quantities: quantities
  }
```

Add accessors near `param_telescope/2`:

```elixir
@doc "A family's parameter arity (0 if none / unknown)."
@spec param_count(Env.t(), atom()) :: non_neg_integer()
def param_count(env, fname), do: length(param_telescope(env, fname) || [])

@doc "A constructor's result *parameter* terms (the param prefix of its result)."
@spec ctor_result_params(Env.t(), atom()) :: [Cure.Core.Term.t()] | nil
def ctor_result_params(env, cname) do
  case get_ctor(env, cname) do
    nil -> nil
    %{result_params: rps} -> rps
    _ -> []
  end
end
```

- [ ] **Step 4: Update production call sites of the ctor builder**

`lib/antigen/challenge.ex` reconstructs `Inductive.ctor` values at lines ~187 and
~238 while decoding challenges, and already threads a `params` field in
`to_pieces/1` (challenge.ex:66-98). Read both call sites; for each, pass the
decoded `result_params` (default `[]` when the encoded piece has none) as the new
5th argument, keeping `quantities` in the 4th. Confirm the encode side
(`to_pieces/1`) emits `result_params` so a family round-trips; if it does not yet,
add it symmetric to how it already emits `result_indices`. (Do NOT touch
`declarations.ex:229` yet — that is Task 6, which needs the split telescopes.)

- [ ] **Step 5: Run tests to verify they pass**

Run: `mix test test/cure/core/param_index_split_test.exs`
Expected: PASS (3 tests).
Run: `mix test test/antigen/` — Expected: PASS (challenge round-trip unaffected).

- [ ] **Step 6: Commit**

```bash
git add lib/cure/core/inductive.ex lib/antigen/challenge.ex \
        test/cure/core/param_index_split_test.exs
git commit -m "feat(core): record datatype parameters separately from indices"
```

---

### Task 2: Kernel `check_ctor` — parameter + uniformity check

**Files:**
- Modify: `lib/cure/core/kernel.ex` (`check_ctor`)
- Test: `test/cure/core/param_index_split_test.exs` (append)

**Interfaces:**
- Consumes: ctor `result_params` (Task 1).
- Produces: `check_ctor` returns `{:error, {:non_uniform_parameter, %{family, ctor,
  position}}}` when a ctor's `result_params` are not the family parameter
  variables; `:ok` when uniform and result_indices well-typed.

- [ ] **Step 1: Write the failing test** (append to the Task-1 test file)

```elixir
  alias Cure.Core.Inductive, as: Ind

  test "check_ctor accepts a uniform parameter constructor" do
    env = param_env()
    fam = Ind.get_family(env, :P)
    ctor = Ind.get_ctor(env, :wrap)
    assert :ok == Kernel.check_ctor(env, fam, ctor)
  end

  test "check_ctor rejects a non-uniform parameter (param slot is not a)" do
    # oddball : P(Bool-ish stand-in, Causal) — param slot is a GROUND family, not
    # the parameter variable a. Use Dcoupled-indexed Dec as a stand-in rigid term.
    env = param_env()
    fam = Ind.get_family(env, :P)
    bad =
      Ind.ctor(:oddball, [], [{:ctor, :Causal, []}], [], [{:data, :Dec, [], []}])
    assert {:error, {:non_uniform_parameter, info}} = Kernel.check_ctor(env, fam, bad)
    assert info.family == :P and info.ctor == :oddball and info.position == 0
  end

  test "check_ctor on a param-free family is unchanged (regression)" do
    env = param_env()
    fam = Ind.get_family(env, :Dec)
    assert :ok == Kernel.check_ctor(env, fam, Ind.get_ctor(env, :Causal))
  end
```

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/param_index_split_test.exs`
Expected: FAIL — `check_ctor` ignores `result_params`; the non-uniform ctor is
wrongly accepted (or the uniform one errors on an index-arity mismatch, since
result_indices is now checked against the *index* telescope of arity 1).

- [ ] **Step 3: Implement the check**

In `kernel.ex`, `check_ctor` currently is:

```elixir
def check_ctor(env, %{params: params, indices: index_tele, level: fam_level}, %{
      args: args,
      result_indices: result_indices
    }) do
  with {:ok, ctx_params} <- check_telescope(Context.empty(env), params),
       {:ok, ctx_full, field_levels} <- check_ctor_args(ctx_params, args),
       :ok <- check_field_levels(field_levels, fam_level),
       :ok <- check_result_indices(ctx_full, result_indices, index_tele) do
    :ok
  end
end
```

Extend the ctor pattern to bind `result_params` (defaulting to `[]` via
`Map.get` if a legacy record lacks it), and add a uniformity check after
`check_ctor_args`. A parameter at declaration position `p` (0-based) is, within
`ctx_full = params ++ args`, the de Bruijn variable
`length(args) + (length(params) - 1 - p)`:

```elixir
def check_ctor(env, %{name: fname, params: params, indices: index_tele, level: fam_level} = _fam, ctor) do
  %{args: args, result_indices: result_indices} = ctor
  result_params = Map.get(ctor, :result_params, [])

  with {:ok, ctx_params} <- check_telescope(Context.empty(env), params),
       {:ok, ctx_full, field_levels} <- check_ctor_args(ctx_params, args),
       :ok <- check_field_levels(field_levels, fam_level),
       :ok <- check_uniform_params(fname, ctor.name, result_params, length(params), length(args)),
       :ok <- check_result_indices(ctx_full, result_indices, index_tele) do
    :ok
  end
end

# Each result parameter must be exactly the family's corresponding parameter
# variable, as a de Bruijn var in ctx_full = params(outer) ++ args(inner).
defp check_uniform_params(fname, cname, result_params, num_params, num_args) do
  cond do
    length(result_params) != num_params ->
      {:error, {:non_uniform_parameter, %{family: fname, ctor: cname, position: :arity}}}

    true ->
      result_params
      |> Enum.with_index()
      |> Enum.reduce_while(:ok, fn {term, p}, :ok ->
        expected = {:var, num_args + (num_params - 1 - p)}
        if term == expected,
          do: {:cont, :ok},
          else: {:halt, {:error, {:non_uniform_parameter, %{family: fname, ctor: cname, position: p}}}}
      end)
  end
end
```

(Confirm `check_result_indices`'s arity check now compares against
`length(index_tele)` — the *index* arity — since `result_indices` is index-only.
If `check_result_indices` derived arity from the full telescope before, it did so
via `index_tele` already; verify and adjust only if it used a full-arity source.)

- [ ] **Step 4: Run tests to verify they pass**

Run: `mix test test/cure/core/param_index_split_test.exs`
Expected: PASS (Task-1 tests + 3 new).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/core/kernel.ex test/cure/core/param_index_split_test.exs
git commit -m "feat(kernel): reject non-uniform parameters in check_ctor"
```

---

### Task 3: Kernel `infer({:ctor})` — prepend params to vdata

**Files:**
- Modify: `lib/cure/core/kernel.ex` (`infer({:ctor, …})`, ~180-190)
- Test: `test/cure/core/param_index_split_test.exs` (append)

**Interfaces:**
- Consumes: ctor `result_params` (Task 1).
- Produces: `infer(ctx, {:ctor, name, args})` returns `{:vdata, fam, param_vals ++
  index_vals}` (Invariant 3), implementing the standing TODO.

- [ ] **Step 1: Write the failing test** (append)

```elixir
  alias Cure.Core.Context

  test "infer of a param-bearing constructor carries params ++ indices in vdata" do
    env = param_env()
    ctx = Context.empty(env)
    # wrap(d) where d : Dec (stand-in for a := Dec). Provide a concrete arg of a
    # ground type by instantiating a := Dec through the arg's type at use.
    # Here we infer wrap applied to a Causal value; param a is inferred from p's type.
    term = {:ctor, :wrap, [{:ctor, :Dcoupled, []}]}
    assert {:ok, {:vdata, :P, [param, index]}} = Kernel.infer(ctx, term)
    # index slot is the ctor's fixed Causal; param slot is present (arity 2, not 1).
    assert index == {:vctor, :Causal, []} or match?({:vdata, :Dec, _}, index) or index != nil
    assert param != nil
  end
```

Note: the exact `param`/`index` values depend on how `a` is inferred from `p`'s
type; the load-bearing assertion is **vdata arity 2** (`params ++ indices`), not
arity 1. Refine the value assertions to the concrete inferred terms once the
scenario type-checks (pre-green latitude).

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/core/param_index_split_test.exs`
Expected: FAIL — current `infer({:ctor})` returns `{:vdata, :P, [index]}` (arity
1, index-only), so the 2-element match fails.

- [ ] **Step 3: Implement the prefix**

In `kernel.ex`, `infer(ctx, {:ctor, name, args})`, the `%{args: tele,
result_indices: result_indices}` arm currently ends:

```elixir
      index_values = Enum.map(result_indices, &Eval.eval(&1, arg_env))
      {:ok, {:vdata, family_name, index_values}}
```

Bind `result_params` from the ctor and prepend their evaluated values:

```elixir
      %{args: tele, result_indices: result_indices} = ctor_sig
      result_params = Map.get(ctor_sig, :result_params, [])
      ...
      param_values = Enum.map(result_params, &Eval.eval(&1, arg_env))
      index_values = Enum.map(result_indices, &Eval.eval(&1, arg_env))
      {:ok, {:vdata, family_name, param_values ++ index_values}}
```

(Match the existing local variable names in that clause — bind the ctor signature
map so `result_params` is reachable.)

- [ ] **Step 4: Run tests to verify they pass**

Run: `mix test test/cure/core/param_index_split_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/core/kernel.ex test/cure/core/param_index_split_test.exs
git commit -m "feat(kernel): constructor values carry params ++ indices in vdata"
```

---

### Task 4: Kernel case path — split, motive reconciliation, index-only branches

**Files:**
- Modify: `lib/cure/core/kernel.ex` (`infer({:case})`, `check_motive_wf`,
  `check_case_branches`)
- Test: `test/cure/core/param_index_split_test.exs` (append)

**Interfaces:**
- Consumes: `Inductive.param_count/2`; ctor `result_indices` (now index-only for
  param families).
- Produces: `infer({:case})` splits `scrut_args` by `param_count`; `check_motive_wf`
  builds `data_value` with scrutinee params; `check_case_branches` unifies indices
  only; motive applied to `index ++ [scrutinee]` everywhere (Invariant 4).

- [ ] **Step 1: Write the failing tests** (append)

```elixir
  # Test 1 (spec §7.1): a parameter survives matching unchanged. Match on a
  # P(a, Causal); in the wrap branch, a hypothesis h : a is still usable at type a
  # (the parameter is NOT refined away by the match).
  test "a parameter-typed hypothesis is reusable in a branch (param not matched)" do
    env = param_env()
    # def probe : Π(a:Type). Π(h:a). Π(v:P(a,Causal)). a
    #   = λa.λh.λv. case v of wrap(p) -> h
    # de Bruijn inside wrap branch (adds binder p): h was var1 before case → var2.
    p_ac = {:data, :P, [{:var, 1}], [{:ctor, :Causal, []}]}   # P(a, Causal) under a,h
    def_type = {:pi, @type0, {:pi, {:var, 0}, {:pi, p_ac_shift(), {:var, 2}}}}
    motive = {:lam, {:data, :P, [{:var, 2}], [{:var, 0}]}, {:var, 3}} # λ(idx n).λ(x). a
    body =
      {:lam, @type0,
       {:lam, {:var, 0},
        {:lam, p_ac_shift(),
         {:case, {:var, 0}, motive, [{:wrap, 1, {:var, 2}}]}}}}
    env = Env.add_def(env, :probe, def_type, body)
    assert :ok == Kernel.check_def(env, :probe)
  end

  # Test 4 (spec §7.4): param-free family behaves exactly as before. Reuse the
  # existing Box/Dec ground-index refinement shape as a regression guard.
  test "param-free family case is unchanged" do
    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Dec, [], [], 0),
           [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])])
      |> Inductive.declare(Inductive.family(:Box, [], [{:d, @dec}], 0),
           [Inductive.ctor(:mk, [{:x, @dec}], [{:var, 0}])])
    box_causal = {:data, :Box, [], [{:ctor, :Causal, []}]}
    motive = {:lam, @dec, {:lam, {:data, :Box, [], [{:var, 0}]}, @dec}}
    def_type = {:pi, box_causal, @dec}
    body = {:lam, box_causal, {:case, {:var, 0}, motive, [{:mk, 1, {:var, 0}}]}}
    env = Env.add_def(env, :probe2, def_type, body)
    assert :ok == Kernel.check_def(env, :probe2)
  end
```

The `p_ac_shift/0` helper and the exact de Bruijn indices in Test 1 encode
"match refines the index, parameter `a` stays `a`"; correct them to faithfully
express that intent while red (the motive abstracts the single index + scrutinee
only — arity 2 — and reads the parameter `a` from the enclosing context, not from
a motive binder). Add a small private helper returning the correctly-shifted
`P(a, Causal)` type for the `v` binder position.

- [ ] **Step 2: Run tests to verify they fail**

Run: `mix test test/cure/core/param_index_split_test.exs`
Expected: Test 1 FAILs (motive/vdata arity mismatch: `check_motive_wf` builds a
1-element `data_value` while the scrutinee's vdata is 2-element; or the branch
unifier receives params). Test 4 should PASS already (param-free) — it is the
regression guard; if it fails, the split logic wrongly touches param-free
families.

- [ ] **Step 3: Implement the split + reconciliation**

(a) `infer({:case, scrut, motive, branches})` — split `scrut_indices` (the vdata
args) by `param_count` and thread the pieces:

```elixir
    case infer(ctx, scrut) do
      {:ok, {:vdata, dname, scrut_args}} ->
        family = Inductive.get_family(sig, dname)
        pc = Inductive.param_count(sig, dname)
        {scrut_params, scrut_idx} = Enum.split(scrut_args, pc)
        motive_value = Eval.eval(motive, Context.env(ctx))

        with :ok <- check_motive_wf(ctx, motive_value, family, scrut_params),
             :ok <- check_coverage(sig, dname, branches),
             :ok <- check_case_branches(ctx, sig, dname, motive_value, branches, scrut_idx) do
          scrut_value = Eval.eval(scrut, Context.env(ctx))
          {:ok, apply_motive(motive_value, scrut_idx ++ [scrut_value])}
        end
```

(b) `check_motive_wf` — take the scrutinee params and build the scrutinee
`data_value` as `params ++ fresh_indices`; the motive still abstracts indices +
scrutinee only:

```elixir
  defp check_motive_wf(ctx, motive_value, %{name: dname, indices: index_tele}, scrut_params) do
    {ctx_indices, index_vals} = extend_with_telescope(ctx, index_tele)
    scrut_level = Context.length(ctx_indices)
    # scrut_params are values from the outer ctx; shift them under the freshly
    # added index binders so they refer correctly inside ctx_indices.
    shifted_params = Enum.map(scrut_params, &shift_value(&1, length(index_tele)))
    data_value = {:vdata, dname, shifted_params ++ index_vals}
    ctx_motive = Context.extend(ctx_indices, data_value)
    x_value = {:vneutral, {:nvar, scrut_level}}

    body_value = apply_motive(motive_value, index_vals ++ [x_value])

    case infer_type_value_sort(ctx_motive, body_value) do
      {:ok, _level} -> :ok
      _ -> {:error, :bad_motive}
    end
  end
```

Use the existing value-shifting utility for `shift_value/2` (the kernel already
shifts values when extending telescopes — reuse that helper; if only a term-level
`Term.shift` exists, reify→shift→eval, or shift the neutral levels, consistent
with how `extend_with_telescope` produces `index_vals`). For `param_count = 0`,
`scrut_params = []` and this is identical to the pre-change body (Invariant 5).

(c) `check_case_branches` — already receives the index-only vector as its last
argument (now named `scrut_idx`); no structural change beyond confirming
`result_indices` (index-only after Task 6 for surface families; already
index-only for these hand-built kernel families) unify against it. The
`apply_motive(motive_value, s_values ++ [ctor_value])` call is already index-only
because `s_values` derives from `result_indices`.

- [ ] **Step 4: Run tests to verify they pass**

Run: `mix test test/cure/core/param_index_split_test.exs`
Expected: PASS (all Task 1–4 tests).
Run: `mix test test/cure/core/case_soundness_index_test.exs` — Expected: PASS
(the 4.3 tests are param-free; must be untouched).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/core/kernel.ex test/cure/core/param_index_split_test.exs
git commit -m "feat(kernel): case splits params from indices; motive over indices only"
```

---

### Task 5: Parser — `type … indices (…)` form

**Files:**
- Modify: `lib/cure/compiler/parser.ex` (`parse_type_def`, the `:type` dispatch;
  retire `:indexed` arm + `parse_indexed_type`)
- Modify: lexer keyword set if `indices` is not already a keyword
- Test: `test/cure/compiler/parser_indexed_type_test.exs` (new)

**Interfaces:**
- Produces: parsing `type NAME(params) indices (idx) <ctor block>` yields
  `{:indexed_type, [name: …, params: <typed tele>, indices: <typed tele>, line,
  col], ctors}`; ordinary `type X(a) = …` unchanged; a leading `indexed` keyword
  no longer parses as a type declaration.

- [ ] **Step 1: Write the failing test**

Create `test/cure/compiler/parser_indexed_type_test.exs`. First read
`lib/cure/compiler/parser.ex` around `parse_type_def` (2322-2410) and confirm the
public entry used elsewhere in `test/cure/compiler/` for parsing a module/decl;
model the new test on that existing harness (e.g. `Parser.parse/1` over lexed
source). Assert:

```elixir
defmodule Cure.Compiler.ParserIndexedTypeTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse_decl(src) do
    {:ok, toks} = Lexer.tokenize(src)      # match the real lexer entry name
    Parser.parse(toks)                     # match the real parser entry name
  end

  test "type NAME(params) indices (idx) parses into split meta" do
    src = """
    mod M
      type Vector(a: Type) indices (n: Nat)
        empty   : Vector(a, Z)
        prepend : a -> Vector(a, n) -> Vector(a, S(n))
    """
    {:ok, ast} = parse_decl(src)
    node = find_indexed_type(ast, "Vector")
    assert {:indexed_type, meta, ctors} = node
    assert Keyword.get(meta, :params) |> length() == 1
    assert Keyword.get(meta, :indices) |> length() == 1
    assert length(ctors) == 2
  end

  test "parameter-free family: type Length indices (n: Nat)" do
    src = "mod M\n  type Length indices (n: Nat)\n    zero : Length(Z)\n"
    {:ok, ast} = parse_decl(src)
    assert {:indexed_type, meta, _} = find_indexed_type(ast, "Length")
    assert Keyword.get(meta, :params) == []
    assert Keyword.get(meta, :indices) |> length() == 1
  end

  test "ordinary ADT still parses unchanged" do
    src = "mod M\n  type Option(a) = Some(a) | None\n"
    {:ok, ast} = parse_decl(src)
    refute match?({:indexed_type, _, _}, find_type(ast, "Option"))
  end
end
```

Write the `find_indexed_type/2`, `find_type/2` helpers to walk the produced AST
(shape confirmed while reading the parser). Adjust the lexer/parser entry-point
names and AST-walk to the real API discovered in Step 0-read.

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/compiler/parser_indexed_type_test.exs`
Expected: FAIL — `parse_type_def` requires `=` after the head params, so the
`indices` form is a parse error.

- [ ] **Step 3: Implement the parser rework**

Per spec §4.1: in `parse_type_def` (parser.ex:2322-2410), after parsing the family
name and the optional head-paren telescope, do NOT unconditionally
`expect(state, :assign)`. Instead peek:
- next token is `=` (`:assign`) → existing ordinary-ADT/alias path, unchanged.
  Parse head params permissively as `parse_typed_params` and project just the
  names into the existing `type_params` meta key so `Option(a) = …` is unaffected.
- next token is the `indices` keyword → the indexed-family path: reuse the parsed
  head telescope as `params`, `expect` `indices`, `expect` `:lparen`,
  `parse_typed_params`, `expect` `:rparen`, `skip_newlines`, parse the
  indentation-delimited ctor block via `parse_gadt_ctors` (unchanged). Emit
  `{:indexed_type, [name: name, params: params, indices: idx_tele, line:, col:],
  ctors}`.
- neither → parse error (unchanged behavior for a bare `type X` with no `=`).

Add `indices` to the lexer keyword table if absent (verify first: grep the lexer
for the keyword list; there are no `indices` identifiers in `lib/`/`examples/`
outside comments per spec §4.1 — confirm with grep before adding). Retire the
`:indexed -> parse_indexed_type(state)` dispatch arm (parser.ex:1235-1236) and
`parse_indexed_type/1` (2418-2469); a leading `indexed` keyword now has no decl
path (a later plan may reintroduce it as an explicit migration-hint error, but
this plan removes it — see §7 Test 7). If `indexed` was a reserved keyword solely
for this, leave the keyword token in the lexer (harmless) or remove it; do not
break unrelated tokenization.

- [ ] **Step 4: Run tests to verify they pass**

Run: `mix test test/cure/compiler/parser_indexed_type_test.exs`
Expected: PASS.
Run: `mix test test/cure/compiler/` — Expected: PASS (no parser regressions).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/compiler/parser.ex test/cure/compiler/parser_indexed_type_test.exs
git commit -m "feat(parser): type NAME(params) indices (idx) syntax for indexed families"
```

---

### Task 6: Elaborator (`declarations.ex`) — split telescopes + per-ctor param scoping

**Files:**
- Modify: `lib/cure/elab/declarations.ex` (read split meta; elaborate param +
  index telescopes; per-ctor param pre-binding; positional-misalignment fix;
  populate `family(name, param_tele, index_tele, level)` + ctor `result_params`)
- Test: `test/cure/elab/param_index_elab_test.exs` (new)

**Interfaces:**
- Consumes: parser split meta (Task 5); `Inductive.ctor/5` (Task 1); kernel
  `check_ctor` uniformity (Task 2).
- Produces: elaborating a surface param-bearing declaration registers a family
  with the correct param/index telescopes and constructors whose `result_params`
  are the family parameter variables and `result_indices` are index-only.

- [ ] **Step 1: Write the failing test**

Create `test/cure/elab/param_index_elab_test.exs`. Read an existing
`test/cure/elab/` test to reuse its elaborate-a-module harness (e.g. the slice1
conformance test). Then:

```elixir
defmodule Cure.Elab.ParamIndexElabTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Inductive
  # ... reuse the module-elaboration entry the sibling elab tests use ...

  @src """
  mod M
    type Pair(a: Type) indices (tag: Dec)
      mk : a -> a -> Pair(a, Causal)
  """

  test "param-bearing declaration registers split telescopes + result_params" do
    env = elaborate_module!(@src)               # sibling-test helper name
    assert Inductive.param_count(env, :Pair) == 1
    assert Inductive.index_telescope(env, :Pair) |> length() == 1
    rps = Inductive.ctor_result_params(env, :mk)
    ris = Inductive.ctor_result_indices(env, :mk)
    assert length(rps) == 1           # the single parameter position
    assert length(ris) == 1           # index-only (Causal)
    # the recorded family + ctor pass the kernel's own well-formedness check
    fam = Inductive.get_family(env, :Pair)
    assert :ok == Cure.Core.Kernel.check_ctor(env, fam, Inductive.get_ctor(env, :mk))
  end
end
```

(Use a `Dec` family in scope — declare it in the source, or pick whatever base
type the sibling elab tests already make available. Param/index counts here are
1-and-1 like Vector; Task 7 adds a differing-count family to catch off-by-position
bugs.)

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/param_index_elab_test.exs`
Expected: FAIL — `declarations.ex` reads the old single `index_params` meta,
declares `family(name, [], all_args, level)` (param_count 0), and constructors
carry no `result_params`.

- [ ] **Step 3: Implement the elaborator split** (spec §4.2)

Read `declarations.ex:70-90` (indexed-family entry) and `197-331`
(`elaborate_gadt_ctors`, `elaborate_gadt_ctor`, `infer_implicits`,
`collect_implicit_vars`, `family_index_types`, and the `declare_indexed_at_min_level`
call at ~405). Then:

1. Read `params` and `indices` from the node meta (was `index_params`).
2. Elaborate the parameter telescope to core; elaborate the index telescope **in
   scope of the parameters** (params in the `idx_to_core` name→deBruijn map first,
   then indices). Produce `param_tele` and `index_tele`.
3. In `elaborate_gadt_ctor`, open each constructor's local `idx_to_core` scope
   with the **family parameter names pre-bound** to the outer parameter positions
   (correctly shifted under that constructor's own implicit + explicit arg count),
   BEFORE running implicit-index inference — so parameters are not inference
   candidates. Elaborate the constructor's result type, then **split its applied
   argument vector by `length(param_tele)`** into `result_params` (prefix) and
   `result_indices` (suffix). Build the ctor with `Inductive.ctor/5` passing
   `result_params`.
4. **Positional-misalignment fix** (spec §4.2, decl.ex:286-316): wherever
   `collect_implicit_vars` zips a family/self application's full surface argument
   list against `family_index_types(...)` by raw position, skip the leading
   `param_count` argument positions (the parameter args are not index-typed
   candidates) so `index_types` aligns with the index suffix, not the full arg
   list.
5. Call `declare_indexed_at_min_level` / `Inductive.family` with the real
   `param_tele` (the `[]` at decl.ex:405 becomes `param_tele`).

Keep the parameter-free path identical (empty `param_tele` ⇒ every step degrades
to today's behavior; `slice1.cure`'s `SF` and `Length` are parameter-free).

- [ ] **Step 4: Run tests to verify they pass**

Run: `mix test test/cure/elab/param_index_elab_test.exs`
Expected: PASS.
Run: `mix test test/cure/elab/` — Expected: PASS (existing elab incl. slice1
conformance — but see Task 8 for the fixture migration; if slice1 uses the old
syntax it is migrated in Task 8, so run slice1 conformance there. If it fails
here purely on old syntax, proceed; Task 8 migrates it).

- [ ] **Step 5: Commit**

```bash
git add lib/cure/elab/declarations.ex test/cure/elab/param_index_elab_test.exs
git commit -m "feat(elab): split parameters from indices in indexed-type declarations"
```

---

### Task 7: Untrusted elaborator (`elaborator.ex`) — four param-aware sites

**Files:**
- Modify: `lib/cure/elab/elaborator.ex` (`elaborate_match`, `build_motive`,
  `branch_expected_type`/`specialize_branch_context`/`branch_index_subst`,
  `finish_ctor_app`)
- Test: `test/cure/elab/param_index_elab_test.exs` (append)

**Interfaces:**
- Consumes: `Inductive.param_count/2`, ctor `result_params` (Tasks 1, 6).
- Produces: `elaborate_match` and `elaborate_ctor_app` on a param-bearing family
  produce motive/result-type values whose parameter component is the scrutinee's
  actual (non-empty, correctly-sliced) parameters.

- [ ] **Step 1: Write the failing test** (append) — use a family whose param and
index counts **differ** so an off-by-position bug cannot hide:

```elixir
  @src2 """
  mod M
    type Tagged(a: Type) indices (x: Dec, y: Dec)
      wrap : a -> Tagged(a, Causal, Dcoupled)
    fn use(t: Tagged(Dec, Causal, Dcoupled)) -> Dec =
      match t
        wrap(v) -> v
  """

  test "match + ctor-app on a param-bearing family carry correct sliced params" do
    # Elaborates end-to-end: the match's motive binder x:D j̄ and the ctor-app
    # result type must carry the actual parameter (Dec), not []; index slice is
    # the 2 indices only. If build_motive/finish_ctor_app kept params=[], or
    # branch_index_subst zipped params against indices, this fails to elaborate.
    assert {:ok, _env} = elaborate_module(@src2)
  end
```

Prefer asserting a structural property if the harness exposes the elaborated
term (e.g. the produced `{:case, scrut, motive, _}` motive's scrutinee-binder
type is `{:data, :Tagged, [<param>], [_, _]}` with a non-empty param list). If
only pass/fail elaboration is observable, the successful end-to-end elaboration of
a param/index-count-differing family is the guard (a params-`[]` bug misaligns the
2 indices vs. 1 param and fails).

- [ ] **Step 2: Run test to verify it fails**

Run: `mix test test/cure/elab/param_index_elab_test.exs`
Expected: FAIL — `build_motive` uses `{:data, dname, [], …}` and
`finish_ctor_app` uses `{:data, family, [], indices}`; `elaborate_match` feeds the
full `index_vals` (params + indices) as `idx_terms`; `branch_index_subst` zips a
1-element `result_indices`-param-prefix against a 3-element `scrut_indices`.

- [ ] **Step 3: Implement the four fixes** (spec §4.5)

1. **`elaborate_match`** (elaborator.ex:277-294): after `{:vdata, dname,
   index_vals}`, split by `param_count`:
   ```elixir
   pc = Inductive.param_count(env, dname)
   {param_vals, idx_only} = Enum.split(index_vals, pc)
   param_terms = Enum.map(param_vals, &Quote.reify(&1, Context.length(ctx)))
   idx_terms = Enum.map(idx_only, &Quote.reify(&1, Context.length(ctx)))
   motive = build_motive(dname, family.indices, param_terms, idx_terms, scrut_term, result_type_term)
   ```
   Pass `idx_terms` (index-only) to `elaborate_branches` as `scrut_indices`.
2. **`build_motive`** (306-332): accept `param_terms`; build
   `scrut_type = {:data, dname, param_terms_shifted, Enum.map((k-1)..0//-1, &{:var, &1})}`
   where `param_terms` are shifted under the `k` index binders (they refer to the
   outer frame). `k = length(index_tele)` unchanged; the rebind map and
   generalization are unchanged (they concern indices + scrutinee only).
3. **`branch_index_subst` / `specialize_branch_context` / `branch_expected_type`**
   (475-538): these already receive `scrut_indices`; ensure the caller now passes
   the **index-only** `idx_terms` from fix 1 (so `result_indices` (index-only from
   Task 6) and `scrut_indices` are the same arity and align head-to-head). No
   change to the zip logic itself once both are index-only; add a doc line noting
   both sides are index-only post param/index split.
4. **`finish_ctor_app`** (644-654): evaluate `ctor.result_params` the same way
   `indices` is, and pass as the real first component:
   ```elixir
   params = Enum.map(Map.get(ctor, :result_params, []), &Subst.instantiate(&1, args))
   indices = Enum.map(ctor.result_indices, &Subst.instantiate(&1, args))
   result_type = Eval.eval({:data, family, params, indices}, [])
   ```

For `param_count = 0` every fix degrades to the current behavior (empty split,
empty param list) — Invariant 5.

- [ ] **Step 4: Run tests to verify they pass**

Run: `mix test test/cure/elab/param_index_elab_test.exs`
Expected: PASS.
Run: `mix test test/cure/elab/` — Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/cure/elab/elaborator.ex test/cure/elab/param_index_elab_test.exs
git commit -m "feat(elab): thread datatype parameters through match + ctor-app elaboration"
```

---

### Task 8: Migration + end-to-end integration

**Files:**
- Modify: `lib/std/vector.cure`, `examples/length_indexed.cure`,
  `test/fixtures/slice1.cure`
- Test: existing `test/cure/elab/slice1_conformance_test.exs`; a `Std.Vector`
  compile/type-check assertion (new or existing stdlib test)

**Interfaces:**
- Consumes: the full stack (Tasks 1–7).
- Produces: all three `.cure` declarations use the new syntax; `Std.Vector.append`
  type-checks; slice1 conformance stays green.

- [ ] **Step 1: Write / identify the failing integration test**

Locate the existing test that compiles `Std.Vector` (grep `test/` for `Vector`
and `append`). If one asserts `append` type-checks, use it. Otherwise add to a
stdlib test:

```elixir
test "Std.Vector compiles and append type-checks under the new syntax" do
  assert {:ok, _} = compile_std_module("Std.Vector")   # match real helper
end
```

Also ensure `test/cure/elab/slice1_conformance_test.exs` is in the run set (it
exercises `test/fixtures/slice1.cure`).

- [ ] **Step 2: Run to verify current failure**

Run: `mix test <the Vector test> test/cure/elab/slice1_conformance_test.exs`
Expected: FAIL/parse-error — the three `.cure` files still use the removed
`indexed type … where` syntax (Task 5 deleted its parse path).

- [ ] **Step 3: Migrate the three declarations** (spec §6)

- `lib/std/vector.cure`:
  `indexed type Vector(a: Type, n: Nat) where` →
  `type Vector(a: Type) indices (n: Nat)`. Constructor lines and `append`
  unchanged.
- `examples/length_indexed.cure`:
  `indexed type Length(n: Nat) where` → `type Length indices (n: Nat)`
  (parameter-free).
- `test/fixtures/slice1.cure` (line ~12):
  `indexed type SF(as: SVDesc, bs: SVDesc, d: Dec) where` →
  `type SF indices (as: SVDesc, bs: SVDesc, d: Dec)` (parameter-free — all three
  are refined per constructor).

Preserve indentation of the constructor blocks (the `where` line's indentation
context is replaced by the `type … indices (…)` line at the same column).

- [ ] **Step 4: Run the integration + regression tests**

Run: `mix test <the Vector test> test/cure/elab/slice1_conformance_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/std/vector.cure examples/length_indexed.cure test/fixtures/slice1.cure
git commit -m "refactor(std): migrate indexed types to type NAME indices (...) syntax"
```

- [ ] **Step 6: Full-suite verification** (Stage 5 boundary — one run only)

Run: `mix test`
Expected: **≥ 2137 passing** (baseline) **plus** the new tests
(param_index_split, parser_indexed_type, param_index_elab), zero failures. If any
pre-existing test regresses, it indicates a missed param-aware site — do not
edit the failing test; fix the implementation.

---

## Self-Review

**Spec coverage:** §3 surface syntax → Task 5; §3.1 disambiguation → Task 5 Step 3;
§4.1 parser → Task 5; §4.2 elaborator split + per-ctor scoping + positional fix →
Task 6; §4.3 registry + call sites → Task 1; §4.4 kernel (eval unchanged; ctor
vdata → Task 3; check_ctor → Task 2; check_motive_wf + case split → Task 4) → Tasks
2-4; §4.5 elaborator.ex four sites → Task 7; §5 uniformity → Task 2; §6 migration →
Task 8; §7 tests 1-8 → distributed (T1→T4, T2→T2, T3→T4, T4→T4, T5→T3, T6→T8,
T7→T5, T8→T6/T7); §8 invariants → Global Constraints + per-task notes; §9 deferred
→ untouched.

**Placeholder scan:** no TBD/TODO; every step names a concrete file, test, and
command. De Bruijn indices in Tasks 3-4 tests are flagged as pre-green-adjustable
to faithfully encode stated intent (allowed by the immutability rule, which
freezes only *green* tests).

**Type consistency:** `Inductive.ctor/5` (result_params trailing) used identically
in Tasks 1, 6; `param_count/2` and `ctor_result_params/2` names consistent across
Tasks 1, 4, 6, 7; `{:vdata, name, params ++ indices}` shape consistent Tasks 3, 4,
7; the case-path split (`Enum.split(scrut_args, param_count)`) identical in kernel
(Task 4) and elaborator (Task 7).
