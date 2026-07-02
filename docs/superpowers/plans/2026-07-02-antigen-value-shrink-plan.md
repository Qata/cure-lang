# Antigen value-level post-shrink — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** When an assay fires, greedily rewrite the reified `Challenge` artifact into a minimal witness before banking it, so antibodies are minimal. The rewriter is purely structural (untyped); a same-violation-shape predicate is the sole validity gate.

**Architecture:** New `Antigen.Shrink` module — `minimize/3` runs a deterministic greedy sweep of single-edit candidates (4 rules), accepting the first that stays well-formed and keeps the predicate true, to a fixpoint or step budget. `Antigen.Runner`'s infection branch builds the predicate (pinning the violation tag via `same_shape?/2`), minimizes, and banks the minimized artifact.

**Tech Stack:** Elixir; `Cure.Core.Term` (`shift/3`, `term?/1`); `Antigen.Coverage`; `Antigen.Challenge`.

## Global Constraints

- **Predicate is the only validity gate (LOCKED):** the rewriter does untyped structural edits; a candidate is accepted iff `well_formed?(k)` (shape check) AND `pred.(k)` (same-shape violation still fires). `pred` crashes are rescued → reject. No per-edit re-typecheck.
- **Same-shape predicate (LOCKED):** `pred` pins the violation **tag** (leading atom of the detail tuple), NOT `{:violation, _}` — else a `:typed_term` shrink can wander into `{:violation, {:infer_failed, _}}` nonsense (spec §2/§6).
- **Determinism/reproducibility (LOCKED):** no clock, no RNG, no map-ordering dependence in `minimize`. Fixed enumeration. Step-budget only.
- **De Bruijn correctness by construction (LOCKED):** `well_formed?` is shape-only (`Term.term?` accepts any `{:var,k}` with `k≥0`), so it does NOT catch out-of-scope vars. Rule 3 (ctx drop) and rule 4's `:lam`/`:case` cases must be index-correct by construction; §7.3 guards against regressions.
- **Ghost-authored commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no `Co-Authored-By`.
- **One full build/test run at a time.**
- **StreamData quarantine:** `Shrink` is outside `generators/`/`assays/` and uses neither backend — unaffected, but keep it free of the literal `StreamData`.

### Confirmed codebase facts (probed)
- `Cure.Core.Term.shift(term, amount, cutoff \\ 0)` — **positional** cutoff; increments cutoff under binders (`:lam`/`:pi`/`:sigma` body → `c+1`; `:case` branch → `c+arity`). `Term.term?/1` is shape-only.
- `Antigen.Coverage.terms_of(challenge)` returns `[type, term | ctx]` — each ctx entry is a **bare type-term** (not `{name, term}`), so drop/shift acts on it directly.
- `Runner.occurs?/2` (`runner.ex:240-256`, private) is the crosses-binders free-occurrence check — reimplement in `Shrink` (don't reach into Runner's privates).
- `Runner.well_formed?/1` (`runner.ex:328-332`, private) = `Coverage.terms_of(c) |> Enum.all?(&Term.term?/1)` rescue false — **reimplement** the same one-liner in `Shrink` to avoid a Runner↔Shrink cycle (spec §8 said "expose if private"; reimplementing via the same primitives is equivalent and cleaner — a deliberate, documented refinement).
- `Runner.explore/1` infection branch is `runner.ex:24-32`; assay dispatch is `apply(opts[:assay] || assay_module(c.assay), :run, [c])`.

---

## File Structure

- **Create** `lib/antigen/shrink.ex` — `minimize/3`, `size/1`, `occurs?/2`, `well_formed?/1`, the rule/candidate generators, `child_slots/1`.
- **Modify** `lib/antigen/runner.ex` — infection branch minimizes before banking; `same_shape?/2`, `@shrink_budget`, `shrink_budget/1`.
- **Create** `test/antigen/shrink_test.exs`.

---

## Task 1: `Shrink` engine + term/type rules (1, 2, 4)

**Files:** Create `lib/antigen/shrink.ex`. Test: create `test/antigen/shrink_test.exs`.

**Interfaces:**
- Produces: `Shrink.minimize(challenge, pred, budget) :: Challenge`; `Shrink.size(challenge) :: non_neg_integer`. Handles rules 1 (subterm→atom), 2 (numeral shrink), 4 (structural unwrap incl. `:lam`/`:case` de Bruijn) over the `type` and `term` fields. Context drop (rule 3) is Task 2.

- [ ] **Step 1: Write the failing tests**
```elixir
defmodule Antigen.ShrinkTest do
  use ExUnit.Case, async: true
  alias Antigen.{Shrink, Challenge}

  # a well-typed-ish artifact whose predicate is purely structural for these unit tests
  defp art(term, ctx \\ []) do
    Challenge.new(kind: :typed_term, assay: "term/infer_check", label: :well_typed,
      payload: %{sig: :v1, ctx: ctx, type: {:data, :Nat, [], []}, term: term})
  end

  defp s(n), do: {:ctor, :S, [n]}
  defp num(0), do: {:ctor, :Z, []}
  defp num(k), do: s(num(k - 1))

  test "numeral shrink + subterm→atom reduces under a 'contains an S' predicate to a single S Z" do
    a = art(s(s(s(num(0)))))                       # S(S(S Z)))
    pred = fn ch -> match?({:ctor, :S, _}, ch.payload.term) end
    out = Shrink.minimize(a, pred, 1000)
    assert out.payload.term == s(num(0))           # minimal term still headed by S
    assert pred.(out)
  end

  test "structural unwrap peels an app/ctor wrapper down to the payload leaf" do
    # plus(vcons(...), Z) — predicate keeps any term still containing a vcons
    inner = {:ctor, :vcons, [num(0), num(0), {:ctor, :vnil, []}]}
    a = art({:app, {:app, {:global, :plus}, inner}, num(0)})
    pred = fn ch -> contains_vcons?(ch.payload.term) end
    out = Shrink.minimize(a, pred, 1000)
    assert out.payload.term == {:ctor, :vnil, []} or match?({:ctor, :vcons, _}, out.payload.term)
    assert Shrink.size(out) < Shrink.size(a)
    assert pred.(out)
  end

  test "lam-body unwrap shifts free vars and is rejected when body uses its own param" do
    keep = fn _ -> true end
    # λx:Nat. (var 1)  — body does NOT use var 0 ⇒ unwrap to (var 0) after shift
    a = art({:lam, {:data, :Nat, [], []}, {:var, 1}}, [{:data, :Nat, [], []}])
    out = Shrink.minimize(a, keep, 1000)
    assert out.payload.term == {:var, 0}           # shifted down by 1
  end

  test "deterministic + monotone + idempotent" do
    a = art(s(s(num(0))))
    pred = fn ch -> match?({:ctor, :S, _}, ch.payload.term) end
    o1 = Shrink.minimize(a, pred, 1000)
    o2 = Shrink.minimize(a, pred, 1000)
    assert o1 == o2
    assert Shrink.size(o1) <= Shrink.size(a)
    assert Shrink.minimize(o1, pred, 1000) == o1   # idempotent
  end

  test "budget bounds the number of accepted edits" do
    a = art(num(5))
    pred = fn _ -> true end                         # everything shrinks
    out = Shrink.minimize(a, pred, 1)
    assert Shrink.size(out) == Shrink.size(a) - 1   # exactly one edit
  end

  defp contains_vcons?({:ctor, :vcons, _}), do: true
  defp contains_vcons?(t) when is_tuple(t), do: t |> Tuple.to_list() |> tl() |> Enum.any?(&contains_vcons?/1)
  defp contains_vcons?(l) when is_list(l), do: Enum.any?(l, &contains_vcons?/1)
  defp contains_vcons?(_), do: false
end
```

- [ ] **Step 2: Run — expect FAIL** `mix test test/antigen/shrink_test.exs` (module undefined).

- [ ] **Step 3: Implement** — create `lib/antigen/shrink.ex`:
```elixir
defmodule Antigen.Shrink do
  @moduledoc """
  Value-level greedy post-shrink. Minimizes a reified `Challenge` artifact under a
  caller-supplied same-violation-shape predicate, via untyped structural rewrites.
  Purely deterministic (fixed enumeration, no RNG/clock); bounded by a step budget.
  """
  alias Antigen.{Challenge, Coverage}
  alias Cure.Core.Term

  @minimal_atoms [{:ctor, :Z, []}, {:ctor, :vnil, []}, {:ctor, :T, []}, {:type, 0}]

  @spec minimize(Challenge.t(), (Challenge.t() -> boolean()), non_neg_integer()) :: Challenge.t()
  def minimize(%Challenge{} = ch, pred, budget) do
    {out, _b} = sweep(ch, pred, budget)
    out
  end

  # greedy: first accepted candidate → restart sweep; else fixpoint. Budget = pred calls.
  defp sweep(ch, pred, budget) do
    case first_accepted(candidates(ch), pred, budget) do
      {:accepted, ch2, budget2} -> sweep(reseed(ch2), pred, budget2)
      {:none, budget2} -> {ch, budget2}
    end
  end

  defp first_accepted(_cands, _pred, 0), do: {:none, 0}
  defp first_accepted([], _pred, b), do: {:none, b}
  defp first_accepted([k | rest], pred, b) do
    if well_formed?(k) do
      if safe_pred(pred, k), do: {:accepted, k, b - 1}, else: first_accepted(rest, pred, b - 1)
    else
      first_accepted(rest, pred, b)   # shape-invalid: no pred call, no budget spent
    end
  end

  defp safe_pred(pred, k) do
    pred.(k)
  rescue
    _ -> false
  catch
    _, _ -> false
  end

  defp reseed(%Challenge{} = ch), do: %{ch | seed: :erlang.phash2({ch.kind, ch.payload})}

  # ── candidate enumeration (pinned order: ctx → type → term) ──────────────────
  # Task 1 covers type + term. Task 2 prepends ctx-drop candidates.
  defp candidates(%Challenge{payload: p} = ch) do
    field_cands(ch, :type, p.type) ++ field_cands(ch, :term, p.term)
  end

  defp field_cands(ch, field, t) do
    Enum.map(term_candidates(t), fn t2 ->
      %{ch | payload: Map.put(ch.payload, field, t2)}
    end)
  end

  # all single-edit variants of a term, pre-order (edits AT this node before children)
  defp term_candidates(t) do
    here = rule1(t) ++ rule2(t) ++ rule4(t)
    deeper =
      Enum.flat_map(child_slots(t), fn {rebuild, child} ->
        Enum.map(term_candidates(child), rebuild)
      end)
    here ++ deeper
  end

  # rule 1: subterm → minimal atom, only for compound (>1 node) positions
  defp rule1(t) do
    if node_count(t) > 1, do: @minimal_atoms, else: []
  end

  # rule 2: S^k Z → S^(k-1) Z
  defp rule2({:ctor, :S, [n]}), do: [n]
  defp rule2(_), do: []

  # rule 4: structural unwrap (Task 1: non-ctx rules incl. lam/case de Bruijn)
  defp rule4({:app, f, a}), do: [f, a]
  defp rule4({:ctor, _n, args}), do: args
  defp rule4({:fst, p}), do: [p]
  defp rule4({:snd, p}), do: [p]
  defp rule4({:pair, a, b}), do: [a, b]
  defp rule4({:case, scrut, _m, branches}) do
    [scrut | for({_c, 0, body} <- branches, do: body)]   # scrut + arity-0 branch bodies only
  end
  defp rule4({:lam, _dom, body}) do
    if occurs?(body, 0), do: [], else: [Term.shift(body, -1, 0)]
  end
  defp rule4(_), do: []

  # child slots: {rebuild_fn, child} for every immediate sub-term (all Core formers)
  defp child_slots({:app, f, a}), do: [{&{:app, &1, a}, f}, {&{:app, f, &1}, a}]
  defp child_slots({:lam, d, b}), do: [{&{:lam, &1, b}, d}, {&{:lam, d, &1}, b}]
  defp child_slots({:pi, d, c}), do: [{&{:pi, &1, c}, d}, {&{:pi, d, &1}, c}]
  defp child_slots({:sigma, a, b}), do: [{&{:sigma, &1, b}, a}, {&{:sigma, a, &1}, b}]
  defp child_slots({:pair, a, b}), do: [{&{:pair, &1, b}, a}, {&{:pair, a, &1}, b}]
  defp child_slots({:fst, p}), do: [{&{:fst, &1}, p}]
  defp child_slots({:snd, p}), do: [{&{:snd, &1}, p}]
  defp child_slots({:ctor, n, args}), do: slot_list(args, &{:ctor, n, &1})
  defp child_slots({:data, n, ps, is}) do
    slot_list(ps, &{:data, n, &1, is}) ++ slot_list(is, &{:data, n, ps, &1})
  end
  defp child_slots({:case, s, m, brs}) do
    [{&{:case, &1, m, brs}, s}, {&{:case, s, &1, brs}, m}] ++
      Enum.with_index(brs)
      |> Enum.map(fn {{c, ar, body}, i} ->
        {fn nb -> {:case, s, m, List.replace_at(brs, i, {c, ar, nb})} end, body}
      end)
  end
  defp child_slots({:eq, ty, a, b}) do
    [{&{:eq, &1, a, b}, ty}, {&{:eq, ty, &1, b}, a}, {&{:eq, ty, a, &1}, b}]
  end
  defp child_slots({:refl, a}), do: [{&{:refl, &1}, a}]
  defp child_slots(_leaf), do: []

  defp slot_list(elems, rebuild_list) do
    elems
    |> Enum.with_index()
    |> Enum.map(fn {e, i} -> {fn ne -> rebuild_list.(List.replace_at(elems, i, ne)) end, e} end)
  end

  # ── measures / helpers ──────────────────────────────────────────────────────
  @spec size(Challenge.t()) :: non_neg_integer()
  def size(%Challenge{payload: p}),
    do: node_count(p.term) + length(p.ctx) + numeral_magnitude(p.term)

  defp node_count(t) when is_tuple(t),
    do: 1 + (t |> Tuple.to_list() |> tl() |> Enum.map(&node_count/1) |> Enum.sum())
  defp node_count(l) when is_list(l), do: l |> Enum.map(&node_count/1) |> Enum.sum()
  defp node_count(_), do: 0

  defp numeral_magnitude({:ctor, :S, [n]}), do: 1 + numeral_magnitude(n)
  defp numeral_magnitude(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> tl() |> Enum.map(&numeral_magnitude/1) |> Enum.sum()
  defp numeral_magnitude(l) when is_list(l), do: l |> Enum.map(&numeral_magnitude/1) |> Enum.sum()
  defp numeral_magnitude(_), do: 0

  # free-occurrence of de-Bruijn index k (crosses binders, incrementing) — mirrors Runner.occurs?/2
  def occurs?({:var, k}, k), do: true
  def occurs?({:var, _}, _k), do: false
  def occurs?({:lam, d, b}, k), do: occurs?(d, k) or occurs?(b, k + 1)
  def occurs?({:pi, d, c}, k), do: occurs?(d, k) or occurs?(c, k + 1)
  def occurs?({:sigma, a, b}, k), do: occurs?(a, k) or occurs?(b, k + 1)
  def occurs?({:case, s, m, brs}, k) do
    occurs?(s, k) or occurs?(m, k) or
      Enum.any?(brs, fn {_c, ar, body} -> occurs?(body, k + ar) end)
  end
  def occurs?(t, k) when is_tuple(t), do: t |> Tuple.to_list() |> tl() |> Enum.any?(&occurs?(&1, k))
  def occurs?(l, k) when is_list(l), do: Enum.any?(l, &occurs?(&1, k))
  def occurs?(_leaf, _k), do: false

  # shape-only well-formedness (reimplements Runner.well_formed?/1 to avoid a cycle)
  defp well_formed?(c) do
    c |> Coverage.terms_of() |> Enum.all?(&Term.term?/1)
  rescue
    _ -> false
  end
end
```

- [ ] **Step 4: Run — expect PASS** `mix test test/antigen/shrink_test.exs`

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/shrink.ex test/antigen/shrink_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): Shrink engine + term/type rules (subterm→atom, numeral, unwrap)"
```

---

## Task 2: rule 3 — context drop (de Bruijn)

**Files:** Modify `lib/antigen/shrink.ex`, `test/antigen/shrink_test.exs`.

**Interfaces:** Produces: `minimize` now also drops unreferenced `ctx` entries, shifting `term`/`type`/sibling-entry indices per spec §4 rule 3. Prepended to the candidate sweep (ctx before type/term).

- [ ] **Step 1: Write the failing tests**
```elixir
# append to test/antigen/shrink_test.exs
  test "context drop removes an unreferenced entry and shifts higher vars down" do
    # ctx [Nat, Nat]; term uses only var 0 ⇒ entry 1 is droppable, var 0 stays, higher shift
    a = art({:var, 0}, [{:data, :Nat, [], []}, {:data, :Nat, [], []}])
    out = Shrink.minimize(a, fn _ -> true end, 1000)
    assert length(out.payload.ctx) < 2
    # every var in the result is in-scope for its ctx
    assert Antigen.Shrink.closed?(out)
  end

  test "context drop is REJECTED when the entry is referenced" do
    # term uses var 1 ⇒ entry 1 (abs index 1) may not be dropped; but entry 0 (var 0 unused) may
    a = art({:var, 1}, [{:data, :Nat, [], []}, {:data, :Nat, [], []}])
    out = Shrink.minimize(a, fn ch -> Antigen.Shrink.occurs?(ch.payload.term, 0) end, 1000)
    # predicate forces keeping a reference to abs-0 after shifts; result stays closed + valid
    assert Antigen.Shrink.closed?(out)
    assert Antigen.Shrink.occurs?(out.payload.term, 0)
  end

  test "every ctx-drop candidate is de-Bruijn closed (regression guard for §7.3)" do
    a = art({:app, {:var, 0}, {:var, 2}},
            [{:data, :Nat, [], []}, {:data, :Nat, [], []}, {:data, :Nat, [], []}])
    for c <- Antigen.Shrink.candidates_for_test(a) do
      assert Antigen.Shrink.closed?(c), "candidate not closed: #{inspect(c.payload)}"
    end
  end
```

- [ ] **Step 2: Run — expect FAIL** (`ctx` never shrinks; `closed?`/`candidates_for_test` undefined).

- [ ] **Step 3: Implement** — in `lib/antigen/shrink.ex`, prepend ctx candidates and add the drop + a closedness checker (test-only export):
```elixir
  defp candidates(%Challenge{payload: p} = ch) do
    ctx_candidates(ch) ++ field_cands(ch, :type, p.type) ++ field_cands(ch, :term, p.term)
  end

  # rule 3: drop each unreferenced absolute ctx position d (index 0 = innermost/list head)
  defp ctx_candidates(%Challenge{payload: p} = ch) do
    n = length(p.ctx)
    0..(n - 1)
    |> Enum.map(fn d -> drop_candidate(ch, d) end)
    |> Enum.reject(&is_nil/1)
  end

  defp drop_candidate(%Challenge{payload: p} = ch, d) do
    ctx = p.ctx

    referenced? =
      occurs?(p.term, d) or occurs?(p.type, d) or
        ctx
        |> Enum.with_index()
        |> Enum.any?(fn {e, pos} -> pos < d and occurs?(e, d - pos - 1) end)

    if referenced? do
      nil
    else
      new_ctx =
        ctx
        |> Enum.with_index()
        |> Enum.reject(fn {_e, pos} -> pos == d end)
        |> Enum.map(fn
          {e, pos} when pos < d -> Term.shift(e, -1, d - pos)   # local k>=d-pos shift down
          {e, _pos} -> e                                         # pos>d: content unchanged
        end)

      %{ch | payload: %{p | ctx: new_ctx,
                            term: Term.shift(p.term, -1, d + 1),
                            type: Term.shift(p.type, -1, d + 1)}}
    end
  end

  # de-Bruijn closedness of the WHOLE artifact (term/type against ctx length,
  # each ctx entry against the entries outward of it). Test/guard helper.
  def closed?(%Challenge{payload: p}) do
    n = length(p.ctx)
    max_index_below(p.term, 0) < n and max_index_below(p.type, 0) < n and
      p.ctx
      |> Enum.with_index()
      |> Enum.all?(fn {e, pos} -> max_index_below(e, 0) < n - pos - 1 end)
  end

  # highest free index (relative to `depth` binders already entered), or -1 if closed-at-depth
  defp max_index_below({:var, k}, depth) when k >= depth, do: k - depth
  defp max_index_below({:var, _}, _depth), do: -1
  defp max_index_below({:lam, d, b}, depth), do: max(max_index_below(d, depth), max_index_below(b, depth + 1))
  defp max_index_below({:pi, d, c}, depth), do: max(max_index_below(d, depth), max_index_below(c, depth + 1))
  defp max_index_below({:sigma, a, b}, depth), do: max(max_index_below(a, depth), max_index_below(b, depth + 1))
  defp max_index_below({:case, s, m, brs}, depth) do
    [max_index_below(s, depth), max_index_below(m, depth) |
     Enum.map(brs, fn {_c, ar, body} -> max_index_below(body, depth + ar) end)] |> Enum.max()
  end
  defp max_index_below(t, depth) when is_tuple(t),
    do: t |> Tuple.to_list() |> tl() |> Enum.map(&max_index_below(&1, depth)) |> max_or(-1)
  defp max_index_below(l, depth) when is_list(l),
    do: l |> Enum.map(&max_index_below(&1, depth)) |> max_or(-1)
  defp max_index_below(_leaf, _depth), do: -1
  defp max_or([], default), do: default
  defp max_or(xs, _default), do: Enum.max(xs)

  # test-only: expose the full candidate list for the §7.3 closure sweep
  def candidates_for_test(ch), do: candidates(ch)
```

- [ ] **Step 4: Run — expect PASS** `mix test test/antigen/shrink_test.exs`

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/shrink.ex test/antigen/shrink_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): Shrink rule 3 — context drop with de Bruijn shift"
```

---

## Task 3: synthetic full-machinery test (spec §7.4)

**Files:** Modify `test/antigen/shrink_test.exs`.

**Interfaces:** Consumes only public `Shrink.minimize/3`; asserts end-to-end minimization of a real generated deep term under a composite predicate (infer-ok ∧ contains vcons).

- [ ] **Step 1: Write the failing test**
```elixir
# append to test/antigen/shrink_test.exs (add aliases at top: Antigen.Generators.{Term, SigMenu}, Antigen.Backend.StreamData as B, Cure.Core.{Context, Kernel})
  test "shrinks a deep well-typed term to a minimal vcons-containing witness (§7.4)" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)

    infer_ok? = fn ch ->
      c = SigMenu.rebuild_context(env, ch.payload.ctx)
      match?({:ok, _}, Kernel.infer(c, ch.payload.term))
    end
    pred = fn ch -> infer_ok?.(ch) and contains_vcons?(ch.payload.term) end

    # find a generated well-typed term containing a vcons, wrap it deeper, then shrink
    seed =
      B.interp(Term.gen_term(ctx, {:data, :Vec, [], [{:ctor, :S, [{:ctor, :Z, []}]}]}))
      |> Enum.take(50)
      |> Enum.find(&contains_vcons?/1)

    if seed do
      a = art(seed)
      assert pred.(a)
      out = Shrink.minimize(a, pred, 5000)
      assert pred.(out)
      assert Shrink.size(out) <= Shrink.size(a)
      # minimal witness: a lone vcons whose args are minimal atoms
      assert match?({:ctor, :vcons, [_, _, _]}, out.payload.term)
      assert Shrink.size(out) <= 8
    end
  end
```

- [ ] **Step 2: Run — expect FAIL** (if the assertion bounds are not yet met by the implementation, or the composite pred surfaces a rule gap). If it passes immediately, tighten the `size(out) <= 8` bound to the observed minimum so the test is load-bearing, and note why in the commit.

- [ ] **Step 3: Implement** — only if a real rule gap surfaces (e.g. a former lacking a `child_slots` clause). Otherwise no production change — this task validates Tasks 1–2 against generated input. Record the observed minimal size.

- [ ] **Step 4: Run — expect PASS** `mix test test/antigen/shrink_test.exs`

- [ ] **Step 5: Commit**
```bash
git add test/antigen/shrink_test.exs lib/antigen/shrink.ex
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(antigen): Shrink minimizes a generated deep term to a minimal witness"
```

---

## Task 4: Runner integration — same-shape pred + shrink-before-bank (§6, §7.5)

**Files:** Modify `lib/antigen/runner.ex`, `test/antigen/shrink_test.exs`.

**Interfaces:** Produces: `Runner.explore/1` minimizes any infection before banking; `same_shape?/2` (tag comparator), `@shrink_budget`/`shrink_budget/1`. Consumes: `Shrink.minimize/3`.

- [ ] **Step 1: Write the failing test** (buggy-infer end-to-end via `opts[:assay]`)
```elixir
# append to test/antigen/shrink_test.exs
  defmodule BuggyMutationAssay do
    # wraps Assays.Mutation with an infer that WRONGLY ACCEPTS :head_swap mutants
    alias Cure.Core.Kernel
    def run(%{payload: %{fault: %{kind: :head_swap}}} = c) do
      Antigen.Assays.Mutation.run(c, fn ctx, t ->
        case Kernel.infer(ctx, t) do
          {:error, _} -> {:ok, {:type, 0}}   # pretend it type-checks ⇒ wrongly accepted
          ok -> ok
        end
      end)
    end
    def run(c), do: Antigen.Assays.Mutation.run(c)
  end

  test "Runner shrinks a deep head_swap survivor to the bare minimal witness before banking (§7.5)" do
    alias Antigen.Generators.{Mutation, SigMenu}
    alias Antigen.Backend.StreamData, as: B
    tmp = System.tmp_dir!()
    corpus = Path.join(tmp, "shrink_ab_#{:erlang.unique_integer([:positive])}.sexp")
    File.rm(corpus)

    # a deep head_swap mutant (grown by deepen), in a padded context
    deep =
      B.interp(Mutation.mutant())
      |> Enum.take(400)
      |> Enum.find(fn c -> c.payload.fault.kind == :head_swap and c.payload.fault.depth >= 3 end)

    assert deep, "no deep head_swap mutant sampled"

    Antigen.Runner.explore(
      challenges: [deep], count: 1, assay: BuggyMutationAssay,
      corpus_path: corpus, seeds_path: Path.join(tmp, "seeds_ignore.sexp"),
      report_dir: tmp
    )

    banked = Antigen.Corpus.stream(corpus) |> Enum.flat_map(fn {:ok, c} -> [c]; _ -> [] end)
    assert [ab] = banked
    # term is structurally bare: strictly smaller than the deep original, still trips the bug
    assert Antigen.Shrink.size(ab) < Antigen.Shrink.size(deep)
    assert match?({:violation, {:accepted_ill_typed, _, _}}, BuggyMutationAssay.run(ab))
  end
```
(Confirm `explore/1` accepts a `challenges:` override for the batch; if it derives challenges from a generator instead, pass the generator that yields exactly `[deep]`, or add a thin `challenges:` opt — the minimal seam so the test drives one known artifact.)

- [ ] **Step 2: Run — expect FAIL** (Runner banks the raw `deep`, not a minimized one; `size(ab) == size(deep)`).

- [ ] **Step 3: Implement** — edit the infection branch in `lib/antigen/runner.ex` (§6):
```elixir
            {:violation, orig_detail} = v ->
              assay = opts[:assay] || assay_module(c.assay)
              pred = fn ch ->
                case apply(assay, :run, [ch]) do
                  {:violation, detail} -> same_shape?(detail, orig_detail)
                  _ -> false
                end
              end

              c_min = Antigen.Shrink.minimize(c, pred, shrink_budget(opts))
              {:ok, path} = Report.write_infection(opts[:report_dir], c_min, v, summarize(acc, count))
              IO.puts(Report.breadcrumb(c_min, path))
              Corpus.append(opts[:corpus_path], c_min, Corpus.dedup_key(c_min, :antibody))
              %{acc | infections: acc.infections + 1}
```
Add near the other private helpers:
```elixir
  @shrink_budget 2000
  defp shrink_budget(opts), do: opts[:shrink_budget] || @shrink_budget

  defp same_shape?(d1, d2) when is_tuple(d1) and is_tuple(d2), do: elem(d1, 0) == elem(d2, 0)
  defp same_shape?(d1, d2), do: d1 == d2
```
If `explore/1` does not already accept an explicit `challenges:` batch, add that opt at the top of `explore/1` (`challenges = opts[:challenges] || default_batch(opts)`) — the smallest seam that lets the test drive one artifact; keep the existing generator path as the default.

- [ ] **Step 4: Run — expect PASS** `mix test test/antigen/shrink_test.exs`

- [ ] **Step 5: Commit**
```bash
git add lib/antigen/runner.ex test/antigen/shrink_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): Runner shrinks infections (same-shape pred) before banking"
```

---

## Task 5: Acceptance — quarantine + full suite

**Files:** none (verification only).

- [ ] **Step 1: Quarantine** — `mix test test/antigen/architecture_test.exs`. PASS (Shrink is outside generators/assays; no `StreamData` literal).
- [ ] **Step 2: Full suite ONCE** — `mix test`. All green (§7.7: with 0 organic infections the Runner change is inert on existing corpora; banked seeds unchanged).
- [ ] **Step 3: Sanity explore** — `MIX_ENV=test mix antigen --count 300`. Expect unchanged health lines and **0 infections** (the shrink path stays dormant). Record it.
- [ ] **Step 4:** No commit.

---

## Self-Review

**Spec coverage:** §2 predicate-only-gate → Task 4's `same_shape?` + Task 1's `well_formed?`+`safe_pred`. §3 interface/seed-recompute → Task 1 `minimize/3`+`reseed`. §4 rules 1/2/4 → Task 1; rule 3 → Task 2; search discipline (ctx→type→term, pre-order, rules 1→2→4, greedy restart, budget) → Task 1 `candidates`/`term_candidates`/`sweep` + Task 2 `ctx_candidates` prepend. §5 size/monotone/idempotent/deterministic → Task 1 tests + `size/1`. §6 Runner integration → Task 4. §7 tests 1–2 Task 1; 3 Tasks 1/2 (`closed?`); 4 Task 3; 5 Task 4; 6 Task 1 budget test; 7 Task 5. §8 files/occurs?/well_formed? reimpl → Tasks 1/4. §9 non-goals respected (fault kept verbatim; no ChoiceSeq; no provenance path).

**Placeholder scan:** none. Task 3/4 note conditional impl (only if a rule gap / `challenges:` seam is needed) with concrete fallbacks — not placeholders.

**Type consistency:** `minimize/3`, `size/1`, `occurs?/2`, `closed?/1`, `candidates_for_test/1` defined Task 1/2, used in later tasks. `same_shape?/2`, `shrink_budget/1`, `@shrink_budget` Task 4. `child_slots`/`term_candidates`/`drop_candidate` internal, consistent across Tasks 1–2.

**Deviation flagged:** `well_formed?` is reimplemented in `Shrink` (not exposed from Runner) to avoid a Runner↔Shrink cycle — equivalent one-liner over the same primitives (Global Constraints).
