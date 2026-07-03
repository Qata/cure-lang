# Antigen fixture & corpus robustness hardening — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Kill any latent seed-flake in the mutation-generator tests (by making the invariants draw-independent), close the `@known_atoms` decode-safety gap, and lock the fault-schema + corpora-readable guarantees with regression tests — all on `autopilot/antigen-tier-b`.

**Architecture:** Two genuinely red→green changes (add 3 def-name atoms to `@known_atoms`; migrate the 4th corpus `reach_reify_split.sexp`) plus three regression/determinism additions whose invariants already hold today (spec §5) — verified by direct probes. The only production-code change beyond `@known_atoms` is a behavior-preserving refactor of `Mutation.apply_wrapper` into a pure `wrap/3`, giving the tests a deterministic (draw-free) hook.

**Tech Stack:** Elixir; ExUnit; `Antigen.{Corpus, Challenge}`; `Antigen.Generators.Mutation`; `Cure.Core.{Kernel, Context}`.

## Global Constraints

- **Ghost-authored commits:** `--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no `Co-Authored-By` trailer.
- **Test env:** `MIX_ENV=test mix test …` (dev env crashes). macOS has no `timeout`; `elixir` doesn't read stdin via `-` (use a script file). One build/test run at a time.
- **Reuse, don't re-derive:** the hazard set (Part 2) is precisely defined in spec §3.1 — scaffold-carried *value* strings that `from_pieces`/`decode_record` pass to `String.to_existing_atom` (kind, label, sig, def_name, family/ctor `name`/`arg_names`/`quantities`, def_group `names`/`focus`) — **not** Term-piece atoms (minted by `Serialize.decode`), **not** `assay` (never atom-converted), **not** the readable `fault=` field (minted by `decode_fault`). The membership check pulls **map VALUES only** (never keys) from the decoded scaffold, which — probe-verified — yields exactly the atomized names.
- **Construction guarantees already hold** (spec §2.1, §4a: 5,000/3,000/600-draw probes, zero violations). Items 1, 2, 3, 5 of spec §5 are regression-locks expected to pass on first run; only item 4 (atoms) and item 6 (migrate the 4th corpus) are genuinely red. Do not manufacture a red state that doesn't exist; if a "pass-first" test unexpectedly fails, that's a real new finding, not something to weaken.
- **Do not touch** `lib/antigen/corpus.ex`, the migrate task's code, or `seeds.sexp`/`corpus.sexp`/`reach.sexp` (already migrated).

---

## Task 1: `@known_atoms` completeness + membership guard (spec §3.1/§3.2 — genuinely RED)

**Files:**
- Create: `test/antigen/corpus_atoms_test.exs`
- Modify: `lib/antigen/challenge.ex` (`@known_atoms` — add three names)

**Interfaces:** consumes `Antigen.Challenge.__known_atoms__/0`, the four committed corpora, and the scaffold encoding (`Base64` of `:erlang.term_to_binary/1`).

- [ ] **Step 1: Write the failing test**

```elixir
# test/antigen/corpus_atoms_test.exs
defmodule Antigen.CorpusAtomsTest do
  use ExUnit.Case, async: true

  @corpora ~w(seeds.sexp corpus.sexp reach.sexp reach_reify_split.sexp)
           |> Enum.map(&Path.join("test/antigen", &1))

  # every hazard-string (a name from_pieces/decode_record feeds to
  # String.to_existing_atom) in every committed record must be pre-interned via
  # @known_atoms — otherwise a bare-process decode raises ArgumentError.
  # Hazard strings = the record's kind/label + every VALUE string (never a map
  # KEY) inside the decoded Base64 scaffold. Pieces atoms (Serialize mints) and
  # the fault= field (decode_fault mints) and assay (never atomized) are NOT
  # hazards and are deliberately excluded.
  defp scaffold_value_strings(b) when is_binary(b), do: [b]
  defp scaffold_value_strings(m) when is_map(m),
    do: Enum.flat_map(m, fn {_k, v} -> scaffold_value_strings(v) end)
  defp scaffold_value_strings(l) when is_list(l), do: Enum.flat_map(l, &scaffold_value_strings/1)
  defp scaffold_value_strings(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.flat_map(&scaffold_value_strings/1)
  defp scaffold_value_strings(_), do: []

  defp hazard_strings(line) do
    fields = line |> String.trim_trailing("\n") |> String.split("\t") |> tl()
    m = Map.new(fields, fn f ->
      case String.split(f, "=", parts: 2) do
        [k, v] -> {k, v}
        [k] -> {k, ""}
      end
    end)

    scaffold =
      case m["scaffold"] do
        s when s in [nil, "-"] -> %{}
        b64 -> :erlang.binary_to_term(Base.decode64!(b64))
      end

    [m["kind"], m["label"] | scaffold_value_strings(scaffold)]
    |> Enum.reject(&(&1 in [nil, "", "-"]))
  end

  test "every hazard-string in every committed corpus is a member of @known_atoms" do
    known = Antigen.Challenge.__known_atoms__() |> MapSet.new(&Atom.to_string/1)

    missing =
      for path <- @corpora, File.exists?(path), line <- File.stream!(path),
          name <- hazard_strings(line),
          not MapSet.member?(known, name),
          uniq: true,
          do: name

    assert missing == [], "hazard-strings absent from @known_atoms: #{inspect(Enum.sort(missing))}"
  end
end
```

- [ ] **Step 2: Run — expect FAIL**

Run: `MIX_ENV=test mix test test/antigen/corpus_atoms_test.exs`
Expected: FAIL — `hazard-strings absent from @known_atoms: ["data_split", "reify_distinct", "reify_eq"]`.

- [ ] **Step 3: Implement — add the three def-name atoms**

In `lib/antigen/challenge.ex`, in the `@known_atoms` list, add a line under the indexed-case vertical section (near the other `:indexed_case` names):

```elixir
    # reify / data-split verticals (lean-shape-matching): indexed-case def names
    :data_split, :reify_distinct, :reify_eq,
```

- [ ] **Step 4: Run — expect PASS**

Run: `MIX_ENV=test mix test test/antigen/corpus_atoms_test.exs`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/challenge.ex test/antigen/corpus_atoms_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "fix(antigen): add reify/data-split def-name atoms to @known_atoms + corpus membership guard"
```

---

## Task 2: Corpora-readable guard + migrate the 4th corpus (spec §4c — genuinely RED)

**Files:**
- Modify: `test/antigen/corpus_atoms_test.exs` (append the readable guard)
- Modify (data): `test/antigen/reach_reify_split.sexp` (migrate in place)

**Interfaces:** consumes `Antigen.Corpus.decode_record/1` and the four corpora; `mix antigen.migrate` (already shipped, proven idempotent/lossless by `corpus_test.exs`).

- [ ] **Step 1: Write the failing test**

```elixir
# append to test/antigen/corpus_atoms_test.exs (inside the module)
  alias Antigen.Corpus

  test "every committed corpus is in the readable format and fully decodes" do
    for path <- @corpora, File.exists?(path), line <- File.stream!(path) do
      trimmed = String.trim_trailing(line, "\n")

      pieces_field =
        trimmed |> String.split("\t") |> Enum.find_value(fn f ->
          case String.split(f, "=", parts: 2) do
            ["pieces", v] -> v
            _ -> nil
          end
        end)

      for piece <- String.split(pieces_field || "", ";;", trim: true) do
        [_id, body] = String.split(piece, "::", parts: 2)
        assert String.starts_with?(body, "("),
               "#{Path.basename(path)}: non-readable (Base64) piece: #{String.slice(body, 0, 24)}…"
      end

      assert {:ok, _} = Corpus.decode_record(trimmed), "#{Path.basename(path)}: record failed to decode"
    end
  end
```

- [ ] **Step 2: Run — expect FAIL**

Run: `MIX_ENV=test mix test test/antigen/corpus_atoms_test.exs`
Expected: FAIL on `reach_reify_split.sexp` — its one record still has Base64 pieces (`non-readable (Base64) piece: …`).

- [ ] **Step 3: Implement — migrate the 4th corpus**

```bash
MIX_ENV=test mix antigen.migrate test/antigen/reach_reify_split.sexp
```

Confirm it decodes and the replay test that reads it still passes:

```bash
MIX_ENV=test mix test test/antigen/reify_split_gap_reach_test.exs
```

Expected: migrate prints `migrated test/antigen/reach_reify_split.sexp (1 records)`; the replay test PASSES (dedup-key preserved).

- [ ] **Step 4: Run — expect PASS**

Run: `MIX_ENV=test mix test test/antigen/corpus_atoms_test.exs`
Expected: PASS (all four corpora readable + decode).

- [ ] **Step 5: Commit**

```bash
git add test/antigen/corpus_atoms_test.exs test/antigen/reach_reify_split.sexp
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "feat(antigen): migrate reach_reify_split.sexp + all-corpora-readable guard"
```

---

## Task 3: Mutation determinism — `wrap/3` refactor + draw-independent tests (spec §2 — regression-lock)

**Files:**
- Modify: `lib/antigen/generators/mutation.ex` (factor `apply_wrapper` through a pure `wrap/3`; behavior-preserving)
- Modify: `test/antigen/generators/mutation_test.exs` (replace the sampling assertions)

**Interfaces:**
- Produces: `Mutation.wrap(inner, kind, filler) :: term` — pure, draw-free application of one wrapper. `apply_wrapper/3` delegates to it (same terms, same `gnat` draws as today).
- Consumes: `Mutation.{operators, wrappers, build, wrap}`, `Cure.Core.Kernel.infer/2`.

- [ ] **Step 1: Write the failing test (determinism rewrites)**

Replace the existing `"deepen wraps a fault … UNCONTAMINATED …"` test (currently ~`:65-87`) and the `"every wrapper kind is reachable across depth-1 draws"` test (~`:89-96`) and the `"a large sample draws at least 5 distinct fault kinds …"` test (~`:60-63`) with these deterministic versions:

```elixir
  test "each wrapper is non-contaminating and fault-driven (deterministic, fixed filler)" do
    ctx = Context.empty(SigMenu.env_of(:v1))
    wt = {:ctor, :Z, []}                 # well-typed Nat
    fault = {:fst, {:ctor, :Z, []}}      # intrinsically ill-typed

    for kind <- Mutation.wrappers() do
      assert {:ok, _} = Kernel.infer(ctx, Mutation.wrap(wt, kind, wt)),
             "wrapper #{kind} contaminated a well-typed inner"
      assert {:error, _} = Kernel.infer(ctx, Mutation.wrap(fault, kind, wt)),
             "wrapper #{kind} did not propagate the inner fault"
    end
  end

  test "a fixed deep wrapper stack stays well-typed and propagates a fault (composition)" do
    ctx = Context.empty(SigMenu.env_of(:v1))
    wt = {:ctor, :Z, []}
    fault = {:fst, {:ctor, :Z, []}}
    # fold every wrapper kind, innermost-first, with a fixed Nat filler
    stack = fn inner -> Enum.reduce(Mutation.wrappers(), inner, fn k, acc -> Mutation.wrap(acc, k, wt) end) end

    assert {:ok, _} = Kernel.infer(ctx, stack.(wt)), "deep fixed stack contaminated a well-typed inner"
    assert {:error, _} = Kernel.infer(ctx, stack.(fault)), "deep fixed stack swallowed the fault"
  end

  test "every operator and every wrapper kind is reachable by construction (deterministic)" do
    ctx = Context.empty(SigMenu.env_of(:v1))
    # each operator's build deterministically records its own fault kind
    kinds = Enum.map(Mutation.operators(), fn op -> elem(Mutation.build(ctx, op), 1).kind end)
    assert Enum.sort(kinds) == Enum.sort(Mutation.operators())
    # each wrapper kind applies without error and yields a distinct well-formed term
    terms = Enum.map(Mutation.wrappers(), fn k -> Mutation.wrap({:ctor, :Z, []}, k, {:ctor, :Z, []}) end)
    assert length(Enum.uniq(terms)) == length(Mutation.wrappers())
    assert Enum.all?(terms, &Cure.Core.Term.term?/1)
  end
```

Leave the `"every operator produces a term the kernel REJECTS"` test (~`:9-21`) and the witness-invariant test (~`:23-46`) as-is: the former is construction-safe (0/600 no-op, filler-independent per spec §2.1) and the latter is already deterministic; neither is a seed-flake surface.

- [ ] **Step 2: Run — expect FAIL (compile error)**

Run: `MIX_ENV=test mix test test/antigen/generators/mutation_test.exs`
Expected: FAIL — `Mutation.wrap/3` is undefined.

- [ ] **Step 3: Implement — factor `wrap/3` out of `apply_wrapper`**

In `lib/antigen/generators/mutation.ex`, add the pure `wrap/3` (public, near `apply_wrapper`) and rewrite `apply_wrapper/3` to delegate — producing byte-identical terms and the same `gnat` draws as today:

```elixir
  @doc "Pure application of one Nat→Nat wrapper with an explicit Nat `filler`."
  def wrap(inner, :app_arg, filler), do: {:app, {:app, {:global, :plus}, inner}, filler}
  def wrap(inner, :ctor_nat, _filler), do: {:ctor, :S, [inner]}
  def wrap(inner, :case_scrut, _filler), do: {:case, inner, motive(), nat_branches(z())}
  def wrap(inner, :case_branch, filler), do: {:case, filler, motive(), nat_branches(inner)}
  def wrap(inner, :pair, filler), do: {:app, {:lam, sig(), z()}, {:pair, inner, filler}}

  # :app_arg/:case_branch/:pair draw a well-typed Nat filler; :ctor_nat/:case_scrut ignore it.
  defp apply_wrapper(ctx, inner, kind) when kind in [:app_arg, :case_branch, :pair],
    do: Gen.bind(gnat(ctx), fn f -> Gen.return(wrap(inner, kind, f)) end)

  defp apply_wrapper(_ctx, inner, kind),
    do: Gen.return(wrap(inner, kind, z()))
```

Delete the five old `defp apply_wrapper(...)` clauses (their term shapes now live once in `wrap/3`).

- [ ] **Step 4: Run — expect PASS**

Run: `MIX_ENV=test mix test test/antigen/generators/mutation_test.exs`
Expected: PASS (all tests, including the untouched sampling/witness ones).

- [ ] **Step 5: Commit**

```bash
git add lib/antigen/generators/mutation.ex test/antigen/generators/mutation_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "refactor(antigen): pure Mutation.wrap/3 + draw-independent wrapper/reachability tests"
```

---

## Task 4: Fault-codec coverage lock over generator-emitted shapes (spec §4a — regression-lock)

**Files:**
- Modify: `test/antigen/corpus_test.exs` (append one coverage test)

**Interfaces:** consumes `Antigen.Corpus.{encode_record, decode_record}`, `Mutation.{operators, build, deepen}`, `Antigen.Generators.Conversion.conv_reject`, `Antigen.Backend.StreamData`.

- [ ] **Step 1: Write the test (expected to pass on first run — §4a verified)**

```elixir
# append to test/antigen/corpus_test.exs
  alias Antigen.Generators.{Mutation, SigMenu}
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.Context, as: CoreCtx

  test "fault codec round-trips every fault shape the generators actually emit (§4a lock)" do
    ctx = CoreCtx.empty(SigMenu.env_of(:v1))

    # one static fault per operator (build/2's fault map is deterministic)
    op_faults = Enum.map(Mutation.operators(), fn op -> elem(Mutation.build(ctx, op), 1) end)

    # a deepened fault (adds :depth + :wrap_path list) — take one concrete draw
    {_deep, path} = B.interp(Mutation.deepen(ctx, {:fst, {:ctor, :Z, []}}, 3)) |> Enum.at(0)
    deep_fault = Map.merge(hd(op_faults), %{depth: 3, wrap_path: path})

    # a conversion carrier fault (:expected_index/:actual_index/:carrier/:reduction ints+atoms)
    conv = B.interp(Antigen.Generators.Conversion.conv_reject()) |> Enum.at(0)
    conv_fault = conv.payload.fault

    for fault <- [deep_fault, conv_fault | op_faults] do
      c = Challenge.new(kind: :mutant_term, assay: "mutation/rejection", label: :ill_typed,
                        payload: %{sig: :v1, ctx: [], type: {:type, 0}, term: {:ctor, :Z, []}, fault: fault})
      assert {:ok, c2} = Corpus.decode_record(Corpus.encode_record(c))
      assert c2.payload.fault == fault, "fault codec lost a generator-emitted shape: #{inspect(fault)}"
    end
  end
```

- [ ] **Step 2: Run — expect PASS on first run**

Run: `MIX_ENV=test mix test test/antigen/corpus_test.exs`
Expected: PASS (spec §4a probe-confirmed the codec already covers these shapes). If it fails, that is a real codec/generator drift finding — investigate, do not weaken the test.

- [ ] **Step 3: Commit**

```bash
git add test/antigen/corpus_test.exs
git commit --author="Made In Heaven <madeinheaven@madeinheaven.com>" -m "test(antigen): lock fault-codec coverage over generator-emitted fault shapes"
```

---

## Self-Review

**Spec coverage:** §2.1 construction guarantees → Task 3 (`wrap/3` refactor documents/locks non-contamination; the invariant already holds so no generator fix — §2.1). §2.2 deterministic tests → Task 3 (uncontaminated → per-wrapper fixed-filler; diversity/reachability → construction-based). §3.1 atom audit → Task 1 (adds `:data_split`/`:reify_distinct`/`:reify_eq`). §3.2 membership guard → Task 1 (values-only scaffold walk + kind/label, the probe-verified precise set). §4a fault-schema lock → Task 4. §4c corpora-readable + migrate 4th corpus → Task 2. §5 red/green split honored (Tasks 1,2 red; Tasks 3,4 pass-first regression locks). §6 files match. §7 non-goals respected (no re-banking; only `reach_reify_split.sexp` data change; `corpus.ex` untouched).

**Placeholder scan:** none — every step has concrete code/commands.

**Type consistency:** `Mutation.wrap/3` is defined in Task 3 and consumed only there; `hazard_strings`/`scaffold_value_strings` are private to the new test module; `@corpora` is shared across Tasks 1–2 in the same file. `Corpus.{encode_record,decode_record,raw_key}` and `Challenge.__known_atoms__/0` are existing public functions. The membership walk collects map **values** only (skips keys) — the exact predicate the probe validated to yield `["data_split","reify_distinct","reify_eq"]` and nothing else.

**Ordering:** Task 1 before Task 2 (both edit `corpus_atoms_test.exs`; Task 1 creates it). Task 2's migration of `reach_reify_split.sexp` does not affect Task 1's membership test (that test dual-reads legacy Base64 fine). Tasks 3–4 are independent.
