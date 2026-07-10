defmodule Cure.Audit.QuoteSerializeTest do
  @moduledoc """
  Audit findings for `lib/cure/core/quote.ex` (NbE read-back) and
  `lib/cure/core/serialize.ex` (commitment C2's S-expression codec).

  Each test below is a specific, currently-RED executable claim about
  behavior the audit believes is correct. See the comment above each test
  for the bug, why it is wrong, and (for serialize.ex) why it matters given
  C2's stated threat model: `docs/KERNEL.md`'s "Serialization" section and
  `serialize.ex`'s own moduledoc both frame `decode/1` as the entry point an
  *independent, untrusted* checker feeds bytes into ("a kernel written in
  another language can parse this format, rebuild the Core term, and re-run
  check/infer on it"). `Antigen.Generators.DecodeProbe`'s own moduledoc says
  decode "must be TOTAL ... malformed input returns `{:error, _}` and never
  crashes or loops" — every finding below is a concrete violation of exactly
  that contract that the existing `@invalid` fuzz corpus
  (`lib/antigen/generators/decode_probe.ex`) does not cover: it only exercises
  parse-level malforms (unbalanced parens, unknown node heads, non-atom
  heads), never a syntactically-valid s-expression whose *shape* silently
  violates a `Cure.Core.Term.term?/1` invariant. Do not run this file
  automatically as part of the trusted-suite gate — it documents open
  findings, not yet-fixed regressions.
  """
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Core.{Context, Env, Inductive, Kernel, Serialize}

  # ---------------------------------------------------------------------
  # Q1: `Quote.reify/3`'s `sig` parameter exists precisely so a `{:vdata,...}`
  # value's family-declared params/indices split survives read-back (quote.ex
  # moduledoc: "required by the kernel's motive-well-formedness check ... a
  # collapsed split otherwise fails with an arity error"). `Kernel.check_via_infer/3`
  # (kernel.ex ~394-405) builds the `:conversion_failure` diagnostic by reifying
  # BOTH normal forms — but calls `Quote.reify(inferred, depth)` and
  # `Quote.reify(expected, depth)` with the 2-arity form, i.e. `sig = nil` by
  # default (quote.ex:40). The surrounding comment (kernel.ex:399-401) says this
  # is done explicitly "so the mismatch is legible (and serializable via C2 for
  # independent checkers)" — but for an INDEXED family that is exactly the case
  # `sig`-less reify is documented to get wrong: the index silently merges into
  # the flat `params` slot with `indices => []` (quote.ex:19-28, "the flat form
  # conversion compares" — true for `Conv`, false for a human/independent-checker
  # -facing diagnostic, which needs the real split to be legible at all).
  #
  # The very same file already has the correct pattern one call away:
  # `Kernel.check_case/… ` at kernel.ex:795 calls
  # `Quote.reify({:vneutral, neutral}, Context.length(ctx), Context.signature(ctx))`
  # — threading the context's signature through as the third argument. The
  # `ctx` carrying that same signature is already in scope inside
  # `check_via_infer/3`; the diagnostic call site simply omits the argument the
  # sibling call site next to it supplies. This is not the same gap as the
  # already-tracked "nf readback flattening" completeness issue (that one is
  # about `check_motive_wf`'s domain-sort inference, fixed by bypassing reify
  # entirely — see `motive_wf_indexed_domain_test.exs`); this is a second,
  # distinct call site with the identical omission, still live.
  #
  # Concretely: checking `{:var, 0}` (bound at `P(Dec, Causal)`, an indexed
  # family with one param and one index) against the mismatched expected type
  # `P(Dec, Dcoupled)` must fail with `:conversion_failure`, and the reified
  # "inferred" term in that diagnostic must show the real split — one param,
  # one index — not both index and param flattened into `params` with an
  # empty `indices` list.
  test "Q1: the :conversion_failure diagnostic for an indexed-family value preserves the params/indices split (Quote.reify is called with the context's signature, not defaulted to nil)" do
    env =
      Env.empty()
      |> Inductive.declare(
        Inductive.family(:Dec, [], [], 0),
        [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]
      )
      |> Inductive.declare(
        Inductive.family(:P, [{:a, {:type, 0}}], [{:n, {:data, :Dec, [], []}}], 1),
        [
          Inductive.ctor(:wrap, [{:p, {:var, 0}}], [{:ctor, :Causal, []}], [:present], [
            {:var, 1}
          ])
        ]
      )

    dec_val = {:vdata, :Dec, []}

    ctx =
      Context.empty(env)
      |> Context.extend({:vdata, :P, [dec_val, {:vctor, :Causal, []}]})

    # `{:var, 0}` is not a `:ctor`/`:bounded_lit` node, so `Kernel.check/3`
    # falls straight through to the generic `check_via_infer/3` fallback
    # (kernel.ex:318) rather than the ctor-specific checking path — the exact
    # call site under audit.
    expected = {:vdata, :P, [dec_val, {:vctor, :Dcoupled, []}]}

    assert {:error, {:conversion_failure, inferred_term, _expected_term}} =
             Kernel.check(ctx, {:var, 0}, expected)

    # Correct: one param (`Dec`), one index (`Causal`) — matching the family's
    # declared telescope, exactly as `Quote.reify(v, depth, Context.signature(ctx))`
    # would produce.
    assert {:data, :P, [{:data, :Dec, [], []}], [{:ctor, :Causal, []}]} == inferred_term
  end

  # ---------------------------------------------------------------------
  # Z1/Z2: `Serialize.decode/1`'s generic `build/1` has bare-leaf pass-through
  # clauses (serialize.ex:128-131: `{:int,n} -> {:ok,n}`, `{:atom,s} -> {:ok,s}`,
  # `{:float,f} -> {:ok,f}`, `{:str,s} -> {:ok,s}`). Those clauses exist ONLY so
  # `build_node`'s own literal-tag handlers can pattern-match a raw token
  # directly (e.g. `build_node("var", [{:int, k}])`, `build_node("int",
  # [{:int, n}])`) — a bare token is never meant to stand on its own as a full
  # Core TERM. But `build_all/1` (used for `ctor` args and `data`
  # params/indices, serialize.ex:179-186) and `binary/3` (used for `pi`/`lam`/
  # `app`, serialize.ex:175-177) both recurse via the SAME generic `build/1`
  # for every CHILD position — positions that must themselves be a full
  # `(tag ...)` term. `enc/1` never emits a bare token in one of these
  # positions (every literal is always wrapped, e.g. `(int 5)`), so this path
  # is unreachable from `encode/1`'s own output — it is reachable only from
  # adversarial/malformed C2 input, exactly the threat model `decode/1` exists
  # to defend. The result is not a decode failure but a silently-mangled Core
  # term: a raw Elixir scalar (not a term tuple) sitting where a sub-term
  # belongs, which fails `Cure.Core.Term.term?/1` and was never producible by
  # this module's own `encode/1`.
  test "Z1: decode rejects a bare literal token where a full term is expected (ctor argument position)" do
    # `5` is a bare `{:int, 5}` token, not `(int 5)` — `enc/1` never emits this.
    assert {:error, _} = Serialize.decode("(ctor True 5)")
  end

  test "Z2: decode rejects a bare literal token where a full term is expected (app function position)" do
    # `foo` is a bare `{:atom, "foo"}` token, not `(global foo)` — `enc/1`
    # never emits this either.
    assert {:error, _} = Serialize.decode("(app foo (int 5))")
  end

  # ---------------------------------------------------------------------
  # Z3: `build_node("type", [{:int, n}])` (serialize.ex:136) accepts ANY
  # integer with no bound check, but `Cure.Core.Term.term?/1` (term.ex:54)
  # requires `0 <= level <= Cure.Core.Universe.ceiling()` for a `{:type,
  # level}` node to be well-formed. `decode/1` therefore happily reconstructs
  # a term `term?/1` itself would reject — the exact "trusting on-disk bytes"
  # failure mode this audit was asked to hunt for. This is not merely
  # cosmetic: `Kernel.infer(_ctx, {:type, level})` (kernel.ex:45-50) calls
  # `Universe.succ(level)`, whose guard `level + 1 <= @ceiling` (universe.ex:32)
  # is satisfied by ANY negative `level` — so a negative-level `Type` term
  # decoded from untrusted C2 bytes is not merely accepted by `decode/1`, it
  # is silently type-checked as sound (`Type(-1) : Type(0)`) by the trusted
  # kernel itself, with no error anywhere on the path.
  test "Z3: decode rejects a universe level outside Term.term?/1's bound (0..Universe.ceiling())" do
    assert {:error, _} = Serialize.decode("(type 999)")
    assert {:error, _} = Serialize.decode("(type -1)")
  end

  # ---------------------------------------------------------------------
  # Z4/Z5: `build_node("var", [{:int, k}])` (serialize.ex:137) accepts any
  # integer, but `Term.term?/1` requires `k >= 0` (term.ex:55) — de Bruijn
  # indices are never negative. This is not just a shape mismatch:
  # `Cure.Core.Context.lookup/2` (context.ex:42) is `Enum.at(ts, k)`, and
  # Elixir's `Enum.at/2` treats a NEGATIVE index as counting from the END of
  # the list. So a `{:var, -1}` decoded straight from untrusted bytes does not
  # fail as "unbound" — `Context.lookup` silently resolves it to the type of
  # whatever variable happens to sit at the OTHER end of the context (the
  # outermost binding instead of "out of range"), and `Kernel.infer(ctx, {:var,
  # -1})` returns `{:ok, <wrong variable's type>}` instead of
  # `{:error, {:unbound_var, -1}}`. This is a genuine type-confusion vector
  # reachable directly from a decoded on-disk term, not merely a cosmetic
  # shape violation.
  test "Z4: decode rejects a negative de Bruijn index for :var" do
    assert {:error, _} = Serialize.decode("(var -1)")
  end

  test "Z5: a negative de Bruijn index from a decoded term must be treated as unbound, not silently wrap around to an unrelated binding" do
    # ctx has two bindings; index 0 (most recent) is Float, index 1 is Int.
    ctx =
      Context.empty()
      |> Context.extend({:vint_type})
      |> Context.extend({:vfloat_type})

    {:ok, {:var, k}} = Serialize.decode("(var -1)")

    # Correct: an out-of-range/negative index is not a binding at all.
    # `Enum.at(ts, -1)` currently resolves it to the OUTERMOST binding
    # ({:vint_type}) instead of `nil` — a variable that "-1" was never meant
    # to refer to.
    assert Context.lookup(ctx, k) == nil
  end

  # ---------------------------------------------------------------------
  # Z6: `build_node("nat", [{:int, n}])` and `build_node("bounded", [{:int, n}])`
  # (serialize.ex:145-146) accept any integer, but `Term.term?/1` requires
  # `n >= 0` for both `{:nat_lit, n}` (term.ex:72) and `{:bounded_lit, n}`
  # (term.ex:73) — both are compact literal encodings of an inherently
  # non-negative inductive tower (`Nat`'s `S`-tower over `Z`; `Bounded`'s
  # `Next`-tower over `First`) and are meaningless for negative `n`.
  # `Kernel.infer`'s clauses for both (kernel.ex:69, kernel.ex:78) are guarded
  # `when ... n >= 0` with NO unguarded fallback clause, so feeding a decoded
  # negative literal straight into the trusted kernel does not cleanly error —
  # it crashes with `FunctionClauseError` instead of the `{:error, _}` that
  # `decode/1`'s own contract (and every other malformed-input path in this
  # module) promises.
  test "Z6: decode rejects negative nat_lit / bounded_lit literals" do
    assert {:error, _} = Serialize.decode("(nat -5)")
    assert {:error, _} = Serialize.decode("(bounded -5)")
  end

  # ---------------------------------------------------------------------
  # Z7: `build_branches/1` (serialize.ex:188-200) parses a branch's arity as a
  # raw `{:int, arity}` token with no non-negativity check, but `Term.term?/1`'s
  # `branch?/1` (term.ex:294-296) requires `arity >= 0` for a `:case` branch to
  # be well-formed — a constructor can never bind a negative number of fields.
  test "Z7: decode rejects a negative case-branch arity" do
    assert {:error, _} = Serialize.decode("(case (var 0) (type 0) (branch True -3 (var 0)))")
  end

  # ---------------------------------------------------------------------
  # Z8: `sym/1` (serialize.ex:57, `Atom.to_string(atom)`) embeds a symbol's
  # name directly as a bareword in the s-expression with NO escaping/quoting,
  # unlike hole labels (`str/1`, serialize.ex:58, which DOES escape). Elixir
  # atoms are not restricted to identifier characters — an atom built via
  # `String.to_atom/1` may contain spaces, parens, or any other byte. When it
  # does, `encode/1` produces a bareword the tokenizer cannot parse back as a
  # single symbol (whitespace and parens are token delimiters, serialize.ex:77-79,
  # 98), so `decode(encode(term)) != {:ok, term}` — a straightforward,
  # unconditional loss of round-trip fidelity for a value this module's own
  # `enc/1` happily produces.
  test "Z8: encode does not escape symbol names, corrupting round-trip for a name containing whitespace" do
    name = String.to_atom("has space")
    term = {:global, name}
    encoded = Serialize.encode(term)
    assert {:ok, ^term} = Serialize.decode(encoded)
  end
end
