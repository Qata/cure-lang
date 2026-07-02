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
    # NOT `fn _ -> true end`: rule 1 is tried before rule 4 ("here" order is
    # rule1 ++ rule2 ++ rule4) and fires on ANY node with node_count > 1 — the
    # top-level lam here has node_count 3 (lam + Nat-dom + var), so a fully
    # permissive predicate would let rule 1 replace the WHOLE lam with its
    # first minimal-atom menu item ({:ctor,:Z,[]}) before rule 4's lam-unwrap
    # is ever tried, and the test would observe `{:ctor,:Z,[]}`, not
    # `{:var,0}` (confirmed by hand-trace + probe against the plan's own
    # `size`/`node_count` helpers). The predicate must exclude the minimal
    # atoms so only a `:var`/`:lam`-shaped result is accepted, isolating rule
    # 4's behavior.
    keep_var_or_lam = fn ch -> match?({:var, _}, ch.payload.term) or match?({:lam, _, _}, ch.payload.term) end
    # λx:Nat. (var 1)  — body does NOT use var 0 ⇒ unwrap to (var 0) after shift
    a = art({:lam, {:data, :Nat, [], []}, {:var, 1}}, [{:data, :Nat, [], []}])
    out = Shrink.minimize(a, keep_var_or_lam, 1000)
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

  test "budget caps cost (pred calls), not accepted edits — spec §3" do
    # NOTE (execution finding): the plan's prior form of this test assumed
    # budget = number of *accepted edits* (`budget:1` ⇒ one edit ⇒ progress).
    # That contradicts spec §3, which defines budget as "max candidate
    # evaluations, i.e. pred calls" — a COST cap. For `num(5)` under an
    # S-headed predicate each sweep rejects the 4 minimal-atom candidates
    # (Z/vnil/T/Type₀ — none S-headed) before rule 2's single-S-peel is
    # accepted, so the FIRST accept costs 5 pred calls. A budget below that
    # makes ZERO progress (the cost cap bites first — correct behavior); a
    # large budget reaches the fixpoint S Z. Rewritten to the spec-faithful
    # behavior (test-encodes-wrong-behavior exception, justified by §3).
    a = art(num(5))                                       # size 11
    pred = fn ch -> match?({:ctor, :S, _}, ch.payload.term) end
    assert Shrink.minimize(a, pred, 3).payload.term == num(5)   # 3 pred calls all reject ⇒ no progress
    out_full = Shrink.minimize(a, pred, 1000)
    assert out_full.payload.term == s(num(0))             # fixpoint: S Z
    assert Shrink.size(out_full) < Shrink.size(a)         # enough budget minimizes
  end

  test "a predicate that raises is safely treated as reject (LOCKED: pred crashes are rescued)" do
    # Global Constraints locks "pred crashes are rescued -> reject", implemented
    # by `safe_pred/2`, but no test anywhere exercised a raising predicate
    # before this — a real gap, since `well_formed?` is shape-only (doesn't
    # check de-Bruijn closedness), so a real assay could plausibly raise on an
    # out-of-scope candidate `pred` builds from. Here `pred` raises
    # specifically on `Z`, so the sweep must safely skip over it (not crash)
    # and settle at the last candidate where `pred` holds without raising.
    a = art(s(s(num(0))))   # S(S(Z))
    pred = fn ch ->
      case ch.payload.term do
        {:ctor, :S, _} -> true
        {:ctor, :Z, []} -> raise "boom"
        _ -> false
      end
    end
    out = Shrink.minimize(a, pred, 1000)   # must not raise
    assert out.payload.term == s(num(0))   # settles at S Z: Z is reachable but pred raises there
    assert pred.(out)
  end

  defp contains_vcons?({:ctor, :vcons, _}), do: true
  defp contains_vcons?(t) when is_tuple(t), do: t |> Tuple.to_list() |> tl() |> Enum.any?(&contains_vcons?/1)
  defp contains_vcons?(l) when is_list(l), do: Enum.any?(l, &contains_vcons?/1)
  defp contains_vcons?(_), do: false
end
