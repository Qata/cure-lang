defmodule Antigen.CoverGuidedTest do
  use ExUnit.Case, async: false   # :cover (+ :cover.reset) is node-wide global
  alias Antigen.Cover

  test "delta/2 reports newly-covered lines and is empty when nothing new is hit" do
    Cover.with_cover([Antigen.CoverFixture], fn ->
      Antigen.CoverFixture.classify(5)          # hit the :pos branch
      s1 = Cover.covered_set([Antigen.CoverFixture])

      Antigen.CoverFixture.classify(-1)         # hit :neg — a NEW line
      d1 = Cover.delta(s1, [Antigen.CoverFixture])
      assert MapSet.size(d1) > 0
      assert Enum.all?(d1, fn {m, l} -> m == Antigen.CoverFixture and is_integer(l) end)

      s2 = Cover.covered_set([Antigen.CoverFixture])
      Antigen.CoverFixture.classify(-2)         # hit :neg again — nothing new
      d2 = Cover.delta(s2, [Antigen.CoverFixture])
      assert MapSet.size(d2) == 0
    end)
  end

  test "attribute/4 pins each challenge's novel coverage via per-challenge reset" do
    # Cover's cond line-attribution (confirmed by probe): classify(0) covers the
    # `n<0 -> :neg` head line 4 and the `n==0` guard line 6; classify(-1) covers
    # the :neg body line 5; classify(5) covers line 6 + the `true -> :pos` line 7.
    # So with a classify(0) baseline, -1 introduces line 5 and 5 introduces line 7 —
    # two distinct, non-empty novel sets. (A classify(5) baseline would make
    # classify(0) contribute nothing novel, since line 6 is already covered — a
    # correct result that just doesn't exercise the "distinct novel" assertion.)
    Cover.with_cover([Antigen.CoverFixture], fn ->
      Antigen.CoverFixture.classify(0)          # baseline: lines {4, 6}
      prev = Cover.covered_set([Antigen.CoverFixture])

      run = fn n -> Antigen.CoverFixture.classify(n) end
      attributed = Cover.attribute(prev, [-1, 5], run, [Antigen.CoverFixture])

      assert length(attributed) == 2
      assert Enum.all?(attributed, fn {_ch, novel} -> MapSet.size(novel) > 0 end)
      [{-1, neg_novel}, {5, pos_novel}] = attributed
      refute MapSet.equal?(neg_novel, pos_novel)
    end)
  end
end
