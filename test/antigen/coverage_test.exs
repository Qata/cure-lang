defmodule Antigen.CoverageTest do
  use ExUnit.Case, async: true
  alias Antigen.{Challenge, Coverage}

  test "constructor set and depth bucket for a small term" do
    c = Challenge.stub({:app, {:lam, {:type, 0}, {:var, 0}}, {:type, 0}})
    {ctors, bucket, _flags, label} = Coverage.key(c)
    assert :app in ctors and :lam in ctors and :type in ctors and :var in ctors
    assert bucket == :b0_2
    assert label == :none
  end

  test "app_present flag is set when an application occurs" do
    c = Challenge.stub({:app, {:var, 0}, {:var, 1}})
    {_ctors, _bucket, flags, _label} = Coverage.key(c)
    assert :app_present in flags
    refute :case_present in flags
  end

  test "depth bucket climbs into b3_5 for a deeper term" do
    deep = {:app, {:app, {:app, {:var, 0}, {:var, 0}}, {:var, 0}}, {:var, 0}}
    {_c, bucket, _f, _l} = Coverage.key(Challenge.stub(deep))
    assert bucket == :b3_5
  end

  test "key_string is stable and identical for equal keys" do
    c = Challenge.stub({:type, 0})
    assert Coverage.key_string(Coverage.key(c)) == Coverage.key_string(Coverage.key(c))
    assert is_binary(Coverage.key_string(Coverage.key(c)))
  end

  test "has_shadowing flag fires for a binder nested under another binder, not for a single binder" do
    single = {:lam, {:type, 0}, {:var, 0}}
    {_c, _b, flags1, _l} = Coverage.key(Challenge.stub(single))
    refute :has_shadowing in flags1

    curried_pi = {:pi, {:type, 0}, {:pi, {:type, 0}, {:type, 0}}}
    {_c, _b, flags2, _l} = Coverage.key(Challenge.stub(curried_pi))
    assert :has_shadowing in flags2
  end
end
