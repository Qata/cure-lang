defmodule Cure.Core.TermTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Term

  test "constructs and recognises core nodes" do
    assert Term.term?({:type, 0})
    assert Term.term?({:var, 0})
    assert Term.term?({:pi, {:type, 0}, {:var, 0}})
    assert Term.term?({:app, {:lam, {:type, 0}, {:var, 0}}, {:type, 0}})
    refute Term.term?({:type, 3})
    refute Term.term?({:var, -1})
    refute Term.term?(:not_a_term)
  end
end
