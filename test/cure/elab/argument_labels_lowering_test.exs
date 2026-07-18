defmodule Cure.Elab.ArgumentLabelsLoweringTest do
  @moduledoc """
  Ph2 Slice B: the parsed argument labels (Slice A) are lowered onto the
  function's def record as a telescope-aligned label vector, readable via
  `Cure.Core.Env.labels/2`. A label-free def stores no label data (inertness).
  """
  use ExUnit.Case, async: true

  alias Cure.Core.Env
  alias Cure.Elab.Program

  defp elab!(src) do
    {:ok, env} = Program.elaborate(src)
    env
  end

  test "a labelled parameter lowers to a telescope-aligned label vector" do
    env = elab!("mod M\n  fn move(to dest: Int) -> Int = dest\nend\n")
    assert Env.labels(env, :"M#move") == ["to"]
  end

  test "a mix of labelled and unlabelled parameters aligns labels by position" do
    env = elab!("mod M\n  fn blit(src: Int, to dest: Int) -> Int = dest\nend\n")
    assert Env.labels(env, :"M#blit") == [nil, "to"]
  end

  test "a label-free def carries no label vector (inert)" do
    env = elab!("mod M\n  fn add(x: Int, y: Int) -> Int = x + y\nend\n")
    assert Env.labels(env, :"M#add") == nil
    refute Map.has_key?(env.defs[:"M#add"], :labels)
  end
end
