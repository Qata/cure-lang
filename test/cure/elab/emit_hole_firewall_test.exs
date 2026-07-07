defmodule Cure.Elab.EmitHoleFirewallTest do
  # The emit/release boundary is the single trusted enforcement point for "no
  # unfilled obligation ships" (K3). It must validate the *pre-erase* Core body:
  # `Erase.erase` drops erased subterms ({:rewrite, proof, _, body} -> body,
  # {:eq,…}/{:refl,…} -> nullary ctors), so a hole hidden in an erased position
  # is invisible to the old erase-then-`has_hole?` gate and shipped silently (#102).
  use ExUnit.Case, async: true
  alias Cure.Core.Env
  alias Cure.Elab.Emit

  test "emit refuses a def whose hole hides in an erased (rewrite-proof) position (#102)" do
    body = {:rewrite, {:hole, "p"}, {:type, 0}, {:int_lit, 0}}
    env = Env.empty() |> Env.add_def(:tainted, {:type, 0}, body, [])
    assert {:error, {:unfilled_hole, :tainted}} = Emit.compile_forms(env, :M, [:tainted])
  end

  test "emit still refuses a plain body hole" do
    env = Env.empty() |> Env.add_def(:h, {:type, 0}, {:hole, "body"}, [])
    assert {:error, {:unfilled_hole, :h}} = Emit.compile_forms(env, :M, [:h])
  end

  test "compile_and_load refuses an erased-position hole too (same gate)" do
    body = {:rewrite, {:hole, "p"}, {:type, 0}, {:int_lit, 0}}
    env = Env.empty() |> Env.add_def(:tainted2, {:type, 0}, body, [])
    assert {:error, {:unfilled_hole, :tainted2}} =
             Emit.compile_and_load(env, module: :M2, functions: [:tainted2])
  end

  test "emit still accepts a hole-free def (no false positive)" do
    env = Env.empty() |> Env.add_def(:clean, {:type, 0}, {:int_lit, 42}, [])
    assert {:ok, _forms} = Emit.compile_forms(env, :M, [:clean])
  end
end
