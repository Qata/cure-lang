defmodule Cure.Elab.ProgramCodegenGateTest do
  # The program-level codegen gate must share the ONE Final-Core enforcement
  # mechanism (Validator.release_config) with the emit gate — not a second,
  # hand-maintained hole walker that can drift. `Erase.has_hole?` has no
  # `{:prim, …}` clause, so a hole in a primitive-op argument slipped past it;
  # the validator descends into prim args, so it catches the same leak the emit
  # boundary now catches (K3, single trusted enforcement point).
  use ExUnit.Case, async: true
  alias Cure.Core.Env
  alias Cure.Elab.Program

  test "codegen gate refuses a hole hidden in a primitive-op argument" do
    body = {:prim, :add, [{:hole, "x"}, {:int_lit, 1}]}
    env = Env.empty() |> Env.add_def(:tainted, {:type, 0}, body, [])
    assert {:error, {:unfilled_hole, :tainted}} = Program.check_codegen_ready(env)
  end

  test "codegen gate still refuses a plain body hole" do
    env = Env.empty() |> Env.add_def(:h, {:type, 0}, {:hole, "body"}, [])
    assert {:error, {:unfilled_hole, :h}} = Program.check_codegen_ready(env)
  end

  test "codegen gate accepts a hole-free program" do
    env = Env.empty() |> Env.add_def(:clean, {:type, 0}, {:int_lit, 42}, [])
    assert :ok = Program.check_codegen_ready(env)
  end
end
