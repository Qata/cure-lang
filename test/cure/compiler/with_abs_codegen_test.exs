defmodule Cure.Compiler.WithAbsCodegenTest do
  @moduledoc """
  Runtime codegen for value-level `with`-abstraction. A value-level
  `with e … arms` erases its type-level refinement and must run identically
  to the equivalent `match e … arms` (an Erlang `case`).

  These are end-to-end checks: the source is compiled to Erlang forms,
  loaded into the VM, and the resulting functions are actually invoked.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Codegen, Lexer, Parser}

  # A value-level `with` (no dependent constructs) routes through the
  # surface codegen path (Cure.Compiler.Codegen), not the kernel.
  @with_src """
  mod WithVal
    type Nat = Z | S(Nat)
    fn pred(n: Nat) -> Nat =
      with n
        Z() -> Z()
        S(k) -> k
  end
  """

  @match_src """
  mod MatchVal
    type Nat = Z | S(Nat)
    fn pred(n: Nat) -> Nat =
      match n
        Z() -> Z()
        S(k) -> k
  end
  """

  @with_proof_src """
  mod WithProofVal
    type Nat = Z | S(Nat)
    fn pred(n: Nat) -> Nat =
      with n proof pf
        Z() -> Z()
        S(k) -> k
  end
  """

  defp forms(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    refute Cure.Elab.Program.dependent?(ast), "expected a non-dependent (surface) program"
    {:ok, forms} = Codegen.compile_module(ast, emit_events: false)
    forms
  end

  # Locate the `case` form emitted for the body of `pred/1`.
  defp pred_case_form(forms) do
    fun =
      Enum.find(forms, fn
        {:function, _l, :pred, 1, _clauses} -> true
        _ -> false
      end)

    assert {:function, _l, :pred, 1, [{:clause, _cl, _pats, _guards, body}]} = fun
    Enum.find(body, &match?({:case, _, _, _}, &1))
  end

  test "value-level `with` compiles, loads, and runs like the equivalent `match`" do
    assert {:ok, wmod} = Cure.Compiler.compile_and_load(@with_src, emit_events: false)
    assert {:ok, mmod} = Cure.Compiler.compile_and_load(@match_src, emit_events: false)

    # pred(S(Z)) == Z, pred(Z) == Z
    assert apply(wmod, :pred, [{:s, {:z}}]) == {:z}
    assert apply(wmod, :pred, [{:z}]) == {:z}
    assert apply(wmod, :pred, [{:s, {:s, {:z}}}]) == {:s, {:z}}

    # `with` runs identically to `match` on every input.
    for input <- [{:z}, {:s, {:z}}, {:s, {:s, {:z}}}] do
      assert apply(wmod, :pred, [input]) == apply(mmod, :pred, [input])
    end
  end

  test "value-level `with` lowers to an Erlang `case` (same shape as `match`)" do
    with_case = pred_case_form(forms(@with_src))
    match_case = pred_case_form(forms(@match_src))

    assert {:case, _, _scrut, _clauses} = with_case
    # The emitted `case` is structurally identical to the `match` lowering
    # (line numbers may differ; erase them before comparing).
    assert strip_lines(with_case) == strip_lines(match_case)
  end

  test "`with … proof p` compiles, loads, and runs like the no-proof form" do
    assert {:ok, pmod} = Cure.Compiler.compile_and_load(@with_proof_src, emit_events: false)

    assert apply(pmod, :pred, [{:s, {:z}}]) == {:z}
    assert apply(pmod, :pred, [{:z}]) == {:z}
    assert apply(pmod, :pred, [{:s, {:s, {:z}}}]) == {:s, {:z}}
  end

  # Replace every line number in an Erlang abstract form with 0 so two
  # structurally-equal forms compare equal regardless of source position.
  defp strip_lines(form) when is_tuple(form) do
    [tag | rest] = Tuple.to_list(form)

    rest =
      case rest do
        [maybe_line | tail] when is_integer(maybe_line) -> [0 | Enum.map(tail, &strip_lines/1)]
        _ -> Enum.map(rest, &strip_lines/1)
      end

    List.to_tuple([tag | rest])
  end

  defp strip_lines(list) when is_list(list), do: Enum.map(list, &strip_lines/1)
  defp strip_lines(other), do: other
end
