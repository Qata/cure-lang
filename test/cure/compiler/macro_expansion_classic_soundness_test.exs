# test/cure/compiler/macro_expansion_classic_soundness_test.exs
defmodule Cure.Compiler.MacroExpansionClassicSoundnessTest do
  # TRANSITIONAL SOUNDNESS FIREWALL for the CLASSIC pipeline entry that
  # `cure build`/the CLI actually calls (`Cure.Compiler.compile_string/2`) on
  # non-dependent macro-using programs. Same property as the dependent firewall
  # (`test/cure/elab/macro_expansion_soundness_test.exs`): a macro's expansion
  # is type-checked identically to hand-written code — verdict-equality, here
  # with `[line:/col:]` metadata stripped since the classic error vocabulary is
  # position-bearing. DELETE THIS FILE when the classic-pipeline-deletion
  # initiative removes Cure.Types.Checker + classic Codegen; the dependent
  # firewall is the permanent guard.
  use ExUnit.Case, async: true
  alias Cure.Compiler

  # Recursively drop :line/:col pairs so macro (template-line) and hand-written
  # (source-line) verdicts compare equal. Leaves every other term shape intact.
  defp strip(t) when is_list(t) do
    t |> Enum.reject(&match?({k, _} when k in [:line, :col], &1)) |> Enum.map(&strip/1)
  end

  defp strip(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.map(&strip/1) |> List.to_tuple()

  defp strip(t), do: t

  defp verdict(src) do
    case Compiler.compile_string(src, []) do
      {:ok, _mod, _forms} -> :accept
      {:error, term} -> {:reject, strip(Cure.Elab.Program.semantic_error(term))}
    end
  end

  @cases [
    {"zero-hole accept: zero => 0", "mod M\n  macro Zero\n    syntax zero becomes 0\n  fn f() -> Int = zero\n",
     "mod M\n  fn f() -> Int = 0\n"},
    {"one-hole accept: inc <x> => x + 1",
     "mod M\n  macro Inc\n    syntax inc <x: Code> becomes x + 1\n  fn f(n: Int) -> Int = inc n\n",
     "mod M\n  fn f(n: Int) -> Int = n + 1\n"},
    {"reject (unbound var): bad => nonexistent_thing",
     "mod M\n  macro Bad\n    syntax bad becomes nonexistent_thing\n  fn f() -> Int = bad\n",
     "mod M\n  fn f() -> Int = nonexistent_thing\n"},
    {"reject (type mismatch): tt => true used as Int",
     "mod M\n  macro T\n    syntax tt becomes true\n  fn f() -> Int = tt\n", "mod M\n  fn f() -> Int = true\n"}
  ]

  for {label, macro_src, hand_src} <- @cases do
    test "classic macro verdict equals hand-written verdict — #{label}" do
      assert verdict(unquote(macro_src)) == verdict(unquote(hand_src))
    end
  end

  test "the two well-typed cases genuinely accept (classic)" do
    assert verdict("mod M\n  macro Zero\n    syntax zero becomes 0\n  fn f() -> Int = zero\n") == :accept

    assert verdict("mod M\n  macro Inc\n    syntax inc <x: Code> becomes x + 1\n  fn f(n: Int) -> Int = inc n\n") ==
             :accept
  end

  test "the two ill-typed cases genuinely reject (classic)" do
    assert {:reject, _} =
             verdict("mod M\n  macro Bad\n    syntax bad becomes nonexistent_thing\n  fn f() -> Int = bad\n")

    assert {:reject, _} = verdict("mod M\n  macro T\n    syntax tt becomes true\n  fn f() -> Int = tt\n")
  end

  test "classic compilation rejects a macro with an ill-typed generated expansion" do
    assert {:reject, {:expansion_ill_typed, _}} =
             verdict("mod M\n  macro Bad\n    syntax bad <n: Nat> becomes n + true\n  fn f() -> Int = 0\n")
  end
end
