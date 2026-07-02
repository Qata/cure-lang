defmodule Antigen.Generators.ConversionTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.{Conversion, SigMenu}
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.{Context, Kernel}

  defp sample(gen, n), do: B.interp(gen) |> Enum.take(n)

  test "conv_reject: every carrier at a range of depths infer-REJECTS, with kernel-free witness" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)

    depths =
      for c <- sample(Conversion.conv_reject(), 300) do
        p = c.payload
        assert %Antigen.Challenge{kind: :mutant_term, assay: "mutation/rejection", label: :ill_typed} = c
        f = p.fault
        assert f.carrier in Conversion.carriers()
        assert f.witness == :conv and f.reduction == :required
        assert f.actual_index == f.expected_index + 1     # kernel-free non-convertibility witness
        assert f.depth == f.expected_index
        # the discriminating index position is a plus REDEX, not a numeral (conversion-at-depth)
        assert redex?(f.carrier, p.term)
        assert {:error, _} = Kernel.infer(ctx, p.term)     # construction guarantee (+ totality)
        f.depth
      end

    assert Enum.member?(depths, 0) and Enum.max(depths) >= 4   # depth reached; d=0 exercised
    assert length(Enum.uniq(depths)) >= 3
  end

  defp redex?(:conv_index, {:ctor, :vcons, [n, _, _]}), do: is_plus(n)
  defp redex?(:conv_motive, {:case, _, {:lam, _, {:data, :Vec, _, [idx]}}, _}), do: is_plus(idx)
  defp is_plus({:app, {:app, {:global, :plus}, _}, _}), do: true
  defp is_plus(_), do: false
end
