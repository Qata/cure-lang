defmodule Antigen.Generators.EqualityTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.{Equality, SigMenu}
  alias Antigen.Backend.StreamData, as: B
  alias Antigen.Challenge
  alias Cure.Core.{Context, Kernel, Normalise}

  defp ctx, do: SigMenu.rebuild_context(SigMenu.env_of(:v1), [])
  @sample 400

  test "every sampled equality challenge is a well-typed :typed_term over v1" do
    for %Challenge{} = c <- B.interp(Equality.gen()) |> Enum.take(@sample) do
      assert c.kind == :typed_term
      assert c.assay in Antigen.Generators.Term.assay_ids()
      assert c.payload.sig == :v1 and c.payload.ctx == []

      cx = ctx()

      case Kernel.infer(cx, c.payload.term) do
        {:ok, inferred} ->
          assert Normalise.quote(inferred, Context.length(cx)) == c.payload.type
          assert Normalise.nf(cx, c.payload.term, fuel: 500_000) != :fuel_exhausted

        other ->
          flunk("equality term failed to infer: #{inspect(c.payload.term)} -> #{inspect(other)}")
      end
    end
  end

  test "the sample exercises refl, eq-type, and rewrite shapes" do
    sample = B.interp(Equality.gen()) |> Enum.take(@sample)
    heads = sample |> Enum.map(fn c -> elem(c.payload.term, 0) end) |> MapSet.new()
    for h <- [:refl, :eq, :rewrite], do: assert(h in heads, "shape #{h} never generated")

    # an eq-type challenge is a Type-0 proposition (drives infer_type_value_sort)
    assert Enum.any?(sample, fn c -> match?({:eq, _, _, _}, c.payload.term) and c.payload.type == {:type, 0} end)
    # a refl challenge claims an Eq type
    assert Enum.any?(sample, fn c -> match?({:refl, _}, c.payload.term) and match?({:eq, _, _, _}, c.payload.type) end)
  end
end
