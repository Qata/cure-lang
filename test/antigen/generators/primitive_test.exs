defmodule Antigen.Generators.PrimitiveTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.{Primitive, SigMenu}
  alias Antigen.Backend.StreamData, as: B
  alias Antigen.Challenge
  alias Cure.Core.{Context, Kernel, Normalise}

  defp ctx, do: SigMenu.rebuild_context(SigMenu.env_of(:v1), [])

  @sample 400

  test "every sampled prim challenge is a well-typed :typed_term over v1" do
    for %Challenge{} = c <- B.interp(Primitive.gen()) |> Enum.take(@sample) do
      assert c.kind == :typed_term
      assert c.assay in Antigen.Generators.Term.assay_ids()
      assert c.payload.sig == :v1
      assert c.payload.ctx == []
      assert match?({:prim, _op, _args}, c.payload.term),
             "expected a :prim term, got #{inspect(c.payload.term)}"

      cx = ctx()

      case Kernel.infer(cx, c.payload.term) do
        {:ok, inferred} ->
          # the claimed type is exactly the inferred type
          assert Normalise.quote(inferred, Context.length(cx)) == c.payload.type
          # and it normalizes without fuel exhaustion (exercises Eval.fold)
          assert Normalise.nf(cx, c.payload.term, fuel: 500_000) != :fuel_exhausted

        other ->
          flunk("prim term failed to infer: #{inspect(c.payload.term)} -> #{inspect(other)}")
      end
    end
  end

  test "the sample exercises every arithmetic op and both numeric types" do
    sample = B.interp(Primitive.gen()) |> Enum.take(@sample)

    ops = sample |> Enum.map(fn c -> elem(c.payload.term, 1) end) |> MapSet.new()
    for op <- [:add, :sub, :mul, :div, :rem, :neg], do: assert(op in ops, "op #{op} never generated")

    types = sample |> Enum.map(fn c -> c.payload.type end) |> MapSet.new()
    assert {:int_type} in types
    assert {:float_type} in types
  end

  test "the sample includes at least one stuck (zero-divisor) prim" do
    sample = B.interp(Primitive.gen()) |> Enum.take(@sample)

    assert Enum.any?(sample, fn c ->
             match?({:prim, op, [_, {:int_lit, 0}]} when op in [:div, :rem], c.payload.term)
           end),
           "no zero-divisor prim generated (needed to hit Eval.fold's :stuck clauses)"
  end
end
