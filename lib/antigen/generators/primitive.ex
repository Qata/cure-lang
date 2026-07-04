defmodule Antigen.Generators.Primitive do
  @moduledoc """
  Structure-directed generator for **primitive arithmetic** Core terms
  (`{:prim, op, args}`), the reachability lever for `Cure.Core.Eval.fold/2`,
  `Kernel.infer_prim/3`, and `numeric_type?/1` — the kernel's Int/Float
  evaluation and typing paths, which the mode-directed `Generators.Term`
  machinery never emits (its goal menu has no Int/Float types, spec §5).

  Every generated term is well-typed **by construction** over the v1 signature
  in the empty context: operands are `:int_lit`/`:float_lit` literals (or shallow
  nested prims of the same numeric type), and the claimed `type` is exactly the
  op's result type (`{:int_type}` or `{:float_type}`). div/rem occasionally draw
  a **zero divisor**, which the kernel types fine but `Eval.fold` leaves *stuck*
  (`{:vneutral, {:nprim, ...}}`) — this is what exercises fold's `:stuck` /
  guarded-fold clauses.

  Emits **numeric** prims (result `Int`/`Float`: `add/sub/mul/div/rem/neg`) and
  **numeric comparisons** (`lt/le/gt/ge/eq/ne` over Int/Float operands, result
  `Bool` via the `:bool` builtin). The Boolean **connectives** (`and/or/not`) and
  Bool-operand `eq/ne` are deliberately NOT emitted: the connectives were retired
  from the kernel to Std.Bool `case`-defs (they now fail `infer_prim` with
  `{:unknown_prim, op}`), and Bool-operand `eq/ne` infers but no longer folds
  (stuck). Both are covered instead through the elaborator's Std.Bool lowering.

  Tagged for the three infer+normalize assays (`infer_check`, `subject_reduction`,
  `normalization`); `normalization` is the one that drives `nf` — hence `eval` —
  hence `fold`.
  """
  alias Antigen.{Gen, Challenge}

  # Numeric-result assays only — every one runs `infer` then `nf` on the term,
  # which is the path through `Eval.fold`. (erasure_preservation is omitted: its
  # value here is marginal and it is the one assay that does not add fold coverage.)
  @assays ["term/infer_check", "term/subject_reduction", "term/normalization"]

  @lit_range 20
  @max_depth 2

  @bool_type {:data, :Bool, [], []}
  @cmp_ops [:lt, :le, :gt, :ge, :eq, :ne]

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.member_of(@assays), fn assay ->
      Gen.bind(prim_gen(), fn {term, type} ->
        Gen.return(
          Challenge.new(
            kind: :typed_term,
            assay: assay,
            label: :well_typed,
            payload: %{sig: :v1, ctx: [], type: type, term: term},
            note: "primitive arithmetic"
          )
        )
      end)
    end)
  end

  # -- prim term + its result type -------------------------------------------
  defp prim_gen do
    Gen.frequency([
      {5, Gen.bind(int_prim(@max_depth), fn t -> Gen.return({t, {:int_type}}) end)},
      {4, Gen.bind(float_prim(@max_depth), fn t -> Gen.return({t, {:float_type}}) end)},
      {5, Gen.bind(bool_prim(@max_depth), fn t -> Gen.return({t, @bool_type}) end)}
    ])
  end

  # -- Int prims --------------------------------------------------------------
  defp int_prim(depth) do
    Gen.frequency([
      {2, binop(:add, &int_operand/1, depth)},
      {2, binop(:sub, &int_operand/1, depth)},
      {2, binop(:mul, &int_operand/1, depth)},
      {2, divop(:div, &int_operand/1, int_zero(), depth)},
      {2, divop(:rem, &int_operand/1, int_zero(), depth)},
      {1, unop(:neg, &int_operand/1, depth)}
    ])
  end

  defp int_operand(0), do: int_lit()

  defp int_operand(depth) do
    Gen.frequency([{4, int_lit()}, {1, int_prim(depth - 1)}])
  end

  defp int_lit, do: Gen.bind(Gen.int(-@lit_range, @lit_range), fn n -> Gen.return({:int_lit, n}) end)
  defp int_zero, do: Gen.return({:int_lit, 0})

  # -- Float prims (no :rem — infer_prim forces Int operands for remainder) ---
  defp float_prim(depth) do
    Gen.frequency([
      {2, binop(:add, &float_operand/1, depth)},
      {2, binop(:sub, &float_operand/1, depth)},
      {2, binop(:mul, &float_operand/1, depth)},
      {2, divop(:div, &float_operand/1, float_zero(), depth)},
      {1, unop(:neg, &float_operand/1, depth)}
    ])
  end

  defp float_operand(0), do: float_lit()

  defp float_operand(depth) do
    Gen.frequency([{4, float_lit()}, {1, float_prim(depth - 1)}])
  end

  defp float_lit,
    do: Gen.bind(Gen.int(-@lit_range, @lit_range), fn n -> Gen.return({:float_lit, n / 4}) end)

  defp float_zero, do: Gen.return({:float_lit, 0.0})

  # -- Bool-returning prims ---------------------------------------------------
  # Numeric comparisons (Int or Float operands), result Bool. Connectives and
  # Bool-operand eq/ne are intentionally excluded (retired / non-folding) — see
  # the moduledoc.
  defp bool_prim(depth) do
    Gen.frequency(
      Enum.flat_map(@cmp_ops, fn op ->
        [{1, binop(op, &int_operand/1, depth)}, {1, binop(op, &float_operand/1, depth)}]
      end)
    )
  end

  # -- op shapes --------------------------------------------------------------
  defp binop(op, operand, depth) do
    Gen.bind(operand.(depth), fn a ->
      Gen.bind(operand.(depth), fn b -> Gen.return({:prim, op, [a, b]}) end)
    end)
  end

  # A binary op whose right operand is occasionally a zero literal (stuck fold).
  defp divop(op, operand, zero_gen, depth) do
    Gen.bind(operand.(depth), fn a ->
      Gen.bind(Gen.frequency([{6, operand.(depth)}, {1, zero_gen}]), fn b ->
        Gen.return({:prim, op, [a, b]})
      end)
    end)
  end

  defp unop(op, operand, depth) do
    Gen.bind(operand.(depth), fn a -> Gen.return({:prim, op, [a]}) end)
  end
end
