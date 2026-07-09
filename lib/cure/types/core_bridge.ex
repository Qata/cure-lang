defmodule Cure.Types.CoreBridge do
  @moduledoc """
  Translation between the checker's *surface* type-level expression AST and
  `Cure.Core` terms, so the `Cure.Types.*` layer delegates all reduction and
  definitional equality to the trusted kernel (design decision 2026-07-01).

  The bridged grammar is the complete language of dependent-type indices:

    * integer/float/boolean literals ↔ `{:int_lit,n}` / `{:float_lit,f}` / `{:bool_lit,b}`
    * free variables                 ↔ `{:global, name}` (stay neutral, read back by name)
    * unary/binary arithmetic + comparison ↔ builtin-op GLOBAL spines
      (`int_add`/`float_mul`/…, K2 spec 2026-07-09; logic stays surface-side)
    * binary tuples + `fst`/`snd`    ↔ the inductive Sigma (D2, spec §8):
      `{:ctor, :mk_pair, [a, b]}` / a single-branch projection `:case` over
      `mk_pair` (eval's ι-rule reduces it; a stuck one reads back as the same
      case shape, recognized by its branch — the motive is never inspected)
    * n-ary applications `f(a, b)`   ↔ neutral application spine over `{:global, f}`

  `to_core/1` returns `:error` only for nodes outside this grammar (named type
  refs, n-ary tuples, …); those are irreducible type formers whose
  children the caller still normalizes structurally. `from_core/1` maps a kernel
  normal form back to surface AST.
  """

  # K2 (spec 2026-07-09 §1.4): arithmetic/comparison lower to builtin-op GLOBAL
  # spines. `to_core` is UNTYPED, so the int_*/float_* twin is chosen from the
  # SHAPE of the already-converted operands: either being `{:float_lit, _}`
  # selects float_*, else int_* (a free variable of unknown eventual type
  # defaults to int_* — dependent indices are Nat/Int-valued in practice; a
  # stuck spine reads back to the same surface binary_op either way). `rem` is
  # Int-only (no float_rem exists). `and`/`or` are NOT bridged (`:error` —
  # `Reduce.kernel_normalize` folds Boolean literal connectives surface-side).
  @int_binops %{
    +: :int_add,
    -: :int_sub,
    *: :int_mul,
    /: :int_div,
    %: :int_rem,
    ==: :int_eq,
    !=: :int_ne,
    <: :int_lt,
    <=: :int_le,
    >: :int_gt,
    >=: :int_ge
  }

  @float_binops %{
    +: :float_add,
    -: :float_sub,
    *: :float_mul,
    /: :float_div,
    %: :int_rem,
    ==: :float_eq,
    !=: :float_ne,
    <: :float_lt,
    <=: :float_le,
    >: :float_gt,
    >=: :float_ge
  }

  # Reverse maps for from_core's dedicated builtin-op spine clauses: a stuck
  # spine must read back as the surface OPERATOR node, never as a
  # `function_call "int_add"` (the generic {:app,…} unwind would mis-render it).
  @from_builtin (for {surface, core} <- @int_binops, into: %{}, do: {core, surface})
                |> Map.merge(for {surface, core} <- @float_binops, into: %{}, do: {core, surface})

  @from_unop_builtin %{int_neg: :-, float_neg: :-}

  # -- surface → Core ---------------------------------------------------------

  @doc "Translate surface type-level AST to a Core term, or `:error` if outside the index grammar."
  @spec to_core(term()) :: {:ok, Cure.Core.Term.t()} | :error
  def to_core({:literal, _meta, n}) when is_integer(n), do: {:ok, {:int_lit, n}}
  def to_core({:literal, _meta, f}) when is_float(f), do: {:ok, {:float_lit, f}}
  def to_core({:literal, _meta, b}) when is_boolean(b),
    do: {:ok, {:ctor, if(b, do: :True, else: :False), []}}

  def to_core({:variable, _meta, name}) when is_binary(name),
    do: {:ok, {:global, String.to_atom(name)}}

  def to_core({:binary_op, meta, [left, right]}) do
    with op_sym when op_sym not in [:and, :or] <- Keyword.get(meta, :operator),
         {:ok, l} <- to_core(left),
         {:ok, r} <- to_core(right),
         g when not is_nil(g) <- binop_global(op_sym, l, r) do
      {:ok, {:app, {:app, {:global, g}, l}, r}}
    else
      _ -> :error
    end
  end

  def to_core({:unary_op, meta, [operand]}) do
    case {Keyword.get(meta, :operator), to_core(operand)} do
      {:-, {:ok, o}} ->
        g = if match?({:float_lit, _}, o), do: :float_neg, else: :int_neg
        {:ok, {:app, {:global, g}, o}}

      # `not` is no longer bridged: `Reduce.kernel_normalize` folds Boolean
      # literal `not` surface-side; anything else stays structural.
      _ ->
        :error
    end
  end

  def to_core({:tuple, _meta, [a, b]}) do
    with {:ok, ca} <- to_core(a), {:ok, cb} <- to_core(b), do: {:ok, {:ctor, :mk_pair, [ca, cb]}}
  end

  def to_core({:function_call, meta, [x]}) when is_list(meta) do
    case Keyword.get(meta, :name) do
      "fst" -> with {:ok, c} <- to_core(x), do: {:ok, projection(c, 1)}
      "snd" -> with {:ok, c} <- to_core(x), do: {:ok, projection(c, 0)}
      name -> application(name, [x])
    end
  end

  def to_core({:function_call, meta, args}) when is_list(meta) and is_list(args),
    do: application(Keyword.get(meta, :name), args)

  def to_core(_other), do: :error

  # Shape dispatch (§1.4): either converted operand a float literal → float_*.
  defp binop_global(op_sym, l, r) do
    map =
      if match?({:float_lit, _}, l) or match?({:float_lit, _}, r),
        do: @float_binops,
        else: @int_binops

    Map.get(map, op_sym)
  end

  # A named application `f(a, b, …)` becomes a neutral spine `((f a) b) …`; its
  # arguments still evaluate, so `f(3 + 5)` normalizes to `f(8)`.
  defp application(name, args) when is_binary(name) and args != [] do
    case translate_all(args) do
      {:ok, cargs} ->
        {:ok, Enum.reduce(cargs, {:global, String.to_atom(name)}, fn a, acc -> {:app, acc, a} end)}

      :error ->
        :error
    end
  end

  defp application(_name, _args), do: :error

  # A projection is a single-branch case over `mk_pair` (spec §8): under the
  # branch's two binders the fields are x = var 1, y = var 0, so `fst` returns
  # var 1 and `snd` var 0. Eval's ι-rule never inspects the motive, and this
  # bridge feeds ONLY Eval (never Kernel.check), so a closed placeholder motive
  # suffices; a stuck projection reads back as this same case shape and is
  # recognized in `from_core` by its branch alone.
  @proj_motive {:lam, {:int_type}, {:int_type}}
  defp projection(p, field_var),
    do: {:case, p, @proj_motive, [{:mk_pair, 2, {:var, field_var}}]}

  defp translate_all(asts) do
    Enum.reduce_while(asts, {:ok, []}, fn ast, {:ok, acc} ->
      case to_core(ast) do
        {:ok, core} -> {:cont, {:ok, acc ++ [core]}}
        :error -> {:halt, :error}
      end
    end)
  end

  # -- Core → surface ---------------------------------------------------------

  @doc "Translate a Core normal form back to surface type-level AST."
  @spec from_core(Cure.Core.Term.t()) :: term()
  def from_core({:int_lit, n}), do: {:literal, [subtype: :integer], n}
  def from_core({:float_lit, f}), do: {:literal, [subtype: :float], f}
  def from_core({:ctor, :True, []}), do: {:literal, [subtype: :boolean], true}
  def from_core({:ctor, :False, []}), do: {:literal, [subtype: :boolean], false}
  def from_core({:global, name}), do: {:variable, [], Atom.to_string(name)}

  # Inductive Sigma read-back (D2, spec §8): mk_pair is the surface tuple; a
  # stuck projection case is recognized by its single mk_pair branch — var 1
  # (field x) was `fst`, var 0 (field y) was `snd`. The motive is not inspected.
  def from_core({:ctor, :mk_pair, [a, b]}), do: {:tuple, [], [from_core(a), from_core(b)]}

  def from_core({:case, p, _motive, [{:mk_pair, 2, {:var, 1}}]}),
    do: {:function_call, [name: "fst"], [from_core(p)]}

  def from_core({:case, p, _motive, [{:mk_pair, 2, {:var, 0}}]}),
    do: {:function_call, [name: "snd"], [from_core(p)]}

  # Builtin-op spine read-back (K2 §1.4): a STUCK arithmetic/comparison spine
  # (e.g. an unbound `n + 1`) re-spells as the surface binary_op/unary_op node.
  # Ordered BEFORE the generic {:app,…} unwind, which would otherwise mis-render
  # it as a call to a function literally named "int_add".
  def from_core({:app, {:app, {:global, g}, l}, r}) when is_map_key(@from_builtin, g),
    do: {:binary_op, [operator: Map.fetch!(@from_builtin, g)], [from_core(l), from_core(r)]}

  def from_core({:app, {:global, g}, x}) when is_map_key(@from_unop_builtin, g),
    do: {:unary_op, [operator: Map.fetch!(@from_unop_builtin, g)], [from_core(x)]}

  def from_core({:app, _f, _x} = app) do
    {head, args} = unwind(app, [])

    case head do
      {:global, name} ->
        {:function_call, [name: Atom.to_string(name)], Enum.map(args, &from_core/1)}
    end
  end

  defp unwind({:app, f, x}, acc), do: unwind(f, [x | acc])
  defp unwind(head, acc), do: {head, acc}
end
