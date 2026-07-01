defmodule Cure.Types.CoreBridge do
  @moduledoc """
  Translation between the checker's *surface* type-level expression AST and
  `Cure.Core` terms, so the legacy `Cure.Types.*` layer can delegate reduction
  and definitional equality to the trusted kernel (design decision 2026-07-01).

  The bridged fragment is the arithmetic/logic core of dependent indices:

    * integer/boolean literals  ↔ `{:int_lit,n}` / `{:bool_lit,b}`
    * free variables            ↔ `{:global, name}` (stay neutral, read back by name)
    * arithmetic/comparison/logic operators ↔ `{:prim, op, args}`
    * binary tuples             ↔ `{:pair, a, b}` with `fst`/`snd` projections

  `to_core/1` returns `:error` for anything outside this fragment (floats, named
  types, refinements, n-ary tuples, …) so the caller can fall back to its own
  handling. `from_core/1` maps a kernel normal form back to surface AST.
  """

  @binops %{
    +: :add,
    -: :sub,
    *: :mul,
    /: :div,
    %: :rem,
    ==: :eq,
    !=: :ne,
    <: :lt,
    <=: :le,
    >: :gt,
    >=: :ge,
    and: :and,
    or: :or
  }

  @from_binop for {surface, core} <- @binops, into: %{}, do: {core, surface}

  @doc "Translate surface type-level AST to a Core term, or `:error` if outside the fragment."
  @spec to_core(term()) :: {:ok, Cure.Core.Term.t()} | :error
  def to_core({:literal, _meta, n}) when is_integer(n), do: {:ok, {:int_lit, n}}
  def to_core({:literal, _meta, b}) when is_boolean(b), do: {:ok, {:bool_lit, b}}

  def to_core({:variable, _meta, name}) when is_binary(name),
    do: {:ok, {:global, String.to_atom(name)}}

  def to_core({:binary_op, meta, [left, right]}) do
    with op when not is_nil(op) <- Map.get(@binops, Keyword.get(meta, :operator)),
         {:ok, l} <- to_core(left),
         {:ok, r} <- to_core(right) do
      {:ok, {:prim, op, [l, r]}}
    else
      _ -> :error
    end
  end

  def to_core({:unary_op, meta, [operand]}) do
    case {Keyword.get(meta, :operator), to_core(operand)} do
      {:not, {:ok, o}} -> {:ok, {:prim, :not, [o]}}
      {:-, {:ok, o}} -> {:ok, {:prim, :sub, [{:int_lit, 0}, o]}}
      _ -> :error
    end
  end

  def to_core({:tuple, _meta, [a, b]}) do
    with {:ok, ca} <- to_core(a), {:ok, cb} <- to_core(b), do: {:ok, {:pair, ca, cb}}
  end

  def to_core({:function_call, meta, [x]}) when is_list(meta) do
    case Keyword.get(meta, :name) do
      "fst" -> with {:ok, c} <- to_core(x), do: {:ok, {:fst, c}}
      "snd" -> with {:ok, c} <- to_core(x), do: {:ok, {:snd, c}}
      _ -> :error
    end
  end

  def to_core(_other), do: :error

  @doc "Translate a Core normal form back to surface type-level AST."
  @spec from_core(Cure.Core.Term.t()) :: term()
  def from_core({:int_lit, n}), do: {:literal, [subtype: :integer], n}
  def from_core({:bool_lit, b}), do: {:literal, [subtype: :boolean], b}
  def from_core({:global, name}), do: {:variable, [], Atom.to_string(name)}
  def from_core({:pair, a, b}), do: {:tuple, [], [from_core(a), from_core(b)]}
  def from_core({:fst, p}), do: {:function_call, [name: "fst"], [from_core(p)]}
  def from_core({:snd, p}), do: {:function_call, [name: "snd"], [from_core(p)]}

  def from_core({:prim, :sub, [{:int_lit, 0}, x]}),
    do: {:unary_op, [operator: :-], [from_core(x)]}

  def from_core({:prim, :not, [x]}), do: {:unary_op, [operator: :not], [from_core(x)]}

  def from_core({:prim, op, [l, r]}),
    do: {:binary_op, [operator: Map.fetch!(@from_binop, op)], [from_core(l), from_core(r)]}
end
