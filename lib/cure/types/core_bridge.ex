defmodule Cure.Types.CoreBridge do
  @moduledoc """
  Translation between the checker's *surface* type-level expression AST and
  `Cure.Core` terms, so the `Cure.Types.*` layer delegates all reduction and
  definitional equality to the trusted kernel (design decision 2026-07-01).

  The bridged grammar is the complete language of dependent-type indices:

    * integer/float/boolean literals ↔ `{:int_lit,n}` / `{:float_lit,f}` / `{:bool_lit,b}`
    * free variables                 ↔ `{:global, name}` (stay neutral, read back by name)
    * unary/binary arithmetic, comparison, logic ↔ `{:prim, op, args}`
    * binary tuples + `fst`/`snd`    ↔ `{:pair, a, b}` / `{:fst,_}` / `{:snd,_}`
    * n-ary applications `f(a, b)`   ↔ neutral application spine over `{:global, f}`

  `to_core/1` returns `:error` only for nodes outside this grammar (named type
  refs, refinements, n-ary tuples, …); those are irreducible type formers whose
  children the caller still normalizes structurally. `from_core/1` maps a kernel
  normal form back to surface AST.
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
      {:-, {:ok, o}} -> {:ok, {:prim, :neg, [o]}}
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
      name -> application(name, [x])
    end
  end

  def to_core({:function_call, meta, args}) when is_list(meta) and is_list(args),
    do: application(Keyword.get(meta, :name), args)

  def to_core(_other), do: :error

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
  def from_core({:pair, a, b}), do: {:tuple, [], [from_core(a), from_core(b)]}
  def from_core({:fst, p}), do: {:function_call, [name: "fst"], [from_core(p)]}
  def from_core({:snd, p}), do: {:function_call, [name: "snd"], [from_core(p)]}

  def from_core({:prim, :neg, [x]}), do: {:unary_op, [operator: :-], [from_core(x)]}
  def from_core({:prim, :not, [x]}), do: {:unary_op, [operator: :not], [from_core(x)]}

  def from_core({:prim, op, [l, r]}),
    do: {:binary_op, [operator: Map.fetch!(@from_binop, op)], [from_core(l), from_core(r)]}

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
