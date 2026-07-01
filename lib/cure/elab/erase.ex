defmodule Cure.Elab.Erase do
  @moduledoc """
  {0,ω} erasure of Core terms (design spec §8 / M9.1).

  Dependent indices exist only for type-checking; at runtime they carry no
  information, so erasure drops every `:erased` constructor argument (the
  quantities recorded by the elaborator, M8.3). What remains is a plain,
  non-dependent value the runtime can represent directly — e.g. `seq` erases from
  its seven-argument dependent form to the two stream functions it actually
  stores.

  `has_hole?/1` reports whether a term still contains an unfilled hole; a program
  with holes typechecks but must not be emitted (§6 negative #5).
  """

  alias Cure.Core.Inductive

  @doc "Erase a Core term to its runtime form (drop erased constructor arguments)."
  @spec erase(Cure.Core.Env.t(), Cure.Core.Term.t()) :: Cure.Core.Term.t()
  def erase(env, {:ctor, cname, args}) do
    quantities = Inductive.ctor_quantities(env, cname) || List.duplicate(:present, length(args))

    kept =
      args
      |> Enum.zip(quantities)
      |> Enum.filter(fn {_arg, q} -> q == :present end)
      |> Enum.map(fn {arg, _q} -> erase(env, arg) end)

    {:ctor, cname, kept}
  end

  def erase(env, {:lam, dom, body}), do: {:lam, erase(env, dom), erase(env, body)}
  def erase(env, {:app, f, x}), do: {:app, erase(env, f), erase(env, x)}
  def erase(env, {:pair, a, b}), do: {:pair, erase(env, a), erase(env, b)}
  def erase(env, {:fst, p}), do: {:fst, erase(env, p)}
  def erase(env, {:snd, p}), do: {:snd, erase(env, p)}
  def erase(env, {:pi, d, c}), do: {:pi, erase(env, d), erase(env, c)}
  def erase(env, {:sigma, a, b}), do: {:sigma, erase(env, a), erase(env, b)}

  def erase(env, {:data, n, ps, is}),
    do: {:data, n, Enum.map(ps, &erase(env, &1)), Enum.map(is, &erase(env, &1))}

  def erase(env, {:case, s, m, branches}) do
    {:case, erase(env, s), erase(env, m),
     Enum.map(branches, fn {c, ar, b} -> {c, ar, erase(env, b)} end)}
  end

  def erase(_env, term), do: term

  @doc "Does the term still contain an unfilled hole?"
  @spec has_hole?(Cure.Core.Term.t()) :: boolean()
  def has_hole?({:hole, _name}), do: true
  def has_hole?({:lam, d, b}), do: has_hole?(d) or has_hole?(b)
  def has_hole?({:pi, d, c}), do: has_hole?(d) or has_hole?(c)
  def has_hole?({:sigma, a, b}), do: has_hole?(a) or has_hole?(b)
  def has_hole?({:app, f, x}), do: has_hole?(f) or has_hole?(x)
  def has_hole?({:pair, a, b}), do: has_hole?(a) or has_hole?(b)
  def has_hole?({:fst, p}), do: has_hole?(p)
  def has_hole?({:snd, p}), do: has_hole?(p)
  def has_hole?({:ctor, _n, args}), do: Enum.any?(args, &has_hole?/1)
  def has_hole?({:data, _n, ps, is}), do: Enum.any?(ps ++ is, &has_hole?/1)

  def has_hole?({:case, s, m, branches}),
    do: has_hole?(s) or has_hole?(m) or Enum.any?(branches, fn {_c, _ar, b} -> has_hole?(b) end)

  def has_hole?(_term), do: false
end
