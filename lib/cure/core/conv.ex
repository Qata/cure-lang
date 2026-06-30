defmodule Cure.Core.Conv do
  @moduledoc """
  Definitional equality (conversion) by normalization-by-evaluation
  (design spec §4.5; mirrors Idris `Core/Normalise/Convert.idr` and Lean
  `type_checker.cpp`'s `is_def_eq`).

  `conv?/4` evaluates both terms under the shared environment and compares the
  resulting values up to β, ι (projections; `case`-ι added in M4), and η. δ
  (global unfolding) is **not** enabled until a global is certified total (M7);
  until then two `:nglobal` heads are convertible iff they are the same name.

  **This is the single canonical conversion entry point** — every caller (the
  kernel's `check`, M6's `refl`) uses `conv?/4`. η is handled here, type-free:
  when one side is a `:vlam` and the other is applicable (a λ or a neutral), we
  apply both to a fresh neutral and compare the bodies (the §4.5 η rule).
  """

  alias Cure.Core.Eval

  @doc """
  True iff `term1` and `term2` are definitionally equal under `env`.

  `depth` is the number of binders in scope (the next fresh de Bruijn level).
  """
  @spec conv?(Cure.Core.Term.t(), Cure.Core.Term.t(), [Cure.Core.Value.t()], non_neg_integer()) ::
          boolean()
  def conv?(term1, term2, env, depth) do
    conv_val?(Eval.eval(term1, env), Eval.eval(term2, env), depth)
  end

  @doc """
  Value-level definitional equality — the core of `conv?/4` for callers (the
  kernel's `check`) that already hold evaluated values. Same NbE algorithm; this
  is **not** a type-indexed variant, just a different entry point.
  """
  @spec conv_values?(Cure.Core.Value.t(), Cure.Core.Value.t(), non_neg_integer()) :: boolean()
  def conv_values?(v1, v2, depth), do: conv_val?(v1, v2, depth)

  # -- value-level conversion -------------------------------------------------

  # η first: a λ on either side, compared by applying both to a fresh neutral.
  defp conv_val?({:vlam, _, _} = l, r, depth), do: eta_eq?(l, r, depth)
  defp conv_val?(l, {:vlam, _, _} = r, depth), do: eta_eq?(r, l, depth)

  defp conv_val?({:vtype, l1}, {:vtype, l2}, _depth), do: l1 == l2

  defp conv_val?({:vneutral, n1}, {:vneutral, n2}, depth), do: conv_neutral?(n1, n2, depth)

  defp conv_val?({:vpair, a1, b1}, {:vpair, a2, b2}, depth),
    do: conv_val?(a1, a2, depth) and conv_val?(b1, b2, depth)

  defp conv_val?({:vpi, d1, c1}, {:vpi, d2, c2}, depth),
    do: conv_val?(d1, d2, depth) and conv_closure?(c1, c2, depth)

  defp conv_val?({:vsigma, d1, c1}, {:vsigma, d2, c2}, depth),
    do: conv_val?(d1, d2, depth) and conv_closure?(c1, c2, depth)

  defp conv_val?({:vdata, n1, vs1}, {:vdata, n2, vs2}, depth),
    do: n1 == n2 and conv_spine?(vs1, vs2, depth)

  defp conv_val?({:vctor, n1, vs1}, {:vctor, n2, vs2}, depth),
    do: n1 == n2 and conv_spine?(vs1, vs2, depth)

  defp conv_val?(_, _, _), do: false

  # η / β-under-binder: apply both values to a fresh neutral and compare bodies.
  # Only valid when the partner is itself applicable (a λ or a neutral); against
  # anything else the two are not convertible.
  defp eta_eq?(lam, {:vlam, _, _} = other, depth), do: apply_eq?(lam, other, depth)
  defp eta_eq?(lam, {:vneutral, _} = other, depth), do: apply_eq?(lam, other, depth)
  defp eta_eq?(_lam, _other, _depth), do: false

  defp apply_eq?(v1, v2, depth) do
    fresh = {:vneutral, {:nvar, depth}}
    conv_val?(Eval.apply(v1, fresh), Eval.apply(v2, fresh), depth + 1)
  end

  # Compare two closures (Π/Σ codomains) under one fresh binder.
  defp conv_closure?({:closure, env1, t1}, {:closure, env2, t2}, depth) do
    fresh = {:vneutral, {:nvar, depth}}
    conv_val?(Eval.eval(t1, [fresh | env1]), Eval.eval(t2, [fresh | env2]), depth + 1)
  end

  defp conv_spine?(vs1, vs2, depth) do
    length(vs1) == length(vs2) and
      Enum.zip(vs1, vs2) |> Enum.all?(fn {a, b} -> conv_val?(a, b, depth) end)
  end

  # -- neutral conversion -----------------------------------------------------

  defp conv_neutral?({:nvar, l1}, {:nvar, l2}, _depth), do: l1 == l2
  # δ is gated (M7): uncertified globals are opaque, equal iff the same name.
  defp conv_neutral?({:nglobal, a}, {:nglobal, b}, _depth), do: a == b

  defp conv_neutral?({:napp, n1, v1}, {:napp, n2, v2}, depth),
    do: conv_neutral?(n1, n2, depth) and conv_val?(v1, v2, depth)

  defp conv_neutral?({:nfst, n1}, {:nfst, n2}, depth), do: conv_neutral?(n1, n2, depth)
  defp conv_neutral?({:nsnd, n1}, {:nsnd, n2}, depth), do: conv_neutral?(n1, n2, depth)
  defp conv_neutral?(_, _, _), do: false
end
