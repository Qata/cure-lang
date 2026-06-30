defmodule Cure.Core.Certificate do
  @moduledoc """
  Totality decision procedures the kernel re-runs before certifying a global for
  δ-reduction (design spec §7).

  Operates directly on **Core terms** (not the surface AST), keeping the trusted
  kernel self-contained. Coverage is already enforced by the kernel's `case`
  typing (`check_def` re-runs it), so this module supplies the **termination**
  half.

  The termination check is *sound but conservative*: a non-recursive definition
  certifies; any self-recursion is rejected (`:not_total`). Slice-1 type-level
  functions (e.g. `and`) are non-recursive, so this suffices; structural /
  size-change recursion (cf. Idris `Core/Termination/SizeChange.idr`) is the
  completion path for recursive type-level functions, out of Slice-1 scope (§2).
  A conservative *rejection* is always sound — the kernel never certifies a
  function it cannot prove total, so δ never unfolds a non-terminating global.
  """

  @doc "True when the Core `body` of global `name` is provably terminating."
  @spec terminating?(atom(), Cure.Core.Term.t()) :: boolean()
  def terminating?(name, body), do: not calls?(name, body)

  # Does `term` contain a reference to the global `name` (a self-call)?
  defp calls?(name, {:global, n}), do: n == name
  defp calls?(name, {:pi, d, c}), do: calls?(name, d) or calls?(name, c)
  defp calls?(name, {:lam, d, b}), do: calls?(name, d) or calls?(name, b)
  defp calls?(name, {:sigma, a, b}), do: calls?(name, a) or calls?(name, b)
  defp calls?(name, {:app, f, a}), do: calls?(name, f) or calls?(name, a)
  defp calls?(name, {:pair, a, b}), do: calls?(name, a) or calls?(name, b)
  defp calls?(name, {:fst, p}), do: calls?(name, p)
  defp calls?(name, {:snd, p}), do: calls?(name, p)

  defp calls?(name, {:data, _n, ps, is}),
    do: Enum.any?(ps, &calls?(name, &1)) or Enum.any?(is, &calls?(name, &1))

  defp calls?(name, {:ctor, _n, args}), do: Enum.any?(args, &calls?(name, &1))

  defp calls?(name, {:case, s, m, brs}),
    do:
      calls?(name, s) or calls?(name, m) or
        Enum.any?(brs, fn {_c, _ar, b} -> calls?(name, b) end)

  defp calls?(name, {:eq, t, a, b}), do: calls?(name, t) or calls?(name, a) or calls?(name, b)
  defp calls?(name, {:refl, a}), do: calls?(name, a)

  defp calls?(name, {:rewrite, p, m, b}),
    do: calls?(name, p) or calls?(name, m) or calls?(name, b)

  defp calls?(_name, _term), do: false
end
