defmodule Cure.Elab.TotalityClosure do
  @moduledoc """
  The **untrusted** type-level totality driver (design spec §5, §7).

  The kernel re-checks each totality certificate (`Kernel.validate_certificate`,
  M7.2); this module decides *which* functions must be certified — the half of
  §7 the kernel does not do. It computes the transitive closure of every global
  reachable from a **type position** (an index expression in a constructor
  signature, a telescope type) — these are the functions whose reduction the
  type-checker relies on, so they must be total — and submits each to the
  kernel. A member that fails certification surfaces as the §10
  `:totality_required` diagnostic, naming the offending function.

  Runtime-only partial functions (referenced in no type) are *not* required to
  be total. Being untrusted, a function this walk misses simply stays
  uncertified (opaque to δ) — never a soundness hole (§7). Surface `@total`
  flags and the whole-program wiring are added at integration time (M9.2).
  """

  alias Cure.Core.{Env, Kernel}

  @doc "The set of global function names reachable from a type position (transitively)."
  @spec type_level_fns(Env.t()) :: MapSet.t(atom())
  def type_level_fns(%Env{} = env) do
    seeds = seed_globals(env)
    close(env, MapSet.to_list(seeds), seeds)
  end

  @doc """
  Submit every type-level function to the kernel for certification, threading the
  resulting (certification-augmented) signature. Returns `{:error,
  {:totality_required, name}}` for the first that cannot be certified.
  """
  @spec certify_type_level(Env.t()) :: {:ok, Env.t()} | {:error, {:totality_required, atom()}}
  def certify_type_level(%Env{} = env) do
    env
    |> type_level_fns()
    |> MapSet.to_list()
    |> Enum.reduce_while({:ok, env}, fn name, {:ok, acc} ->
      case Kernel.validate_certificate(acc, name) do
        {:ok, acc2} -> {:cont, {:ok, acc2}}
        {:error, _reason} -> {:halt, {:error, {:totality_required, name}}}
      end
    end)
  end

  # -- seeds: globals appearing in family/constructor type positions ----------

  defp seed_globals(%Env{families: families, ctors: ctors}) do
    from_families =
      families |> Map.values() |> Enum.flat_map(fn f -> tele_globals(f.params) ++ tele_globals(f.indices) end)

    from_ctors =
      ctors
      |> Map.values()
      |> Enum.flat_map(fn c -> tele_globals(c.args) ++ Enum.flat_map(c.result_indices, &collect/1) end)

    MapSet.new(from_families ++ from_ctors)
  end

  defp tele_globals(tele), do: Enum.flat_map(tele, fn {_name, ty} -> collect(ty) end)

  # Transitive closure: a type-level function's callees are themselves type-level.
  defp close(_env, [], acc), do: acc

  defp close(env, [name | rest], acc) do
    case Env.get_def(env, name) do
      nil ->
        close(env, rest, acc)

      %{body: body} ->
        fresh = body |> collect() |> Enum.reject(&MapSet.member?(acc, &1))
        close(env, rest ++ fresh, Enum.reduce(fresh, acc, &MapSet.put(&2, &1)))
    end
  end

  # -- collect global names occurring in a Core term --------------------------

  defp collect({:global, n}), do: [n]
  defp collect({:pi, d, c}), do: collect(d) ++ collect(c)
  defp collect({:lam, d, b}), do: collect(d) ++ collect(b)
  defp collect({:sigma, a, b}), do: collect(a) ++ collect(b)
  defp collect({:app, f, a}), do: collect(f) ++ collect(a)
  defp collect({:pair, a, b}), do: collect(a) ++ collect(b)
  defp collect({:fst, p}), do: collect(p)
  defp collect({:snd, p}), do: collect(p)

  defp collect({:data, _n, ps, is}),
    do: Enum.flat_map(ps, &collect/1) ++ Enum.flat_map(is, &collect/1)

  defp collect({:ctor, _n, args}), do: Enum.flat_map(args, &collect/1)

  defp collect({:case, s, m, brs}),
    do: collect(s) ++ collect(m) ++ Enum.flat_map(brs, fn {_c, _ar, b} -> collect(b) end)

  defp collect(_), do: []
end
