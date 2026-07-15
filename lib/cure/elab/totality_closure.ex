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
    # Wave-3: an @extern global has no Core body to certify (it is an asserted FFI
    # postulate — spec §2.1 point 4). Certification is a category error for it, so
    # skip it here rather than hand its sentinel body to Kernel.check.
    |> Enum.reject(&extern_def?(env, &1))
    |> Enum.reduce_while({:ok, env}, fn name, {:ok, acc} ->
      case Kernel.validate_certificate(acc, name) do
        {:ok, acc2} -> {:cont, {:ok, acc2}}
        {:error, _reason} -> {:halt, {:error, {:totality_required, name}}}
      end
    end)
  end

  @doc """
  Certify the ordinary total-function closure rooted at compile-time callbacks.

  `computed by` executes a normal Cure function, so its reducer may need to
  unfold imported helpers such as `Std.List.map` and source-level syntax
  builders. Those helpers are not necessarily reachable from a type position;
  certification therefore starts from the callback's elaborated Core globals
  and follows the same kernel-checked closure discipline. This expands
  reducibility for the untrusted compile-time evaluator without changing the
  trusted Core or making runtime functions globally transparent.
  """
  @spec certify_roots(Env.t(), [atom()]) :: {:ok, Env.t()} | {:error, term()}
  def certify_roots(%Env{} = env, roots) when is_list(roots) do
    roots = Enum.filter(roots, &(Env.get_def(env, &1) != nil))

    env
    |> close(roots, MapSet.new(roots))
    |> MapSet.to_list()
    |> Enum.reject(&extern_def?(env, &1))
    |> Enum.reduce_while({:ok, env}, fn name, {:ok, acc} ->
      case Kernel.validate_certificate(acc, name) do
        {:ok, acc2} -> {:cont, {:ok, acc2}}
        {:error, reason} -> {:halt, {:error, {:compile_time_totality, name, reason}}}
      end
    end)
  end

  @doc """
  Re-certify runtime defs that a *declaration-order* deferral left uncertified.

  `Certificate.terminating?/3` deliberately defers (stays uncertified) a def with a
  still-`{:hole, "__pending__"}` callee, because that callee's onward calls are
  invisible and the SCC cannot be trusted (mutual-recursion soundness). The per-def
  `maybe_certify` in `Declarations` runs in declaration order, so a total function
  that calls a helper declared *below* it — `reverse` → `reverse_acc` — is certified
  while the helper is still pending and is deferred. `certify_type_level/1` only
  re-certifies functions reachable from a type position, so a runtime-only total
  function stays uncertified forever.

  This sweep runs once every body is present. It resubmits every uncertified,
  non-extern, non-builtin def with a real (non-pending) body to the kernel. It is a
  no-op for genuinely partial functions: the kernel re-derives the certificate and
  rejects them exactly as before. No fixpoint is needed — `terminating?/3` reads
  bodies, not the `certified` set, so a single pass over the complete env is exact.
  """
  @spec certify_deferred(Env.t()) :: Env.t()
  def certify_deferred(%Env{certified: nil} = env), do: env

  def certify_deferred(%Env{defs: defs} = env) do
    Enum.reduce(defs, env, fn {name, def}, acc ->
      cond do
        Env.certified?(acc, name) -> acc
        match?(%{body: {:hole, _}}, def) -> acc
        match?(%{body: {:extern, _}}, def) -> acc
        not is_nil(Map.get(def, :builtin_op)) -> acc
        true ->
          case Kernel.validate_certificate(acc, name) do
            {:ok, acc2} -> acc2
            {:error, _} -> acc
          end
      end
    end)
  end

  defp extern_def?(env, name), do: match?(%{body: {:extern, _}}, Env.get_def(env, name))

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
  defp collect({:pi, _g, d, c}), do: collect(d) ++ collect(c)
  defp collect({:lam, _g, d, b}), do: collect(d) ++ collect(b)
  defp collect({:app, f, a}), do: collect(f) ++ collect(a)

  defp collect({:data, _n, ps, is}),
    do: Enum.flat_map(ps, &collect/1) ++ Enum.flat_map(is, &collect/1)

  defp collect({:ctor, _n, args}), do: Enum.flat_map(args, &collect/1)

  defp collect({:case, s, m, brs}),
    do: collect(s) ++ collect(m) ++ Enum.flat_map(brs, fn {_c, _ar, b} -> collect(b) end)

  defp collect({:let, _g, ty, value, body}),
    do: collect(ty) ++ collect(value) ++ collect(body)

  defp collect({:effect_type, inner}), do: collect(inner)
  defp collect({:effect_pure, value}), do: collect(value)
  defp collect({:effect_bind, effect, continuation}), do: collect(effect) ++ collect(continuation)

  # Fail closed, like `Validator.children/1` and `Certificate.walk_node/4`: descend into
  # every element of an unrecognized node that is itself a term-tuple or a list of them.
  # The catch-all used to answer `[]` — "no globals here" — for any shape this list does not
  # name, so a global reachable only through such a node never entered the closure and was
  # never submitted for certification. That is a totality hole, not a missed optimisation.
  # Genuine leaves (`{:var,_}`, `{:type,_}`, `{:int_lit,_}`) carry only atoms and integers
  # and yield nothing.
  defp collect(term) when is_tuple(term) do
    term
    |> Tuple.to_list()
    |> Enum.flat_map(fn
      child when is_tuple(child) -> collect(child)
      children when is_list(children) -> Enum.flat_map(children, &collect_child/1)
      _leaf -> []
    end)
  end

  defp collect(_), do: []

  defp collect_child(child) when is_tuple(child), do: collect(child)
  defp collect_child(_other), do: []
end
