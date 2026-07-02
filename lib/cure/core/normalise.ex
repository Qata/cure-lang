defmodule Cure.Core.Normalise do
  @moduledoc """
  Trusted normalization service for Core terms.

  Evaluation and read-back remain split across `Cure.Core.Eval` and
  `Cure.Core.Quote`; this module is the trusted owner of the policy between
  them: certified δ-unfolding, weak-head reduction, full normal forms, and the
  deterministic δ fuel counter used by conversion.
  """

  alias Cure.Core.{Context, Env, Eval, Quote}

  @fuel_key {__MODULE__, :fuel}

  @type delta_mode :: :certified | :none
  @type fuel :: pos_integer() | :infinity
  @type opts :: [
          delta: delta_mode(),
          mode: :whnf | :nf,
          fuel: fuel(),
          stuck_cases: :preserve
        ]

  @doc "Reduce `term` to weak-head normal form in `ctx` and read it back."
  @spec whnf(Context.t(), Cure.Core.Term.t(), opts()) :: Cure.Core.Term.t() | :fuel_exhausted
  def whnf(ctx, term, opts \\ []) do
    run_with_fuel(Keyword.put(opts, :mode, :whnf), fn opts ->
      ctx
      |> eval_in(term)
      |> whnf_value(Context.signature(ctx), opts)
      |> Quote.reify(Context.length(ctx))
    end)
  end

  @doc "Reduce `term` to normal form in `ctx` and read it back."
  @spec nf(Context.t(), Cure.Core.Term.t(), opts()) :: Cure.Core.Term.t() | :fuel_exhausted
  def nf(ctx, term, opts \\ []) do
    run_with_fuel(Keyword.put(opts, :mode, :nf), fn opts ->
      ctx
      |> eval_in(term)
      |> nf_value(Context.signature(ctx), Context.length(ctx), opts)
      |> Quote.reify(Context.length(ctx))
    end)
  end

  @doc "Read a semantic value back to a Core term."
  @spec quote(Cure.Core.Value.t(), non_neg_integer(), opts()) :: Cure.Core.Term.t()
  def quote(value, depth, _opts \\ []), do: Quote.reify(value, depth)

  @doc false
  @spec whnf_value(Cure.Core.Value.t(), Env.t() | nil, opts()) :: Cure.Core.Value.t()
  def whnf_value(value, sig, opts \\ [])

  def whnf_value(value, nil, _opts), do: value

  def whnf_value({:vneutral, neutral} = value, sig, opts) do
    opts = normalize_opts(opts)

    case unfold_head(neutral, sig, opts) do
      {:ok, reduced} -> whnf_value(reduced, sig, opts)
      :stuck -> value
    end
  end

  def whnf_value(value, _sig, _opts), do: value

  @doc false
  @spec with_fuel(fuel(), (-> term())) :: term() | :fuel_exhausted
  def with_fuel(:infinity, fun), do: fun.()

  def with_fuel(fuel, fun) when is_integer(fuel) and fuel > 0 do
    Process.put(@fuel_key, fuel)

    try do
      fun.()
    catch
      :throw, {@fuel_key, :exhausted} -> :fuel_exhausted
    after
      Process.delete(@fuel_key)
    end
  end

  @doc false
  @spec fuel_key() :: term()
  def fuel_key, do: @fuel_key

  defp eval_in(ctx, term), do: Eval.eval(term, Context.env(ctx))

  defp run_with_fuel(opts, fun) do
    opts = normalize_opts(opts)
    with_fuel(opts[:fuel], fn -> fun.(opts) end)
  end

  defp normalize_opts(opts) do
    opts =
      opts
      |> Keyword.put_new(:delta, :certified)
      |> Keyword.put_new(:mode, :nf)
      |> Keyword.put_new(:fuel, :infinity)
      |> Keyword.put_new(:stuck_cases, :preserve)

    delta = Keyword.fetch!(opts, :delta)
    mode = Keyword.fetch!(opts, :mode)
    fuel = Keyword.fetch!(opts, :fuel)
    :preserve = Keyword.fetch!(opts, :stuck_cases)

    unless delta in [:certified, :none] do
      raise ArgumentError, "expected :delta to be :certified or :none, got: #{inspect(delta)}"
    end

    unless mode in [:whnf, :nf] do
      raise ArgumentError, "expected :mode to be :whnf or :nf, got: #{inspect(mode)}"
    end

    unless fuel == :infinity or (is_integer(fuel) and fuel > 0) do
      raise ArgumentError, "expected :fuel to be a positive integer or :infinity, got: #{inspect(fuel)}"
    end

    opts
  rescue
    MatchError ->
      raise ArgumentError,
            "expected normalization options delta: :certified | :none, mode: :whnf | :nf, " <>
              "fuel: pos_integer() | :infinity, stuck_cases: :preserve"
  end

  defp nf_value(value, sig, depth, opts) do
    value
    |> whnf_value(sig, opts)
    |> nf_struct(sig, depth, opts)
  end

  defp nf_struct({:vpi, dom, {:closure, env, cod}}, sig, depth, opts) do
    fresh = {:vneutral, {:nvar, depth}}

    {:vpi, nf_value(dom, sig, depth, opts),
     {:closure, [], quote_nf(Eval.eval(cod, [fresh | env]), sig, depth + 1, opts)}}
  end

  defp nf_struct({:vlam, dom, {:closure, env, body}}, sig, depth, opts) do
    fresh = {:vneutral, {:nvar, depth}}

    {:vlam, nf_value(dom, sig, depth, opts),
     {:closure, [], quote_nf(Eval.eval(body, [fresh | env]), sig, depth + 1, opts)}}
  end

  defp nf_struct({:vsigma, dom, {:closure, env, cod}}, sig, depth, opts) do
    fresh = {:vneutral, {:nvar, depth}}

    {:vsigma, nf_value(dom, sig, depth, opts),
     {:closure, [], quote_nf(Eval.eval(cod, [fresh | env]), sig, depth + 1, opts)}}
  end

  defp nf_struct({:vpair, a, b}, sig, depth, opts),
    do: {:vpair, nf_value(a, sig, depth, opts), nf_value(b, sig, depth, opts)}

  defp nf_struct({:vdata, name, args}, sig, depth, opts),
    do: {:vdata, name, Enum.map(args, &nf_value(&1, sig, depth, opts))}

  defp nf_struct({:vctor, name, args}, sig, depth, opts),
    do: {:vctor, name, Enum.map(args, &nf_value(&1, sig, depth, opts))}

  defp nf_struct({:veq, ty, a, b}, sig, depth, opts),
    do: {:veq, nf_value(ty, sig, depth, opts), nf_value(a, sig, depth, opts), nf_value(b, sig, depth, opts)}

  defp nf_struct({:vrefl, a}, sig, depth, opts), do: {:vrefl, nf_value(a, sig, depth, opts)}

  defp nf_struct({:vneutral, neutral}, sig, depth, opts),
    do: {:vneutral, nf_neutral(neutral, sig, depth, opts)}

  defp nf_struct(value, _sig, _depth, _opts), do: value

  defp nf_neutral({:napp, neutral, arg}, sig, depth, opts),
    do: {:napp, nf_neutral(neutral, sig, depth, opts), nf_value(arg, sig, depth, opts)}

  defp nf_neutral({:nfst, neutral}, sig, depth, opts), do: {:nfst, nf_neutral(neutral, sig, depth, opts)}
  defp nf_neutral({:nsnd, neutral}, sig, depth, opts), do: {:nsnd, nf_neutral(neutral, sig, depth, opts)}

  defp nf_neutral({:nprim, op, args}, sig, depth, opts),
    do: {:nprim, op, Enum.map(args, &nf_value(&1, sig, depth, opts))}

  defp nf_neutral({:ncase, neutral, motive, branches}, sig, depth, opts) do
    {:ncase, nf_neutral(neutral, sig, depth, opts), motive, branches}
  end

  defp nf_neutral(neutral, _sig, _depth, _opts), do: neutral

  defp quote_nf(value, sig, depth, opts), do: value |> nf_value(sig, depth, opts) |> Quote.reify(depth)

  defp unfold_head(neutral, sig, opts) do
    if opts[:delta] == :none do
      :stuck
    else
      unfold_certified_head(neutral, sig, opts)
    end
  end

  # δ-reduce a neutral's spine head when that head is either a certified-total
  # global OR a *stuck eliminator* (`ncase`/`nfst`/`nsnd`) whose target itself
  # δ-reduces to a constructor/pair. In the eliminator case we whnf the target
  # (threading the caller's `opts`, so `delta: :none` and fuel/mode are honored)
  # and, when a value emerges, apply the SAME ι-rule `eval` trusts, then re-apply
  # the spine `args`. Each ι-reduction spends fuel so termination stays bounded.
  defp unfold_certified_head(neutral, sig, opts) do
    {head, args} = spine(neutral, [])

    case head do
      {:nglobal, name} ->
        if Env.certified?(sig, name) do
          %{body: body} = Env.get_def(sig, name)
          {:ok, reapply(args, spend_fuel(Eval.eval(body, [])))}
        else
          :stuck
        end

      # ι on `case`: mirrors the ctor branch of `eval({:case,…})` — reduce the
      # matching branch body in `reverse(cargs) ++ env`.
      {:ncase, scrut, _motive, branches} ->
        case whnf_value({:vneutral, scrut}, sig, opts) do
          {:vctor, cname, cargs} ->
            {_c, _ar, {:closure, env, body}} =
              Enum.find(branches, fn {c, _ar, _b} -> c == cname end)

            reduced = spend_fuel(Eval.eval(body, Enum.reverse(cargs) ++ env))
            {:ok, reapply(args, reduced)}

          _ ->
            :stuck
        end

      # ι on projections: mirrors `vfst`/`vsnd` — the pair's first/second field.
      {:nfst, target} ->
        case whnf_value({:vneutral, target}, sig, opts) do
          {:vpair, a, _b} -> {:ok, reapply(args, spend_fuel(a))}
          _ -> :stuck
        end

      {:nsnd, target} ->
        case whnf_value({:vneutral, target}, sig, opts) do
          {:vpair, _a, b} -> {:ok, reapply(args, spend_fuel(b))}
          _ -> :stuck
        end

      _ ->
        :stuck
    end
  end

  defp reapply(args, value), do: Enum.reduce(args, value, fn arg, acc -> Eval.apply(acc, arg) end)

  defp spend_fuel(reduced) do
    case Process.get(@fuel_key) do
      nil ->
        reduced

      0 ->
        throw({@fuel_key, :exhausted})

      n ->
        Process.put(@fuel_key, n - 1)
        reduced
    end
  end

  defp spine({:napp, n, arg}, acc), do: spine(n, [arg | acc])
  defp spine(head, acc), do: {head, acc}
end
