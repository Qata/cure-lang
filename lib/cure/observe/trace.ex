defmodule Cure.Observe.Trace do
  @moduledoc """
  Typed tracer for Cure (v0.27.0).

  Thin wrapper around OTP's `:dbg` that formats traced calls and
  returns through `inspect/2` and, where a compile-time signature is
  known, annotates each argument with its declared Cure type.

  ## Usage

      iex> Cure.Observe.Trace.start({Cure.Std.List, :map, 2})
      iex> # ... exercise the system ...
      iex> Cure.Observe.Trace.stop()

  From the command line:

      mix cure.trace Cure.Std.List.map/2

  ## Tracing compiler internals

  `:dbg.tpl` traces LOCAL (private) functions too, so the same tracer pins where a
  compiler pass makes a decision or returns an error — point it at
  `Cure.Elab.*` / `Cure.Core.*`. Two things make that practical:

    * pass a LIST of `{module, fun, arity}` to trace a whole path in one run;
    * cap the noise — elaborator arguments carry the full `Env`/`Context`, so the
      default `:limit`/`:printable_limit` keep each line short (override for detail).

  To pin the ORIGIN of a rejection, add `only_errors: true`: only `{:error, _}`
  returns are printed (calls and `return_to` are suppressed), so the first line is
  the innermost pass that produced the error.

  ## Filters / options

  `start/2` accepts:

    * `:only_errors` -- boolean; print only `{:error, _}` return values (pins where
      a rejection originates). Default `false`.
    * `:limit`       -- `inspect/2` `:limit` for args/returns. Default `8`
      (`:infinity` for full detail).
    * `:printable_limit` -- `inspect/2` `:printable_limit`. Default `120`.
    * `:effect`      -- atom; only surface calls whose declared effect set contains
      the given effect.
    * `:format`      -- `:plain` (default) or `:marcli` for ANSI colour.
    * `:self`        -- send formatted lines to the calling process as
      `{:cure_trace, text}` messages instead of printing them. Useful for tests.

  ## Registry

  `Cure.Observe.Trace.Registry` is an ETS table keyed by
  `{module, fun, arity}` that stores the declared parameter types
  and effect set, if known. The type checker populates this table
  opportunistically; missing entries mean the tracer falls back to
  raw `inspect/2` output.
  """

  @reg_table :cure_trace_registry

  @doc """
  Start tracing the given `{module, fun, arity}` triple, or a LIST of them (a whole
  call path in one run). Repeated calls replace the current trace spec.
  """
  @spec start({module(), atom(), arity()} | [{module(), atom(), arity()}], keyword()) :: :ok
  def start(mfa_or_list, opts \\ []) do
    ensure_registry()
    ensure_dbg()

    mfas = List.wrap(mfa_or_list)
    target = if Keyword.get(opts, :self, false), do: self(), else: nil

    :dbg.tracer(:process, {&trace_handler/2, %{target: target, opts: opts}})

    # `return_to` is suppressed under `only_errors` (it carries no value); otherwise
    # it shows which caller control unwinds to, which is useful for path tracing.
    flags = if Keyword.get(opts, :only_errors, false), do: [:call], else: [:call, :return_to]
    :dbg.p(:all, flags)

    Enum.each(mfas, fn {module, fun, arity} ->
      :dbg.tpl(module, fun, arity, [{:_, [], [{:return_trace}]}])
    end)

    Process.put({__MODULE__, :active}, mfas)
    :ok
  end

  @doc "Stop the currently active tracer."
  @spec stop() :: :ok
  def stop do
    try do
      :dbg.stop()
    catch
      _, _ -> :ok
    end

    Process.delete({__MODULE__, :active})
    :ok
  end

  @doc """
  Register the type signature for a function. Called by the Cure
  type checker during compile; safe to call at runtime too.
  """
  @spec register_signature({module(), atom(), arity()}, [String.t()], String.t(), [atom()]) :: :ok
  def register_signature({mod, fun, arity}, param_types, ret_type, effects) do
    ensure_registry()
    :ets.insert(@reg_table, {{mod, fun, arity}, param_types, ret_type, effects})
    :ok
  end

  @doc "Look up a registered signature."
  @spec lookup_signature({module(), atom(), arity()}) :: {:ok, map()} | :error
  def lookup_signature(mfa) do
    ensure_registry()

    case :ets.lookup(@reg_table, mfa) do
      [{_, params, ret, effects}] ->
        {:ok, %{params: params, return: ret, effects: effects}}

      [] ->
        :error
    end
  rescue
    ArgumentError -> :error
  end

  # -- Internals --------------------------------------------------------------

  defp ensure_registry do
    case :ets.whereis(@reg_table) do
      :undefined ->
        :ets.new(@reg_table, [:set, :public, :named_table])
        :ok

      _ ->
        :ok
    end
  end

  defp ensure_dbg do
    case Application.ensure_all_started(:runtime_tools) do
      {:ok, _} -> :ok
      _ -> :ok
    end
  end

  @doc false
  def trace_handler(msg, %{target: target, opts: opts} = state) do
    case format(msg, opts) do
      nil ->
        state

      line ->
        cond do
          is_pid(target) -> send(target, {:cure_trace, line})
          true -> IO.puts(line)
        end

        state
    end
  end

  # `only_errors` suppresses everything but `{:error, _}` returns, so the first line
  # printed is the innermost pass that produced the rejection.
  defp format({:trace, _pid, :call, {mod, fun, args}}, opts) when is_list(args) do
    if Keyword.get(opts, :only_errors, false), do: nil, else: format_call({mod, fun, args}, opts)
  end

  defp format({:trace, _pid, :return_from, {mod, fun, arity}, ret}, opts) do
    if Keyword.get(opts, :only_errors, false) and not match?({:error, _}, ret) do
      nil
    else
      mfa = {mod, fun, arity}

      return_type =
        case lookup_signature(mfa) do
          {:ok, %{return: t}} -> " : #{t}"
          :error -> ""
        end

      "return #{mod}.#{fun}/#{arity} -> #{insp(ret, opts)}#{return_type}"
    end
  end

  defp format({:trace, _pid, :return_to, {mod, fun, arity}}, _opts),
    do: "  ↳ returned to #{mod}.#{fun}/#{arity}"

  defp format({:trace, _pid, :return_to, :undefined}, _opts), do: "  ↳ returned to (top level)"

  defp format(_other, _opts), do: nil

  defp format_call({mod, fun, args}, opts) do
    arity = length(args)
    mfa = {mod, fun, arity}
    header = "call #{mod}.#{fun}/#{arity}"

    body =
      case lookup_signature(mfa) do
        {:ok, %{params: params, effects: effects}} ->
          typed =
            args
            |> Enum.zip(params)
            |> Enum.map(fn {a, t} -> "#{insp(a, opts)} : #{t}" end)
            |> Enum.join(", ")

          effects_tag = if effects == [], do: "pure", else: "! " <> Enum.join(effects, ",")
          "#{header}(#{typed})  [#{effects_tag}]"

        :error ->
          "#{header}(#{Enum.map_join(args, ", ", &insp(&1, opts))})"
      end

    _ = Keyword.get(opts, :format, :plain)
    body
  end

  # Compiler-internal args carry the full `Env`/`Context`; cap them so a line is
  # readable. `:infinity` restores full detail.
  defp insp(term, opts) do
    inspect(term,
      limit: Keyword.get(opts, :limit, 8),
      printable_limit: Keyword.get(opts, :printable_limit, 120)
    )
  end
end
