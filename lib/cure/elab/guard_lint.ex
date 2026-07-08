defmodule Cure.Elab.GuardLint do
  @moduledoc """
  Untrusted Z3 guard-coverage lint (spec 2026-07-08-guard-coverage-lint).

  Two queries over ELABORATED guard Core terms (always with their typing
  `Context`, because the fragment is Int-only and must see operand types):

    * `prove_exhaustive/2` — is the disjunction of the guards valid? `:proven`
      lets `guard_chain` accept a final guarded arm as the catch-all (its test
      elided; the kernel re-checks the emitted term as always — §2.3a). Every
      failure mode (refuted / unknown / timeout / untranslatable / Z3 absent)
      is `:not_proven`, leaving behavior byte-identical to pre-lint.
    * `shadowed?/3` — is a guard implied by the disjunction of the guards
      before it (its arm dead)? Only ever produces a warning.

  Translation fragment (§2.2): `{:prim, cmp, [a, b]}` over Int-typed operands
  (vars checked against the Context, `{:int_lit, _}`, linear `add/sub/mul`),
  plus literal `True`/`False`. Anything else falls back to an uninterpreted
  Bool constant interned BY TERM — identical untranslatable guards share a
  constant (so shadow detection catches a literal repeat), distinct ones do
  not, and an uninterpreted constant can never make a disjunction valid, so
  exhaustiveness can never lean on one (K13: untranslatable ⇒ not proven).

  Z3 is OUT of the TCB: nothing here influences a kernel judgement (locked
  SMT trust-boundary decision). Warnings ride a process-dictionary list reset
  by `Cure.Elab.Program.elaborate/1` (§2.5) — not an `Env` field.
  """

  alias Cure.Core.Context
  alias Cure.SMT.Process, as: Z3

  @warnings_key :cure_guard_lint_warnings
  @timeout 3_000

  # -- Warnings channel (§2.5) -------------------------------------------------

  def reset_warnings, do: Process.put(@warnings_key, [])

  def record_warning(w), do: Process.put(@warnings_key, [w | Process.get(@warnings_key, [])])

  def warnings, do: Process.get(@warnings_key, []) |> Enum.reverse()

  # -- Lint queries -------------------------------------------------------------

  @spec prove_exhaustive([tuple()], Context.t()) :: :proven | :not_proven
  def prove_exhaustive([], _ctx), do: :not_proven

  def prove_exhaustive(guards, ctx) do
    {forms, st} = render_guards(guards, ctx)

    case check_sat("(assert (not " <> disj(forms) <> "))", st) do
      :unsat -> :proven
      _ -> :not_proven
    end
  end

  @spec shadowed?(tuple(), [tuple()], Context.t()) :: boolean()
  def shadowed?(_guard, [], _ctx), do: false

  def shadowed?(guard, prior, ctx) do
    {[g | ps], st} = render_guards([guard | prior], ctx)

    case check_sat("(assert (and " <> g <> " (not " <> disj(ps) <> ")))", st) do
      :unsat -> true
      _ -> false
    end
  end

  # -- Rendering (§2.2) ----------------------------------------------------------

  defp disj([f]), do: f
  defp disj(fs), do: "(or " <> Enum.join(fs, " ") <> ")"

  defp render_guards(guards, ctx) do
    Enum.map_reduce(guards, %{ints: MapSet.new(), atoms: %{}}, fn g, st ->
      case bool_form(g, ctx, st) do
        {:ok, s, st1} ->
          {s, st1}

        :error ->
          case Map.fetch(st.atoms, g) do
            {:ok, name} ->
              {name, st}

            :error ->
              name = "u" <> Integer.to_string(map_size(st.atoms))
              {name, %{st | atoms: Map.put(st.atoms, g, name)}}
          end
      end
    end)
  end

  @cmp %{lt: "<", le: "<=", gt: ">", ge: ">=", eq: "=", ne: "distinct"}

  defp bool_form({:prim, op, [a, b]}, ctx, st) when is_map_key(@cmp, op) do
    with {:ok, sa, st} <- int_form(a, ctx, st),
         {:ok, sb, st} <- int_form(b, ctx, st) do
      {:ok, "(" <> Map.fetch!(@cmp, op) <> " " <> sa <> " " <> sb <> ")", st}
    else
      _ -> :error
    end
  end

  defp bool_form({:ctor, :True, []}, _ctx, st), do: {:ok, "true", st}
  defp bool_form({:ctor, :False, []}, _ctx, st), do: {:ok, "false", st}
  defp bool_form(_other, _ctx, _st), do: :error

  defp int_form({:int_lit, n}, _ctx, st), do: {:ok, int_lit(n), st}

  defp int_form({:var, i}, ctx, st) do
    case Context.lookup(ctx, i) do
      {:vint_type} -> {:ok, var_name(i), %{st | ints: MapSet.put(st.ints, i)}}
      _ -> :error
    end
  end

  # Keep the fragment linear: `mul` needs a literal multiplicand.
  defp int_form({:prim, :mul, [a, b]}, ctx, st) do
    if match?({:int_lit, _}, a) or match?({:int_lit, _}, b),
      do: arith("*", a, b, ctx, st),
      else: :error
  end

  defp int_form({:prim, :add, [a, b]}, ctx, st), do: arith("+", a, b, ctx, st)
  defp int_form({:prim, :sub, [a, b]}, ctx, st), do: arith("-", a, b, ctx, st)
  defp int_form(_other, _ctx, _st), do: :error

  defp arith(sym, a, b, ctx, st) do
    with {:ok, sa, st} <- int_form(a, ctx, st),
         {:ok, sb, st} <- int_form(b, ctx, st) do
      {:ok, "(" <> sym <> " " <> sa <> " " <> sb <> ")", st}
    else
      _ -> :error
    end
  end

  defp int_lit(n) when n < 0, do: "(- " <> Integer.to_string(-n) <> ")"
  defp int_lit(n), do: Integer.to_string(n)

  defp var_name(i), do: "v" <> Integer.to_string(i)

  # -- Z3 execution (§2.4: reuse Cure.SMT.Process ONLY) --------------------------

  defp check_sat(assertion, st) do
    decls =
      Enum.map(Enum.sort(MapSet.to_list(st.ints)), &("(declare-const " <> var_name(&1) <> " Int)")) ++
        Enum.map(Enum.sort(Map.values(st.atoms)), &("(declare-const " <> &1 <> " Bool)"))

    query = Enum.join(decls ++ [assertion, "(check-sat)"], "\n")

    if Z3.z3_available?() do
      run_isolated(fn -> Z3.start_link(timeout: @timeout) end, query)
    else
      :unknown
    end
  end

  # `Cure.SMT.Process.start_link` LINKS the solver GenServer to US (the
  # elaborator/test process). A Z3 binary crash/kill is captured as an ordinary
  # `:exit_status` port message inside `Process`'s own `handle_call` and replied
  # as `{:error, _}` — no crash. But a genuine bug INSIDE the `Process` GenServer
  # (an unhandled message, an exception in its own receive loop) terminates that
  # linked process abnormally, and the resulting EXIT SIGNAL is not something any
  # `try/catch` in our code can intercept — with `trap_exit` at its default
  # `false`, an unhandled linked EXIT kills the receiving process outright,
  # bypassing ordinary exception handling entirely (this is a real per-`Cure.SMT.Process`
  # gap: `Cure.SMT.Solver.run_with_z3` has the identical exposure and no extra
  # guard against it either — but that pipeline is opt-in refinement checking,
  # while this lint sits on every `Program.elaborate/1` call, where spec §3 make
  # "must never crash an elaboration" an absolute, so we harden past parity with
  # the existing caller rather than merely matching it). Toggling `trap_exit` for
  # the duration of the query turns any such crash into an ordinary `{:EXIT, pid,
  # reason}` message we explicitly drain and fold into `:unknown`, instead of
  # letting it kill the caller. Residual, accepted trade-off: for the query's
  # brief window (≤ `@timeout`), an UNRELATED linked process crashing also
  # arrives as a mailbox message instead of killing us; we only drain the one
  # tagged with our own `pid`, so an unrelated `{:EXIT, _, _}` is left queued as
  # ordinary (harmless, since this call runs in an ordinary synchronous
  # process, not a `handle_info` loop expecting none) rather than propagating —
  # acceptable given the alternative (Z3 crashing the elaborator) is strictly
  # worse and the window is short.
  defp run_isolated(start_fun, query) do
    prior = Process.flag(:trap_exit, true)

    try do
      case start_fun.() do
        {:ok, pid} ->
          try do
            case Z3.query(pid, query) do
              {:unsat, _} -> :unsat
              {:sat, _} -> :sat
              _ -> :unknown
            end
          catch
            # A dead port / call timeout / trapped linked crash degrades
            # conservatively (§2.3, §3).
            _, _ -> :unknown
          after
            try do
              Z3.stop(pid)
            catch
              _, _ -> :ok
            end

            # Drain the EXIT message `stop/1` (a normal GenServer.stop) or a
            # crash may have queued, so it never leaks into the caller's own
            # mailbox once trap_exit is restored below.
            receive do
              {:EXIT, ^pid, _} -> :ok
            after
              0 -> :ok
            end
          end

        _ ->
          :unknown
      end
    after
      Process.flag(:trap_exit, prior)
    end
  end
end
