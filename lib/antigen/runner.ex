defmodule Antigen.Runner do
  @moduledoc "Explore / generate / replay orchestration (spec §8)."
  alias Antigen.{Backend, Corpus, Report, Challenge, Coverage}
  alias Cure.Core.Term

  # Health-gate floors (spec §8), scoped to the :typed_term subset for
  # binder-usage / reduction-activity; discard rate keeps its whole-run scope.
  @binder_usage_floor 0.60
  @reduction_activity_floor 0.25
  @discard_floor 0.10

  def explore(opts) do
    count = Keyword.get(opts, :count, 200)
    challenges = draw(opts[:gen], count)

    final =
      Enum.reduce(challenges, %{infections: 0, seeds_banked: 0, discards: 0, coverage: MapSet.new()}, fn c, acc ->
        c = %{c | seed: seed_of(c)}

        if well_formed?(c) do
          acc = %{acc | coverage: MapSet.union(acc.coverage, coverage_flags(c))}
          acc = bank_seed(c, opts, acc)

          case apply(opts[:assay] || assay_module(c.assay), :run, [c]) do
            :ok ->
              acc

            {:violation, _detail} = v ->
              {:ok, path} = Report.write_infection(opts[:report_dir], c, v, summarize(acc, count))
              IO.puts(Report.breadcrumb(c, path))
              Corpus.append(opts[:corpus_path], c, Corpus.dedup_key(c, :antibody))
              %{acc | infections: acc.infections + 1}
          end
        else
          %{acc | discards: acc.discards + 1}
        end
      end)

    metrics = health_metrics(challenges)
    discard_rate = final.discards / max(count, 1)
    stamp = health_stamp(metrics, discard_rate)

    IO.puts(
      "antigen health[typed_term]: binder_usage=#{Float.round(metrics.binder_usage, 2)} " <>
        "reduction_activity=#{Float.round(metrics.reduction_activity, 2)} " <>
        "fuel_exhausted=#{metrics.fuel_exhausted_count} discard=#{Float.round(discard_rate, 2)} → #{stamp}"
    )

    mm = mutation_metrics(challenges)

    if mm.mutants_total > 0 do
      IO.puts(
        "antigen health[mutant_term]: reason_diversity=#{mm.reason_diversity} " <>
          "max_depth=#{mm.max_depth} wrap_diversity=#{mm.wrap_diversity} " <>
          "survivors=#{mm.survivors} → #{mutation_stamp(mm)}"
      )
    end

    cm = conversion_metrics(challenges)

    if cm.conv_reject_count + cm.conv_accept_count > 0 do
      IO.puts(
        "antigen health[conversion]: carriers=#{cm.conv_carrier_diversity} " <>
          "both_polarities=#{cm.conv_both_polarities} " <>
          "reject=#{cm.conv_reject_count} accept=#{cm.conv_accept_count} → #{conversion_stamp(cm)}"
      )
    end

    %{
      infections: final.infections,
      seeds_banked: final.seeds_banked,
      health: summarize(final, count),
      health_metrics: metrics,
      stamp: stamp
    }
  end

  @doc """
  Health metrics over the :typed_term subset (spec §8): binder-usage and
  reduction-activity are scoped to :typed_term only; fuel-exhausted nf results
  are counted separately and excluded from reduction-activity.
  """
  def health_metrics(challenges) do
    tts = Enum.filter(challenges, &match?(%Challenge{kind: :typed_term}, &1))
    terms = Enum.map(tts, fn c -> c.payload.term end)

    {used, total} =
      Enum.reduce(terms, {0, 0}, fn t, {u, tot} ->
        {tu, tt} = binder_stats(t)
        {u + tu, tot + tt}
      end)

    {fired, denom, fuel_out} =
      Enum.reduce(tts, {0, 0, 0}, fn c, {f, d, fx} ->
        env = Antigen.Generators.SigMenu.env_of(c.payload.sig)
        ctx = Antigen.Generators.SigMenu.rebuild_context(env, c.payload.ctx)

        # `fuel: ...` matters here for the same reason it does in Assays.Term:
        # the 2-arg call defaults to :infinity, which would make
        # `fuel_exhausted_count` permanently 0 regardless of the corpus. Reuse
        # Assays.Term's committed constant rather than inventing a second one.
        case Cure.Core.Normalise.nf(ctx, c.payload.term, fuel: Antigen.Assays.Term.assay_fuel()) do
          :fuel_exhausted -> {f, d, fx + 1}
          nf -> {f + (if nf != c.payload.term, do: 1, else: 0), d + 1, fx}
        end
      end)

    %{
      binder_usage: safe_ratio(used, total),
      reduction_activity: safe_ratio(fired, denom),
      fuel_exhausted_count: fuel_out
    }
  end

  def health_stamp(metrics, discard_rate) do
    if metrics.binder_usage >= @binder_usage_floor and
         metrics.reduction_activity >= @reduction_activity_floor and
         discard_rate < @discard_floor,
       do: :healthy,
       else: :vacuous
  end

  @mutation_diversity_floor 5
  @depth_floor 4
  @wrap_floor 4

  @doc """
  Vacuity metrics over the :mutant_term subset: fault-kind diversity (spec §6.2),
  plus deep-propagation generation-quality signals `max_depth` / `wrap_diversity`.

  `reason_diversity` is scoped to correctly-REJECTED mutants; `max_depth` and
  `wrap_diversity` are generation-time properties computed over EVERY mutant
  (survivors included — excluding them would hide exactly the slice the gate needs).
  Legacy v1 seeds predate `:depth`/`:wrap_path`, so both are read defensively.
  """
  def mutation_metrics(challenges) do
    ms = Enum.filter(challenges, &match?(%Challenge{kind: :mutant_term}, &1))

    {rejected_kinds, survivors} =
      Enum.reduce(ms, {MapSet.new(), 0}, fn c, {kinds, surv} ->
        case Antigen.Assays.Mutation.run(c) do
          :ok -> {MapSet.put(kinds, c.payload.fault.kind), surv}
          {:violation, _} -> {kinds, surv + 1}
        end
      end)

    depths = Enum.map(ms, fn c -> Map.get(c.payload.fault, :depth, 0) end)
    wraps = ms |> Enum.flat_map(fn c -> Map.get(c.payload.fault, :wrap_path, []) end) |> MapSet.new()

    %{
      reason_diversity: MapSet.size(rejected_kinds),
      survivors: survivors,
      mutants_total: length(ms),
      max_depth: Enum.max([0 | depths]),
      wrap_diversity: MapSet.size(wraps)
    }
  end

  @doc """
  Vacuity stamp: diversity + depth + wrapper-diversity floors. Survivors are an
  infection, surfaced separately, never folded into the stamp (spec §6.2 rule).
  """
  def mutation_stamp(%{reason_diversity: d, max_depth: md, wrap_diversity: wd}),
    do:
      if(d >= @mutation_diversity_floor and md >= @depth_floor and wd >= @wrap_floor,
        do: :healthy,
        else: :vacuous
      )

  @conv_carrier_floor 2

  @doc """
  Structural carrier tag of a `:typed_term` conversion accept carrier, or nil.
  Accept challenges are ordinary `:typed_term`s (no fault field), so the conversion
  subset must be recognised by term shape. Safe in v1: the ordinary `Term` generator
  never emits a `plus`-headed Vec index (spec §6).
  """
  def conv_carrier_of(%Challenge{kind: :typed_term, payload: %{term: t}}) do
    case t do
      {:ctor, :vcons, [{:app, {:app, {:global, :plus}, _}, _}, _, _]} -> :conv_index
      {:case, _, {:lam, _, {:data, :Vec, _, [{:app, {:app, {:global, :plus}, _}, _}]}}, _} -> :conv_motive
      _ -> nil
    end
  end

  def conv_carrier_of(_), do: nil

  @doc "Conversion-subset vacuity metrics over both polarities (spec §6)."
  def conversion_metrics(challenges) do
    rej =
      challenges
      |> Enum.filter(fn c ->
        match?(%Challenge{kind: :mutant_term}, c) and Map.get(c.payload.fault, :witness) == :conv
      end)
      |> Enum.map(fn c -> c.payload.fault.carrier end)

    acc = challenges |> Enum.map(&conv_carrier_of/1) |> Enum.reject(&is_nil/1)

    %{
      conv_carrier_diversity: MapSet.size(MapSet.new(rej ++ acc)),
      conv_both_polarities: rej != [] and acc != [],
      conv_reject_count: length(rej),
      conv_accept_count: length(acc)
    }
  end

  def conversion_stamp(%{conv_carrier_diversity: d, conv_both_polarities: both}),
    do: if(d >= @conv_carrier_floor and both, do: :healthy, else: :vacuous)

  # Count binders (lam / case-branch) and how many bind a variable that occurs.
  defp binder_stats(t), do: binder_stats(t, {0, 0})

  defp binder_stats({:lam, _dom, body}, {u, tot}) do
    used = if occurs?(body, 0), do: 1, else: 0
    binder_stats(body, {u + used, tot + 1})
  end

  defp binder_stats({:case, scrut, _motive, branches}, acc) do
    # The motive is a type-level annotation the generator supplies (v1 uses a
    # constant motive whose binder is by construction unused), NOT a generated
    # term binder — spec §8's metric counts "lam / case-branch binders", so the
    # motive is deliberately excluded rather than dragging binder-usage down.
    acc = binder_stats(scrut, acc)

    Enum.reduce(branches, acc, fn {_c, arity, body}, {u, tot} ->
      used = if arity > 0 and Enum.any?(0..(arity - 1)//1, &occurs?(body, &1)), do: 1, else: 0
      tot2 = if arity > 0, do: tot + 1, else: tot
      binder_stats(body, {u + used, tot2})
    end)
  end

  defp binder_stats(t, acc) when is_tuple(t) do
    t |> Tuple.to_list() |> tl() |> Enum.reduce(acc, &binder_stats/2)
  end

  defp binder_stats(l, acc) when is_list(l), do: Enum.reduce(l, acc, &binder_stats/2)
  defp binder_stats(_leaf, acc), do: acc

  # Does de Bruijn index `k` occur free in `t`? (crosses binders by incrementing k)
  defp occurs?({:var, k}, k), do: true
  defp occurs?({:var, _}, _k), do: false
  defp occurs?({:lam, dom, body}, k), do: occurs?(dom, k) or occurs?(body, k + 1)
  defp occurs?({:pi, dom, cod}, k), do: occurs?(dom, k) or occurs?(cod, k + 1)
  defp occurs?({:sigma, a, b}, k), do: occurs?(a, k) or occurs?(b, k + 1)

  defp occurs?({:case, scrut, motive, branches}, k) do
    # `motive` is itself a `:lam`-headed term (spec §6.5's constant-motive
    # convention); its extra binder lives inside its own `:lam` node and is
    # handled by the `:lam` clause, so motive stays at the SAME `k` here.
    occurs?(scrut, k) or occurs?(motive, k) or
      Enum.any?(branches, fn {_c, arity, body} -> occurs?(body, k + arity) end)
  end

  defp occurs?(t, k) when is_tuple(t), do: t |> Tuple.to_list() |> tl() |> Enum.any?(&occurs?(&1, k))
  defp occurs?(l, k) when is_list(l), do: Enum.any?(l, &occurs?(&1, k))
  defp occurs?(_leaf, _k), do: false

  defp safe_ratio(_num, 0), do: 1.0
  defp safe_ratio(num, den), do: num / den

  def generate(opts) do
    count = Keyword.get(opts, :count, 200)

    draw(opts[:gen], count)
    |> Enum.reduce(%{seeds_banked: 0}, fn c, acc -> bank_seed(%{c | seed: seed_of(c)}, opts, acc) end)
    |> Map.take([:seeds_banked])
  end

  def replay(paths, assays) do
    Enum.flat_map(paths, fn path ->
      Corpus.stream(path)
      |> Enum.map(fn
        {:ok, c} ->
          verdict =
            case Map.fetch(assays, c.assay) do
              {:ok, mod} -> apply(mod, :run, [c])
              :error -> {:violation, {:unknown_assay, c.assay}}
            end

          %{entry: c, verdict: verdict}

        {:decode_error, line, reason} ->
          %{entry: line, verdict: {:decode_error, line, reason}}
      end)
    end)
  end

  def replay_one(%Challenge{assay: a} = c), do: apply(assay_module(a), :run, [c])

  # The assay registry: challenge assay-id → assay module.
  defp assay_module("stub"), do: Antigen.Assays.Stub
  defp assay_module("totality/diverging"), do: Antigen.Assays.Totality
  defp assay_module("totality/terminating"), do: Antigen.Assays.Totality
  defp assay_module("positivity"), do: Antigen.Assays.Positivity
  defp assay_module("reflexivity"), do: Antigen.Assays.Reflexivity
  defp assay_module("indexed/case"), do: Antigen.Assays.Indexed
  defp assay_module("rewrite/eq"), do: Antigen.Assays.Rewrite
  defp assay_module("universes"), do: Antigen.Assays.Universes
  defp assay_module("stuck_elim_delta"), do: Antigen.Assays.StuckElimDelta
  defp assay_module("term/infer_check"), do: Antigen.Assays.Term
  defp assay_module("term/subject_reduction"), do: Antigen.Assays.Term
  defp assay_module("term/normalization"), do: Antigen.Assays.Term
  defp assay_module("mutation/rejection"), do: Antigen.Assays.Mutation
  defp assay_module("elab/completeness"), do: Antigen.Assays.Elab
  defp assay_module("elab/metamorphic"), do: Antigen.Assays.Elab

  @doc "Public view of the assay registry (for tests)."
  def assay_module_for(assay_id), do: assay_module(assay_id)

  defp bank_seed(c, opts, acc) do
    case Corpus.append(opts[:seeds_path], c, Corpus.dedup_key(c, :seed)) do
      :appended -> %{acc | seeds_banked: acc.seeds_banked + 1}
      :duplicate -> acc
    end
  end

  defp draw(gen, count), do: Backend.StreamData.interp(gen) |> Enum.take(count)
  defp seed_of(c), do: c.seed || :erlang.phash2({c.kind, c.payload})

  # Health gate (spec §9): discard rate (malformed candidates) + coverage buckets
  # (the binder-shape flags actually hit). Reported, never hard-failed.
  defp summarize(acc, count), do: %{discard_rate: acc.discards / max(count, 1), coverage: acc.coverage}

  defp coverage_flags(c) do
    {_ctors, _bucket, flags, _label} = Coverage.key(c)
    flags
  end

  # A generator-quality failure: a candidate whose Core terms aren't well-formed.
  # Distinct from a coverage-duplicate rejection (which is expected, not a discard).
  defp well_formed?(c) do
    c |> Coverage.terms_of() |> Enum.all?(&Term.term?/1)
  rescue
    _ -> false
  end
end
