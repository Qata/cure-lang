defmodule Antigen.Runner do
  @moduledoc "Explore / generate / replay orchestration (spec §8)."
  alias Antigen.{Backend, Corpus, Report, Challenge, Coverage}
  alias Cure.Core.Term

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

    %{infections: final.infections, seeds_banked: final.seeds_banked, health: summarize(final, count)}
  end

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
