defmodule Antigen.Cover do
  @moduledoc "Erlang :cover harness for kernel code coverage (Antigen tooling; no TCB changes)."

  @cover_modules [Cure.Core.Kernel, Cure.Core.Normalise, Cure.Core.Conv,
                  Cure.Core.Eval, Cure.Core.Quote, Cure.Core.Inductive,
                  Cure.Core.Serialize, Cure.Core.Certificate]
  def cover_modules, do: @cover_modules

  @doc """
  True if `module`'s beam carries real abstract_code (required by both
  :cover.compile_beam AND Task 3's function_index; :cover.analyse needs the
  former, cold-line→function mapping needs the latter — same underlying chunk).

  MUST inspect the chunk's inner VALUE, not just that :beam_lib.chunks/2
  returned :ok — confirmed against OTP: :beam_lib.chunks(beam, [:abstract_code])
  ALWAYS returns {:ok, {Mod, [...]}} for any valid .beam, even when abstract
  code is absent; absence is signalled by the sentinel atom
  `:no_abstract_code` as the chunk's VALUE, not by an outer :error. A guard
  that only pattern-matches the outer {:ok, _} is vacuously always true and
  never rejects anything — the negative test exists specifically to catch that.
  """
  def cover_compilable?(module) do
    case :code.which(module) do
      beam when is_list(beam) ->
        match?(
          {:ok, {^module, [{:abstract_code, {:raw_abstract_v1, _forms}}]}},
          :beam_lib.chunks(beam, [:abstract_code])
        )

      _ ->
        false
    end
  end

  @doc "Run `fun` with `modules` cover-compiled; always :cover.stop afterward."
  def with_cover(modules, fun) do
    # :cover.start/0 returns {:ok, pid} the first time and
    # {:error, {:already_started, pid}} if a cover session already exists on the
    # node — both mean "the cover server is available"; only a genuinely
    # different error should surface.
    case :cover.start() do
      {:ok, _} -> :ok
      {:error, {:already_started, _}} -> :ok
    end

    try do
      Enum.each(modules, fn m ->
        {:ok, ^m} = normalize_compile({:cover.compile_beam(m), m}, m)
      end)

      fun.()
    after
      :cover.stop()
    end
  end

  defp normalize_compile({{:ok, m}, _}, m), do: {:ok, m}

  defp normalize_compile({{:error, reason}, m}, m),
    do: raise("cover.compile_beam failed for #{inspect(m)}: #{inspect(reason)}")

  @doc """
  Line-level coverage for a cover-compiled `module`. MUST be called inside a
  `with_cover/2` block (before `:cover.stop`). Returns
  `%{covered: [line], cold: [line], total: n}`, excluding the `{{Mod, 0}, {0, 1}}`
  module-level pseudo-entry that `:cover.analyse` always emits.
  """
  def line_coverage(module) do
    {:ok, pairs} = :cover.analyse(module, :coverage, :line)

    {cov, cold} =
      pairs
      |> Enum.reject(fn {{_m, line}, _} -> line == 0 end)
      |> Enum.reduce({[], []}, fn {{_m, line}, {c, _n}}, {yes, no} ->
        if c > 0, do: {[line | yes], no}, else: {yes, [line | no]}
      end)

    %{covered: Enum.sort(cov), cold: Enum.sort(cold), total: length(cov) + length(cold)}
  end
end
