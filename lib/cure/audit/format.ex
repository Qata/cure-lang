defmodule Cure.Audit.Format do
  @moduledoc """
  Render a `Cure.Audit.Ledger.Report` deterministically.

  Determinism is load-bearing: `cure audit trust Std.List | diff -` is the
  ratchet that makes a new axiom a reviewable diff. Sorted, no timestamps, no
  absolute paths, no map-iteration order. Every section prints even when empty,
  so a `(0)` becoming a `(1)` is a diff rather than a new line from nowhere.
  """

  alias Cure.Audit.Ledger
  alias Cure.Audit.Ledger.Axiom
  alias Cure.Audit.Targets

  @spec render(Ledger.Report.t(), keyword()) :: String.t()
  def render(report, opts) do
    case Keyword.get(opts, :format, "text") do
      "json" -> to_json(report, opts)
      _ -> to_text(report, opts)
    end
  end

  @spec to_text(Ledger.Report.t(), keyword()) :: String.t()
  def to_text(report, opts) do
    target = Keyword.get(opts, :target)

    [
      bucket_section("AXIOMS — OTP", report.axioms, :otp),
      bucket_section("AXIOMS — CURE RUNTIME", report.axioms, :cure_runtime),
      bucket_section("AXIOMS — CURE BRIDGE", report.axioms, :cure_bridge),
      list_section("OPAQUE TYPES", Enum.map(report.opaque, &Atom.to_string/1)),
      "KERNEL BUILTINS\n  #{report.builtin_count} builtin operators (Cure.Core.Builtins)",
      list_section("HOLES", report.holes),
      "ABSURD (#{report.absurd})",
      not_total_section(report.not_proven_total),
      target_section(report.axioms, target),
      list_section("UNAUDITED", Enum.map(report.unaudited, fn {label, _} -> label end))
    ]
    |> Enum.reject(&is_nil/1)
    |> Enum.join("\n\n")
    |> Kernel.<>("\n")
  end

  @spec to_json(Ledger.Report.t(), keyword()) :: String.t()
  def to_json(report, _opts) do
    axioms =
      Enum.map(report.axioms, fn a ->
        ~s({"mfa":"#{mfa(a)}","type":"#{escape(a.type)}","via":"#{a.via}","bucket":"#{a.bucket}"})
      end)

    ~s({"schema":1,"axioms":[#{Enum.join(axioms, ",")}],) <>
      ~s("opaque":[#{Enum.map_join(report.opaque, ",", &~s("#{&1}"))}],) <>
      ~s("builtin_count":#{report.builtin_count},) <>
      ~s("holes":[#{Enum.map_join(report.holes, ",", &~s("#{escape(&1)}"))}],) <>
      ~s("absurd":#{report.absurd},) <>
      ~s("not_proven_total":[#{Enum.map_join(report.not_proven_total, ",", &~s("#{&1}"))}],) <>
      ~s("unaudited":[#{Enum.map_join(report.unaudited, ",", fn {l, _} -> ~s("#{l}") end)}]}) <>
      "\n"
  end

  # -- sections --------------------------------------------------------------

  defp bucket_section(title, axioms, bucket) do
    rows = Enum.filter(axioms, &(&1.bucket == bucket))
    header = "#{title} (#{length(rows)})"

    case rows do
      [] -> header
      _ -> header <> "\n" <> Enum.map_join(rows, "\n", &"  #{pad(mfa(&1))} #{&1.type}")
    end
  end

  defp list_section(title, []), do: "#{title} (0)"

  defp list_section(title, items),
    do: "#{title} (#{length(items)})\n" <> Enum.map_join(items, "\n", &"  #{&1}")

  defp not_total_section([]),
    do: "NOT PROVEN TOTAL (0)   — cannot be used in proofs; not assumptions"

  defp not_total_section(names) do
    "NOT PROVEN TOTAL (#{length(names)})   — cannot be used in proofs; not assumptions\n" <>
      "  " <> Enum.map_join(names, ", ", &Atom.to_string/1)
  end

  defp target_section(_axioms, nil), do: nil

  defp target_section(axioms, target) do
    rows = Enum.filter(axioms, &Targets.unavailable?(target, &1.mfa))
    header = "UNAVAILABLE ON TARGET (#{length(rows)})"

    case rows do
      [] ->
        header

      _ ->
        header <>
          "\n" <>
          Enum.map_join(rows, "\n", fn a ->
            {m, _f, _a} = a.mfa
            "  #{pad(mfa(a))} via #{a.via}   — :#{m} absent on #{target}"
          end)
    end
  end

  # -- helpers ---------------------------------------------------------------

  defp mfa(%Axiom{mfa: {m, f, a}}), do: "#{m}:#{f}/#{a}"
  defp pad(s), do: String.pad_trailing(s, 24)
  defp escape(s), do: s |> String.replace("\\", "\\\\") |> String.replace("\"", "\\\"")
end
