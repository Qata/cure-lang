defmodule Cure.Audit.Source do
  @moduledoc """
  Locate a stdlib module's source by its declared `mod` header.

  The filename does not determine the module name — `Std.NonEmpty` lives in
  `non_empty.cure` and `Std.CRDT` in `crdt.cure` — so the header is authoritative.
  """

  @std_dir Path.expand("../../../lib/std", __DIR__)

  @doc """
  The absolute stdlib source directory this module was compiled against. Baked
  at compile time, so it points at the real checkout regardless of the caller's
  working directory. The CLI seeds it into `Cure.Stdlib.Paths`' import resolver
  so a module's `use Std.X` imports resolve from any CWD (see the audit CLI).
  """
  @spec std_dir() :: Path.t()
  def std_dir, do: @std_dir

  @spec locate(String.t()) :: {:ok, Path.t()} | {:error, :not_found}
  def locate(module) do
    pattern = ~r/^\s*mod\s+#{Regex.escape(module)}\s*$/m

    Path.join(@std_dir, "*.cure")
    |> Path.wildcard()
    |> Enum.sort()
    |> Enum.find(fn path -> Regex.match?(pattern, File.read!(path)) end)
    |> case do
      nil -> {:error, :not_found}
      path -> {:ok, path}
    end
  end
end
