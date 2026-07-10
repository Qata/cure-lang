defmodule Cure.Audit.Source do
  @moduledoc """
  Locate a stdlib module's source by its declared `mod` header.

  The filename does not determine the module name — `Std.NonEmpty` lives in
  `non_empty.cure` and `Std.CRDT` in `crdt.cure` — so the header is authoritative.
  """

  @std_dir Path.expand("../../../lib/std", __DIR__)

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
