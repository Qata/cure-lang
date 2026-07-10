defmodule Cure.Edition do
  @moduledoc """
  Cure editions: a coarse, declared, calendar-named compatibility line a file or
  project is read against (design: docs/superpowers/specs/2026-07-10-editions-design.md).

  An edition is a 4-digit calendar-year string. The set of real editions is the
  closed allow-list `@known`; `current/0` is the newest. Ordering is by integer
  year and is deliberately independent of the allow-list so ordering logic is
  usable for editions not yet minted.
  """

  @known ["2026"]
  @current "2026"

  @type t :: String.t()

  @doc "All known editions, oldest-first."
  @spec all() :: [t()]
  def all, do: Enum.sort(@known, &(year(&1) <= year(&2)))

  @doc "Every known edition (declaration set; unordered)."
  @spec known() :: [t()]
  def known, do: @known

  @doc "The newest known edition — the compiler default when none is declared."
  @spec current() :: t()
  def current, do: @current

  @doc "True iff `edition` is a known edition."
  @spec valid?(term()) :: boolean()
  def valid?(edition), do: edition in @known

  @doc "Validate an edition string against the allow-list."
  @spec parse(term()) :: {:ok, t()} | {:error, {:unknown_edition, term()}}
  def parse(edition) do
    if valid?(edition), do: {:ok, edition}, else: {:error, {:unknown_edition, edition}}
  end

  @doc "Total order on editions by integer year (allow-list-independent)."
  @spec compare(t(), t()) :: :lt | :eq | :gt
  def compare(a, b) do
    cond do
      year(a) < year(b) -> :lt
      year(a) > year(b) -> :gt
      true -> :eq
    end
  end

  defp year(<<y::binary-size(4)>>), do: String.to_integer(y)
  defp year(other) when is_binary(other), do: String.to_integer(other)
end
