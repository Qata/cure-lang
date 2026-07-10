defmodule Cure.Edition do
  @moduledoc """
  Cure editions: a coarse, declared, calendar-named compatibility line a file or
  project is read against (design: docs/superpowers/specs/2026-07-10-editions-design.md).

  An edition is a 4-digit calendar-year string. The set of real editions is the
  closed allow-list `@known`; `current/0` is the newest. Ordering is by integer
  year and is deliberately independent of the allow-list so ordering logic is
  usable for editions not yet minted.
  """

  require Logger

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

  @doc """
  The edition named by a file-leading `@edition("YYYY")` pragma, or `nil`. Uses a
  lightweight pre-parse line scan (not the full parser) because the edition must
  be known BEFORE parsing selects the keyword set. Skips leading blank lines and
  `#`/`##` comment lines; the first substantive line must be the pragma or there
  is none.
  """
  @spec pragma_edition(String.t()) :: t() | nil
  def pragma_edition(source) when is_binary(source) do
    source
    |> String.split("\n")
    |> Enum.drop_while(&trivia_line?/1)
    |> case do
      [first | _] -> pragma_capture(first)
      [] -> nil
    end
  end

  defp trivia_line?(line) do
    t = String.trim(line)
    t == "" or String.starts_with?(t, "#")
  end

  defp pragma_capture(line) do
    case Regex.run(~r/^\s*@edition\(\s*"(\d{4})"\s*\)/, line) do
      [_, year] -> year
      nil -> nil
    end
  end

  @doc """
  Resolve the effective edition for a source/project per precedence:
  file `@edition` pragma > `Cure.toml` `[project].edition` > compiler default.
  """
  @spec resolve(map()) :: {:ok, t()} | {:error, term()}
  def resolve(input) do
    case pragma_edition(Map.get(input, :source, "")) do
      nil -> resolve_project(Map.get(input, :project_dir))
      pragma -> parse(pragma)
    end
  end

  defp resolve_project(nil), do: {:ok, current()}

  defp resolve_project(dir) do
    case Cure.Project.load(dir) do
      {:ok, %{edition: nil}} ->
        maybe_advise_missing_edition()
        {:ok, current()}

      {:ok, %{edition: edition}} ->
        {:ok, edition}

      {:error, :no_project_file} ->
        {:ok, current()}

      {:error, _} = err ->
        err
    end
  end

  @advisory_key {__MODULE__, :missing_edition_advisory_shown?}

  # Spec §3.2 point 2: a project with a Cure.toml but no `edition` key still
  # resolves (to `current/0`) rather than hard-failing, but logs a one-time
  # advisory so projects converge on an explicit edition. "Once" is
  # process-lifetime via :persistent_term (mirrors the existing memoisation
  # pattern in lib/cure/types/stdlib.ex), not per-file — a whole-project
  # build touching many undeclared files must not spam one warning per file.
  defp maybe_advise_missing_edition do
    case :persistent_term.get(@advisory_key, false) do
      true ->
        :ok

      false ->
        :persistent_term.put(@advisory_key, true)
        Logger.warning("no `edition` declared in Cure.toml — add `edition = \"#{current()}\"` under [project] to pin the language surface this project reads against")
    end
  end

  @doc false
  # Test-only: clears the one-time advisory flag so tests asserting on it are
  # isolated from each other and from resolve/1 calls made by other tests.
  @spec reset_advisory!() :: :ok
  def reset_advisory! do
    :persistent_term.erase(@advisory_key)
    :ok
  end

  @doc """
  The keywords retired at or before `edition`, derived from the migration
  registry (single source of truth). A rule retires each of its
  `retires_keywords` at its `enforced_in` edition: present for editions before
  it, absent at/after. `enforced_in: nil` never retires.

  `Cure.Migrate.rules()` is called at RUNTIME (the default arg) rather than at
  compile time to avoid a compile cycle (lexer → Edition → Migrate → rule
  modules).
  """
  @spec retired_keywords(t(), [Cure.Migrate.Rule.t()]) :: [String.t()]
  def retired_keywords(edition, rules \\ Cure.Migrate.rules()) do
    for r <- rules,
        r.enforced_in != nil,
        compare(edition, r.enforced_in) in [:eq, :gt],
        kw <- r.retires_keywords,
        uniq: true,
        do: kw
  end
end
