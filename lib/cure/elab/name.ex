defmodule Cure.Elab.Name do
  @moduledoc """
  Canonical identities for elaborated global names.

  Core keeps globals as `{:global, atom()}`. This module owns the elaborator's
  spelling convention for module-owned names so registration and every later
  consumer agree on the same identity without open-coded string parsing.
  """

  @separator "#"

  @type owner :: String.t() | atom()
  @type base :: String.t() | atom()

  @doc "Return the canonical atom for a module-owned global name."
  @spec qualify(owner(), base()) :: atom()
  def qualify(owner, base) do
    String.to_atom(normalize_owner(owner) <> @separator <> normalize_base(base))
  end

  @doc "Return the module owner encoded in a canonical name, or nil for a bare atom."
  @spec owner(atom() | String.t()) :: String.t() | nil
  def owner(name) when is_atom(name), do: owner(Atom.to_string(name))

  def owner(name) when is_binary(name) do
    case String.split(name, @separator, parts: 2) do
      [owner, _base] -> if valid_owner?(owner), do: owner, else: nil
      _ -> nil
    end
  end

  def owner(_name), do: nil

  @doc "Return the basename encoded in a canonical name, or the original bare name."
  @spec base(atom() | String.t()) :: String.t() | nil
  def base(name) when is_atom(name), do: base(Atom.to_string(name))

  def base(name) when is_binary(name) do
    case String.split(name, @separator, parts: 2) do
      [owner, base] -> if valid_owner?(owner), do: base, else: name
      [bare] -> bare
    end
  end

  def base(_name), do: nil

  @doc "Whether a global identity carries an owner qualifier."
  @spec qualified?(atom() | String.t()) :: boolean()
  def qualified?(name), do: owner(name) != nil

  defp normalize_owner(owner) when is_atom(owner), do: Atom.to_string(owner)
  defp normalize_owner(owner) when is_binary(owner), do: owner

  defp normalize_base(base) when is_atom(base), do: Atom.to_string(base)
  defp normalize_base(base) when is_binary(base), do: base

  defp valid_owner?(owner) do
    owner != "" and String.match?(owner, ~r/^[A-Za-z_][A-Za-z0-9_.]*$/)
  end
end
