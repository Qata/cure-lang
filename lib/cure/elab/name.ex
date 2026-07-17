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

  # `[A-Za-z_][A-Za-z0-9_.]*`, anchored at both ends, as a byte scan rather than
  # a regex. `owner/1` and `base/1` sit under the elaborator's name resolution,
  # which asks this question millions of times per elaboration; a `Regex.match?/2`
  # here cost roughly a quarter of a cold compile in `re:run`/`re:import` alone.
  defp valid_owner?(<<c, rest::binary>>) when c in ?A..?Z or c in ?a..?z or c == ?_,
    do: owner_rest?(rest)

  defp valid_owner?(_owner), do: false

  defp owner_rest?(<<>>), do: true

  defp owner_rest?(<<c, rest::binary>>)
       when c in ?A..?Z or c in ?a..?z or c in ?0..?9 or c == ?_ or c == ?.,
       do: owner_rest?(rest)

  defp owner_rest?(_rest), do: false
end
