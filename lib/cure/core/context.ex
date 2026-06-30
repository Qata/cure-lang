defmodule Cure.Core.Context do
  @moduledoc """
  The kernel's typing context: a telescope of variable **types** (as semantic
  values) for bidirectional `infer`/`check` (design spec §5).

  Variables are de Bruijn-indexed — index 0 is the most-recently-bound, at the
  head. `env/1` produces the matching NbE evaluation environment, mapping each
  bound variable to a fresh neutral at its de Bruijn *level* (the most-recent
  variable, index 0, gets the highest level), so types and bodies can be
  evaluated and read back consistently under the context.
  """

  alias Cure.Core.Value

  defstruct types: [], length: 0

  @type t :: %__MODULE__{types: [Value.t()], length: non_neg_integer()}

  @doc "The empty context."
  @spec empty() :: t()
  def empty, do: %__MODULE__{}

  @doc "Extend the context with one more variable of the given type value."
  @spec extend(t(), Value.t()) :: t()
  def extend(%__MODULE__{types: ts, length: n}, type_value),
    do: %__MODULE__{types: [type_value | ts], length: n + 1}

  @doc "The type value of the variable at de Bruijn index `k` (0 = most recent)."
  @spec lookup(t(), non_neg_integer()) :: Value.t() | nil
  def lookup(%__MODULE__{types: ts}, k), do: Enum.at(ts, k)

  @doc "Number of variables in scope."
  @spec length(t()) :: non_neg_integer()
  def length(%__MODULE__{length: n}), do: n

  @doc """
  The NbE environment for this context: a fresh neutral per variable, with the
  most-recent variable (index 0) bound to the highest de Bruijn level.
  """
  @spec env(t()) :: [Value.t()]
  def env(%__MODULE__{length: 0}), do: []

  def env(%__MODULE__{length: n}),
    do: for(level <- (n - 1)..0//-1, do: {:vneutral, {:nvar, level}})
end
