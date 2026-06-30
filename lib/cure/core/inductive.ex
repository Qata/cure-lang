defmodule Cure.Core.Env do
  @moduledoc """
  The global signature: indexed inductive families, their constructors, and
  (from M7.1) global function definitions plus the set of totality-certified
  globals that δ-reduction is permitted to unfold.

  This is the single shared environment threaded through the kernel and
  elaborator; later tasks refer to it as `Core.Env`. It carries no PIDs or
  closures — only Core terms and metadata — so it stays serializable.
  """

  defstruct families: %{}, ctors: %{}, ctor_to_family: %{}, defs: %{}, certified: nil

  @type t :: %__MODULE__{
          families: %{atom() => map()},
          ctors: %{atom() => map()},
          ctor_to_family: %{atom() => atom()},
          defs: %{atom() => map()},
          certified: MapSet.t() | nil
        }

  @doc "An empty signature."
  @spec empty() :: t()
  def empty, do: %__MODULE__{certified: MapSet.new()}
end

defmodule Cure.Core.Inductive do
  @moduledoc """
  Representation of indexed inductive families and their constructors
  (design spec §4.4; mirrors Idris `Core/Context/Data.idr` and Lean
  `inductive.cpp`).

  A **family** has a parameter telescope, an index telescope, and a universe
  level. A **constructor** has an argument telescope and a list of *result
  index terms* — the indices of the family value it builds, written over the
  constructor's parameters and arguments (so they may be computed, e.g.
  `and(d1, d2)`). A telescope is `[{var_name, type_term}]`.

  Well-formedness checking (M3.2), strict positivity (M3.3), and constructor
  application typing (M3.4) build on this representation.
  """

  alias Cure.Core.Env

  @type telescope :: [{atom(), Cure.Core.Term.t()}]
  @type family :: %{name: atom(), params: telescope(), indices: telescope(), level: non_neg_integer()}
  @type ctor :: %{name: atom(), args: telescope(), result_indices: [Cure.Core.Term.t()]}

  @doc "Build a family signature (no registration; see `declare/3`)."
  @spec family(atom(), telescope(), telescope(), non_neg_integer()) :: family()
  def family(name, param_tele, index_tele, level),
    do: %{name: name, params: param_tele, indices: index_tele, level: level}

  @doc "Build a constructor signature."
  @spec ctor(atom(), telescope(), [Cure.Core.Term.t()]) :: ctor()
  def ctor(name, arg_tele, result_indices),
    do: %{name: name, args: arg_tele, result_indices: result_indices}

  @doc "Register a family and its constructors in the env."
  @spec declare(Env.t(), family(), [ctor()]) :: Env.t()
  def declare(%Env{} = env, %{name: fname} = family, ctors) do
    env = %{env | families: Map.put(env.families, fname, family)}

    Enum.reduce(ctors, env, fn %{name: cname} = c, acc ->
      %{
        acc
        | ctors: Map.put(acc.ctors, cname, c),
          ctor_to_family: Map.put(acc.ctor_to_family, cname, fname)
      }
    end)
  end

  # -- accessors --------------------------------------------------------------

  @doc "Is `name` a registered family?"
  @spec family?(Env.t(), atom()) :: boolean()
  def family?(%Env{families: fs}, name), do: Map.has_key?(fs, name)

  @doc "The family signature for `name`, or nil."
  @spec get_family(Env.t(), atom()) :: family() | nil
  def get_family(%Env{families: fs}, name), do: Map.get(fs, name)

  @doc "The constructor signature for `name`, or nil."
  @spec get_ctor(Env.t(), atom()) :: ctor() | nil
  def get_ctor(%Env{ctors: cs}, name), do: Map.get(cs, name)

  @doc "The family a constructor belongs to."
  @spec ctor_family(Env.t(), atom()) :: atom() | nil
  def ctor_family(%Env{ctor_to_family: m}, cname), do: Map.get(m, cname)

  @doc "A constructor's result index terms."
  @spec ctor_result_indices(Env.t(), atom()) :: [Cure.Core.Term.t()] | nil
  def ctor_result_indices(env, cname) do
    case get_ctor(env, cname) do
      nil -> nil
      %{result_indices: ris} -> ris
    end
  end

  @doc "A constructor's argument telescope."
  @spec arg_telescope(Env.t(), atom()) :: telescope() | nil
  def arg_telescope(env, cname) do
    case get_ctor(env, cname) do
      nil -> nil
      %{args: args} -> args
    end
  end

  @doc "A family's index telescope."
  @spec index_telescope(Env.t(), atom()) :: telescope() | nil
  def index_telescope(env, fname) do
    case get_family(env, fname) do
      nil -> nil
      %{indices: idx} -> idx
    end
  end

  @doc "A family's parameter telescope."
  @spec param_telescope(Env.t(), atom()) :: telescope() | nil
  def param_telescope(env, fname) do
    case get_family(env, fname) do
      nil -> nil
      %{params: params} -> params
    end
  end
end
