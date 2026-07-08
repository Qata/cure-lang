defmodule Cure.Core.Env do
  @moduledoc """
  The global signature: indexed inductive families, their constructors, and
  (from M7.1) global function definitions plus the set of totality-certified
  globals that δ-reduction is permitted to unfold.

  This is the single shared environment threaded through the kernel and
  elaborator; later tasks refer to it as `Core.Env`. It carries no PIDs or
  closures — only Core terms and metadata — so it stays serializable.
  """

  defstruct families: %{}, ctors: %{}, ctor_to_family: %{}, defs: %{}, certified: nil, builtins: %{}

  @type t :: %__MODULE__{
          families: %{atom() => map()},
          ctors: %{atom() => map()},
          ctor_to_family: %{atom() => atom()},
          defs: %{atom() => map()},
          certified: MapSet.t() | nil,
          builtins: %{atom() => atom()}
        }

  @doc "An empty signature."
  @spec empty() :: t()
  def empty, do: %__MODULE__{certified: MapSet.new()}

  @doc """
  Register a global function definition (declared type + Core body). The kernel
  must `check_def/2` it before it may be referenced; certification (M7.2) gates
  whether δ-reduction may unfold it.
  """
  @spec add_def(t(), atom(), Cure.Core.Term.t(), Cure.Core.Term.t()) :: t()
  def add_def(env, name, type_term, body_term), do: add_def(env, name, type_term, body_term, nil)

  @doc """
  Register a global function definition with per-parameter {0,ω} quantities
  (`nil` = unspecified/all runtime-relevant). Erased parameters are dropped by
  erasure (M8.3 / M9).
  """
  @spec add_def(t(), atom(), Cure.Core.Term.t(), Cure.Core.Term.t(), [atom()] | nil) :: t()
  def add_def(%__MODULE__{} = env, name, type_term, body_term, quantities),
    do: %{
      env
      | defs:
          Map.put(env.defs, name, %{
            name: name,
            type: type_term,
            body: body_term,
            quantities: quantities
          })
    }

  @doc "The global definition `%{name, type, body}` for `name`, or nil."
  @spec get_def(t(), atom()) :: map() | nil
  def get_def(%__MODULE__{defs: defs}, name), do: Map.get(defs, name)

  @doc """
  Mark a global as totality-certified (δ may unfold it). See M7.2.

  Refuses a def whose body is not closed: δ evaluates a certified body in the
  empty environment, so an open body's free variables would alias context
  variables (a capture). Certification is only legitimately produced by the
  kernel's `validate_certificate` on a checked (hence closed) body; this
  assertion makes an open-bodied certificate impossible to create through the
  public seam. (A5)
  """
  @spec certify(t(), atom()) :: t()
  def certify(%__MODULE__{certified: c} = env, name) do
    case get_def(env, name) do
      %{body: body} ->
        unless Cure.Core.Term.closed?(body) do
          raise ArgumentError,
                "cannot certify #{inspect(name)}: body has a free de Bruijn variable " <>
                  "(open body). Certification requires a closed, kernel-validated body (M7.2 / A5)."
        end

      _ ->
        :ok
    end

    %{env | certified: MapSet.put(c, name)}
  end

  @doc "Is the global `name` certified total (δ-reducible)?"
  @spec certified?(t(), atom()) :: boolean()
  def certified?(%__MODULE__{certified: c}, name), do: MapSet.member?(c, name)
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
  @type quantity :: :erased | :present
  @type family :: %{name: atom(), params: telescope(), indices: telescope(), level: non_neg_integer()}
  @type ctor :: %{
          name: atom(),
          args: telescope(),
          result_indices: [Cure.Core.Term.t()],
          result_params: [Cure.Core.Term.t()],
          quantities: [quantity()]
        }

  @doc """
  Bind a builtin key to a family-id. Re-binding the key to the SAME family-id is
  an idempotent no-op (the auto-seed + a prelude source's own self-registration
  both target the same canonical family); re-binding to a DIFFERENT family-id is
  a hard error (the single-registration invariant that stops a user module from
  hijacking a builtin key).
  """
  @spec register_builtin(Env.t(), atom(), atom()) :: Env.t()
  def register_builtin(%Env{builtins: b} = env, key, family_id) when is_map_key(b, key) do
    case Map.fetch!(b, key) do
      ^family_id ->
        env

      other ->
        raise ArgumentError,
              "builtin key #{inspect(key)} already bound to #{inspect(other)} (cannot rebind to #{inspect(family_id)})"
    end
  end

  def register_builtin(%Env{} = env, key, family_id) do
    %{env | builtins: Map.put(env.builtins, key, family_id)}
  end

  @doc "Resolve a builtin key to its family-id, or nil."
  @spec builtin(Env.t(), atom()) :: atom() | nil
  def builtin(%Env{builtins: b}, key), do: Map.get(b, key)

  @doc "Build a family signature (no registration; see `declare/3`)."
  @spec family(atom(), telescope(), telescope(), non_neg_integer()) :: family()
  def family(name, param_tele, index_tele, level),
    do: %{name: name, params: param_tele, indices: index_tele, level: level}

  @doc """
  Build a constructor signature. Every argument defaults to runtime-relevant
  (`:present`, quantity ω); use `ctor/4` to mark inferred index arguments
  `:erased` (quantity 0) so they are dropped by erasure (M8.3 / M9).
  """
  @spec ctor(atom(), telescope(), [Cure.Core.Term.t()]) :: ctor()
  def ctor(name, arg_tele, result_indices),
    do: ctor(name, arg_tele, result_indices, List.duplicate(:present, length(arg_tele)))

  @doc "Build a constructor signature with explicit {0,ω} argument quantities."
  @spec ctor(atom(), telescope(), [Cure.Core.Term.t()], [quantity()]) :: ctor()
  def ctor(name, arg_tele, result_indices, quantities),
    do: ctor(name, arg_tele, result_indices, quantities, [])

  @doc """
  Build a constructor signature carrying its result *parameter* terms (the
  uniform parameter prefix of the family value it builds) separately from its
  result *index* terms. The parameter-free forms (`ctor/3`, `ctor/4`) default
  `result_params` to `[]`.
  """
  @spec ctor(atom(), telescope(), [Cure.Core.Term.t()], [quantity()], [Cure.Core.Term.t()]) ::
          ctor()
  def ctor(name, arg_tele, result_indices, quantities, result_params),
    do: %{
      name: name,
      args: arg_tele,
      result_indices: result_indices,
      result_params: result_params,
      quantities: quantities
    }

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

  @doc "A constructor's per-argument {0,ω} quantities (`:erased` / `:present`)."
  @spec ctor_quantities(Env.t(), atom()) :: [quantity()] | nil
  def ctor_quantities(env, cname) do
    case get_ctor(env, cname) do
      nil -> nil
      %{quantities: qs} -> qs
      _ -> nil
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

  @doc "A family's parameter arity (0 if none / unknown)."
  @spec param_count(Env.t(), atom()) :: non_neg_integer()
  def param_count(env, fname), do: length(param_telescope(env, fname) || [])

  @doc "A constructor's result *parameter* terms (the param prefix of its result)."
  @spec ctor_result_params(Env.t(), atom()) :: [Cure.Core.Term.t()] | nil
  def ctor_result_params(env, cname) do
    case get_ctor(env, cname) do
      nil -> nil
      %{result_params: rps} -> rps
      _ -> []
    end
  end

  @doc "All constructors registered for the family `fname`."
  @spec ctors_of(Env.t(), atom()) :: [ctor()]
  def ctors_of(%Env{ctors: cs, ctor_to_family: c2f}, fname) do
    cs
    |> Map.values()
    |> Enum.filter(fn %{name: n} -> Map.get(c2f, n) == fname end)
  end

  # -- strict positivity ------------------------------------------------------

  @doc """
  Strict positivity check (design spec §4.4; mirrors Agda `Positivity.hs` /
  Idris `Positivity.idr`): the family name may appear in a constructor field
  only strictly positively — never to the left of an arrow (a negative /
  contravariant position), which would break the well-foundedness that makes
  the eliminator and totality sound.
  """
  @spec positive?(Env.t(), family()) :: :ok | {:error, {:non_strictly_positive, atom()}}
  def positive?(env, %{name: fname}) do
    Enum.reduce_while(ctors_of(env, fname), :ok, fn %{name: cname, args: args}, :ok ->
      if Enum.all?(args, fn {_n, ty} -> strictly_positive?(env, fname, ty, MapSet.new()) end) do
        {:cont, :ok}
      else
        {:halt, {:error, {:non_strictly_positive, cname}}}
      end
    end)
  end

  # A field type is strictly positive in `fname` when, at every function arrow,
  # `fname` does not occur in the domain — not even hidden behind another
  # declared family's constructor fields (the through-constructor rule) — and
  # the codomain stays strictly positive. Σ is covariant in both components. A
  # field headed by ANOTHER family is checked by expanding that family's
  # constructor fields (`seen` breaks family cycles); `fname` occurring in
  # another family's parameters/indices is conservatively rejected.
  defp strictly_positive?(env, fname, {:pi, dom, cod}, seen),
    do: not occurs_deep?(env, fname, dom, seen) and strictly_positive?(env, fname, cod, seen)

  defp strictly_positive?(_env, fname, {:data, fname, _ps, _is}, _seen), do: true

  defp strictly_positive?(env, fname, {:data, other, ps, is}, seen) do
    cond do
      Enum.any?(ps ++ is, &occurs?(fname, &1)) ->
        false

      MapSet.member?(seen, other) ->
        true

      true ->
        seen2 = MapSet.put(seen, other)

        env
        |> ctors_of(other)
        |> Enum.all?(fn %{args: args} ->
          Enum.all?(args, fn {_n, ty} -> strictly_positive?(env, fname, ty, seen2) end)
        end)
    end
  end

  defp strictly_positive?(_env, _fname, _other, _seen), do: true

  # Does `fname` occur anywhere in `ty`, including inside the constructor fields
  # of other families referenced by `ty`? Used for arrow DOMAINS, where any
  # reachable occurrence is a negative position.
  defp occurs_deep?(env, fname, ty, seen) do
    occurs?(fname, ty) or
      Enum.any?(data_heads(ty), fn other ->
        other != fname and not MapSet.member?(seen, other) and
          env
          |> ctors_of(other)
          |> Enum.any?(fn %{args: args} ->
            Enum.any?(args, fn {_n, t} ->
              occurs_deep?(env, fname, t, MapSet.put(seen, other))
            end)
          end)
      end)
  end

  # Every family name appearing as a `{:data, …}` head anywhere in the term.
  defp data_heads(term), do: term |> gather_data_heads(MapSet.new()) |> MapSet.to_list()

  defp gather_data_heads({:data, n, ps, is}, acc),
    do: Enum.reduce(ps ++ is, MapSet.put(acc, n), &gather_data_heads/2)

  defp gather_data_heads(t, acc) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.reduce(acc, &gather_data_heads/2)

  defp gather_data_heads(l, acc) when is_list(l), do: Enum.reduce(l, acc, &gather_data_heads/2)
  defp gather_data_heads(_t, acc), do: acc

  # Does the family name `fname` occur anywhere in `term` (as an applied family)?
  defp occurs?(fname, {:data, fname, _ps, _is}), do: true

  defp occurs?(fname, {:data, _other, ps, is}),
    do: Enum.any?(ps, &occurs?(fname, &1)) or Enum.any?(is, &occurs?(fname, &1))

  defp occurs?(fname, {:pi, d, c}), do: occurs?(fname, d) or occurs?(fname, c)
  defp occurs?(fname, {:lam, d, b}), do: occurs?(fname, d) or occurs?(fname, b)
  defp occurs?(fname, {:app, f, a}), do: occurs?(fname, f) or occurs?(fname, a)
  defp occurs?(fname, {:ctor, _n, args}), do: Enum.any?(args, &occurs?(fname, &1))

  defp occurs?(fname, {:case, s, m, brs}),
    do:
      occurs?(fname, s) or occurs?(fname, m) or
        Enum.any?(brs, fn {_c, _ar, body} -> occurs?(fname, body) end)

  defp occurs?(_fname, _term), do: false
end
