defmodule Cure.Core.Env do
  @moduledoc """
  The global signature: indexed inductive families, their constructors, and
  (from M7.1) global function definitions plus the set of totality-certified
  globals that δ-reduction is permitted to unfold.

  This is the single shared environment threaded through the kernel and
  elaborator; later tasks refer to it as `Core.Env`. It carries no PIDs or
  closures — only Core terms and metadata — so it stays serializable.
  """

  defstruct families: %{},
            ctors: %{},
            ctor_to_family: %{},
            defs: %{},
            certified: nil,
            builtins: %{},
            interfaces: %{},
            coherence: nil,
            constrained: %{},
            primitives: %{},
            import_modules: MapSet.new(),
            lemmas: %{},
            module_owner: nil

  @type t :: %__MODULE__{
          families: %{atom() => map()},
          ctors: %{atom() => map()},
          ctor_to_family: %{atom() => atom()},
          defs: %{atom() => map()},
          certified: MapSet.t() | nil,
          builtins: %{atom() => atom()},
          interfaces: %{atom() => map()},
          coherence: term(),
          constrained: %{atom() => [map()]},
          primitives: %{String.t() => tuple()},
          # The source module whose declarations are currently being
          # elaborated. Imported environments retain their own owner until
          # their canonical entries are merged into the importing environment.
          module_owner: String.t() | nil,
          # Inert elaborator metadata (the kernel never reads it): the set of
          # module-ids DIRECTLY imported by the module this env belongs to
          # (explicit `use` + auto-prelude). Bare-name resolution prefers a
          # direct owner over a name reachable only via a module's transitive
          # re-export, matching must-import semantics (Haskell/Elm/Idris/Swift).
          import_modules: MapSet.t(String.t()),
          # Inert elaborator metadata (the kernel never reads it): `@lemma`-tagged
          # theorems keyed by their conclusion-head atom, for auto proof-search
          # (see `Cure.Elab.ProofSearch`). Same status as `interfaces`/`coherence`.
          lemmas: %{atom() => [map()]}
        }

  @doc "An empty signature."
  @spec empty() :: t()
  def empty, do: %__MODULE__{certified: MapSet.new()}

  @doc "Attach the source-module owner used for canonical declaration identity."
  @spec with_owner(t(), String.t() | atom() | nil) :: t()
  def with_owner(%__MODULE__{} = env, nil), do: %{env | module_owner: nil}

  def with_owner(%__MODULE__{} = env, owner) when is_atom(owner),
    do: with_owner(env, Atom.to_string(owner))

  def with_owner(%__MODULE__{} = env, owner) when is_binary(owner) or is_nil(owner),
    do: %{env | module_owner: owner}

  @doc "Return the source-module owner for the current elaboration environment."
  @spec owner(t()) :: String.t() | nil
  def owner(%__MODULE__{module_owner: owner}), do: owner

  @doc """
  Register a global function definition (declared type + Core body). The kernel
  must `check_def/2` it before it may be referenced; certification (M7.2) gates
  whether δ-reduction may unfold it.
  """
  @typedoc """
  What a definition's body slot may actually hold.

  Three inhabitants, and only the first is a Core term:

    * a `Cure.Core.Term.t()` — an ordinary definition;
    * `nil` — a builtin, seeded with a type but no body (`Cure.Core.Builtins`);
    * `{:extern, {mod, fun, arity}}` — an `@extern` FFI binding, whose body lives
      on the BEAM, not in Core.

  The spec used to claim this was always a term. Dialyzer disagreed, and it was
  right: `Declarations` passes the `:extern` tuple and `Builtins` passes `nil`.
  """
  @type def_body :: Cure.Core.Term.t() | nil | {:extern, {module(), atom(), arity()}}

  @spec add_def(t(), atom(), Cure.Core.Term.t(), def_body()) :: t()
  def add_def(env, name, type_term, body_term), do: add_def(env, name, type_term, body_term, nil)

  @doc """
  Register a global function definition with per-parameter {0,ω} quantities
  (`nil` = unspecified/all runtime-relevant). Erased parameters are dropped by
  erasure (M8.3 / M9).
  """
  @spec add_def(t(), atom(), Cure.Core.Term.t(), def_body(), [atom()] | nil) :: t()
  def add_def(%__MODULE__{} = env, name, type_term, body_term, quantities) do
    name = owned_name(env, name)

    %{
      env
      | defs:
          Map.put(env.defs, name, %{
            name: name,
            type: type_term,
            body: body_term,
            quantities: quantities
          })
    }
  end

  @doc "The global definition `%{name, type, body}` for `name`, or nil."
  @spec get_def(t(), atom()) :: map() | nil
  def get_def(%__MODULE__{} = env, name), do: Map.get(env.defs, resolve_key(env, env.defs, name))

  @doc "Return the owner-qualified key for a declaration in the current module."
  @spec owned_name(t(), atom() | String.t()) :: atom()
  def owned_name(%__MODULE__{module_owner: owner}, name) when is_binary(name),
    do: owned_name(%__MODULE__{module_owner: owner}, String.to_atom(name))

  def owned_name(%__MODULE__{module_owner: nil}, name), do: name

  def owned_name(%__MODULE__{module_owner: owner}, name) when is_atom(name) do
    if Cure.Elab.Name.qualified?(name), do: name, else: Cure.Elab.Name.qualify(owner, name)
  end

  @doc "Resolve a bare key against the current module's canonical key first."
  @spec resolve_key(t(), map(), atom() | String.t()) :: atom()
  def resolve_key(%__MODULE__{} = env, table, name) when is_binary(name),
    do: resolve_key(env, table, String.to_atom(name))

  def resolve_key(%__MODULE__{} = env, table, name) when is_atom(name) do
    owned = owned_name(env, name)

    cond do
      Map.has_key?(table, owned) ->
        owned

      Map.has_key?(table, name) ->
        name

      true ->
        # Last resort: the name is bare and unowned, so find the unique
        # owner-qualified key whose base it is. This walks every key in the
        # table, so keep the per-key work to a single split, and hoist the
        # target spelling out of the loop rather than re-deriving it per key.
        target = Atom.to_string(name)

        case Enum.filter(Map.keys(table), &owned_alias?(&1, target)) do
          [key] -> key
          _ -> name
        end
    end
  end

  # Whether `key` is an owner-qualified name whose base is `target`.
  defp owned_alias?(key, target) when is_atom(key) do
    case Cure.Elab.Name.split(key) do
      {nil, _base} -> false
      {_owner, base} -> base == target
    end
  end

  defp owned_alias?(_key, _target), do: false

  @doc "Register a primitive base type: surface name → its Core type node."
  @spec put_primitive(t(), String.t(), tuple()) :: t()
  def put_primitive(%__MODULE__{primitives: p} = env, name, node) when is_binary(name),
    do: %{env | primitives: Map.put(p, name, node)}

  @doc "The Core node a primitive surface name resolves to, or nil."
  @spec primitive(t(), String.t()) :: tuple() | nil
  def primitive(%__MODULE__{primitives: p}, name) when is_binary(name), do: Map.get(p, name)

  @doc """
  Register a compile-time interface (typeclass) descriptor under its name
  atom. The descriptor is elaborator-level metadata (head var, head kind,
  method field types, default bodies) — see `Cure.Elab.Interface`.
  """
  @spec put_interface(t(), atom(), map()) :: t()
  def put_interface(%__MODULE__{interfaces: ifaces} = env, name, desc),
    do: %{env | interfaces: Map.put(ifaces, name, desc)}

  @doc "The interface descriptor for `name`, or nil."
  @spec get_interface(t(), atom()) :: map() | nil
  def get_interface(%__MODULE__{interfaces: ifaces}, name), do: Map.get(ifaces, name)

  @doc """
  Register a `@lemma`-tagged theorem for auto proof-search, filed under the
  head atom of its conclusion type. Inert elaborator metadata — the kernel
  never reads it (like `interfaces`/`coherence`). See `Cure.Elab.ProofSearch`.
  """
  @spec put_lemma(t(), atom(), map()) :: t()
  def put_lemma(%__MODULE__{lemmas: ls} = env, head, entry) when is_atom(head),
    do: %{env | lemmas: Map.update(ls, head, [entry], &(&1 ++ [entry]))}

  @doc "The `@lemma` entries filed under conclusion head `head`, or `[]`."
  @spec lemmas(t(), atom()) :: [map()]
  def lemmas(%__MODULE__{lemmas: ls}, head) when is_atom(head), do: Map.get(ls, head, [])

  @doc "Replace the coherence registry (instance table) carried in the env."
  @spec put_coherence(t(), term()) :: t()
  def put_coherence(%__MODULE__{} = env, registry), do: %{env | coherence: registry}

  @doc "The coherence registry (instance table), or nil if none set."
  @spec coherence(t()) :: term()
  def coherence(%__MODULE__{coherence: registry}), do: registry

  @doc """
  Record that global `name` carries interface constraints — a list of
  `%{iface, tyvar, head_arg_index, dict_name}` descriptors, one per `where
  Iface(a)` clause. A concrete call to a constrained global supplies the
  resolved dictionary as a trailing argument (`Cure.Elab.Resolve`).
  """
  @spec put_constrained(t(), atom(), [map()]) :: t()
  def put_constrained(%__MODULE__{constrained: c} = env, name, specs),
    do: %{env | constrained: Map.put(c, owned_name(env, name), specs)}

  @doc "The interface-constraint descriptors for global `name`, or nil."
  @spec constrained(t(), atom()) :: [map()] | nil
  def constrained(%__MODULE__{} = env, name), do: Map.get(env.constrained, resolve_key(env, env.constrained, name))

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
    name = resolve_key(env, env.defs, name)

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
  def certified?(%__MODULE__{} = env, name), do: MapSet.member?(env.certified, resolve_key(env, env.defs, name))

  @doc """
  Mark an already-registered global def as a builtin arithmetic/comparison op,
  keyed by the stable op atom (`:add`, `:lt`, …). The marker lives ON the def
  record; every consumer (the Normalise compute hook, emit inline, GuardLint's
  Z3 translation) resolves through it, never through a bare global name — so a
  user def named `int_add` (whose `add_def` overwrites the whole record and
  carries NO marker) is never builtin-folded/inlined/translated (K2, R1).
  Only `Builtins.seed_ops` produces this marker.
  """
  @spec register_builtin_op(t(), atom(), atom()) :: t()
  def register_builtin_op(%__MODULE__{defs: defs} = env, name, op_key),
    do: %{env | defs: Map.update!(defs, resolve_key(env, defs, name), &Map.put(&1, :builtin_op, op_key))}

  @doc """
  The builtin-op key for `name` (`:add`, `:lt`, …), or nil. Tolerates a nil
  signature (GuardLint may hold `Context.signature/1` = nil) — returns nil.
  """
  @spec builtin_op(t() | nil, atom()) :: atom() | nil
  def builtin_op(nil, _name), do: nil

  def builtin_op(%__MODULE__{} = env, name) do
    case get_def(env, name) do
      %{builtin_op: op} -> op
      _ -> nil
    end
  end

  @doc """
  Mark an already-registered global def as an emit-inline candidate (the
  `Std.Bool` connectives and `Std.Sigma` projections), keyed by the stable
  inline atom (`:and`, `:eq`, `:sigma_first`, …). Same R1 discipline as
  `register_builtin_op/3`: the marker lives ON the def record, so a local def
  shadowing the bare name carries no marker and is never inlined, while a
  re-keyed `Mod#name` import keeps its marker and keeps inlining. Only the
  `Std.Bool`/`Std.Sigma` import path produces this marker.
  """
  @spec register_inline_hint(t(), atom(), atom()) :: t()
  def register_inline_hint(%__MODULE__{defs: defs} = env, name, key),
    do: %{env | defs: Map.update!(defs, resolve_key(env, defs, name), &Map.put(&1, :inline_hint, key))}

  @doc """
  The emit-inline key for `name` (`:and`, `:sigma_first`, …), or nil.
  """
  @spec inline_hint(t() | nil, atom()) :: atom() | nil
  def inline_hint(nil, _name), do: nil

  def inline_hint(%__MODULE__{} = env, name) do
    case get_def(env, name) do
      %{inline_hint: key} -> key
      _ -> nil
    end
  end
end

defmodule Cure.Core.Inductive do
  alias Cure.Core.Grade

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
  @typedoc """
  A definition's or constructor's per-argument quantity. This is the **grade
  carrier** (`Cure.Core.Grade.t/0`), not a bespoke pair: `:erased` is `0`, and
  the other three inhabitants all denote a runtime-present argument.
  """
  @type quantity :: Grade.t()
  @type family :: %{
          :name => atom(),
          :params => telescope(),
          :indices => telescope(),
          :level => non_neg_integer(),
          # Set (to `true`) only by `opaque_family/3` for postulate families the
          # kernel refuses to eliminate; absent on ordinary inductive families.
          optional(:opaque) => boolean()
        }
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
    family_id = Env.resolve_key(env, env.families, family_id)

    case Map.fetch!(b, key) do
      ^family_id ->
        env

      other ->
        raise ArgumentError,
              "builtin key #{inspect(key)} already bound to #{inspect(other)} (cannot rebind to #{inspect(family_id)})"
    end
  end

  def register_builtin(%Env{} = env, key, family_id) do
    family_id = Env.resolve_key(env, env.families, family_id)
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
  Build an OPAQUE (postulate) family signature: constructor-less and marked
  `opaque: true` so the kernel refuses to eliminate it (Agda `postulate T :
  Set`). Distinct from a genuinely-empty inductive — which is unmarked and
  remains ex-falso-eliminable. An opaque type carries values (e.g. `@extern`
  BEAM ops) through the TCB to codegen without the kernel ever inspecting or
  unfolding them. Always parameter-only (no indices).

  `erasure` is the runtime class its values take on the BEAM — declared by
  `@erases(<class>)`, since a family with NO constructors has no erasure to infer.
  `nil` means undeclared, which is what every opaque type that never crosses an
  anonymous union wants. The kernel never reads it; it is elaborator metadata riding
  on the family record.
  """
  @spec opaque_family(atom(), telescope(), non_neg_integer(), atom() | nil) :: family()
  def opaque_family(name, param_tele, level, erasure \\ nil),
    do: %{
      name: name,
      params: param_tele,
      indices: [],
      level: level,
      opaque: true,
      erasure: erasure
    }

  @doc """
  Build a constructor signature. Every argument defaults to runtime-relevant
  (`:unrestricted`, quantity ω); use `ctor/4` to mark inferred index arguments
  `:erased` (quantity 0) so they are dropped by erasure (M8.3 / M9).
  """
  @spec ctor(atom(), telescope(), [Cure.Core.Term.t()]) :: ctor()
  def ctor(name, arg_tele, result_indices),
    do: ctor(name, arg_tele, result_indices, List.duplicate(:unrestricted, length(arg_tele)))

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
    fname = Env.owned_name(env, fname)
    family = %{family | name: fname}
    env = %{env | families: Map.put(env.families, fname, family)}

    Enum.reduce(ctors, env, fn %{name: cname} = c, acc ->
      cname = Env.owned_name(acc, cname)
      c = %{c | name: cname}

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
  def family?(%Env{} = env, name), do: Map.has_key?(env.families, Env.resolve_key(env, env.families, name))

  @doc """
  Is `name` an OPAQUE (postulate) family? The `opaque: true` marker — not the
  constructor count — is what makes a type non-eliminable, so a genuinely-empty
  inductive answers `false` here while `opaque type Effect` answers `true`.
  """
  @spec opaque?(Env.t(), atom()) :: boolean()
  def opaque?(%Env{} = env, name), do: opaque_family?(get_family(env, name))

  @doc "Is `family` (a family map or nil) marked opaque?"
  @spec opaque_family?(family() | nil) :: boolean()
  def opaque_family?(%{opaque: true}), do: true
  def opaque_family?(_), do: false

  @doc "The family signature for `name`, or nil."
  @spec get_family(Env.t(), atom()) :: family() | nil
  def get_family(%Env{} = env, name), do: Map.get(env.families, Env.resolve_key(env, env.families, name))

  @doc "The constructor signature for `name`, or nil."
  @spec get_ctor(Env.t(), atom()) :: ctor() | nil
  def get_ctor(%Env{} = env, name), do: Map.get(env.ctors, Env.resolve_key(env, env.ctors, name))

  @doc "The family a constructor belongs to."
  @spec ctor_family(Env.t(), atom()) :: atom() | nil
  def ctor_family(%Env{} = env, cname),
    do: Map.get(env.ctor_to_family, Env.resolve_key(env, env.ctor_to_family, cname))

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

  @doc """
  A constructor's field count (the length of its argument telescope), or nil when
  the constructor is unknown. This is the single authority for "how many of a
  ctor value's spine slots are FIELDS" — the count both `Eval`'s ι-rule (via the
  branch arity) and `Conv`'s params-on-spine coercion strip down to.
  """
  @spec field_count(Env.t(), atom()) :: non_neg_integer() | nil
  def field_count(env, cname) do
    case arg_telescope(env, cname) do
      tele when is_list(tele) -> length(tele)
      _ -> nil
    end
  end

  @doc "A constructor's per-argument {0,ω} quantities (`:erased` / `:unrestricted`)."
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
  def ctors_of(%Env{} = env, fname) do
    fname = Env.resolve_key(env, env.families, fname)

    cs = env.ctors
    c2f = env.ctor_to_family

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
  # constructor fields (`seen` breaks family cycles). When `fname` occurs inside
  # another family's ARGUMENTS (nested positivity — `Node (List Rose)`), the
  # other family's constructor fields are INSTANTIATED with those arguments and
  # re-checked: a strictly-positive parameter (`List`, `Option`) keeps `fname`
  # positive, a negative one (`Neg t = t -> Empty`) drops it left of an arrow and
  # is rejected. An opaque/constructorless carrier has unknowable polarity and is
  # conservatively rejected.
  defp strictly_positive?(env, fname, {:pi, _g, dom, cod}, seen),
    do: not occurs_deep?(env, fname, dom, seen) and strictly_positive?(env, fname, cod, seen)

  # A recursive occurrence of the family itself is strictly positive ONLY when
  # `fname` does not also occur inside its own parameter/index arguments — the
  # same guard the other-family clause below applies. Without it a negative
  # occurrence buried in the family's own arguments (`Bad ((Bad Unit) -> Empty)`)
  # would be admitted, breaking well-foundedness.
  defp strictly_positive?(env, fname, {:data, fname, ps, is}, _seen),
    do: not Enum.any?(ps ++ is, &occurs?(env, fname, &1))

  defp strictly_positive?(env, fname, {:data, other, ps, is}, seen) do
    args = ps ++ is
    fname_in_args = Enum.any?(args, &occurs?(env, fname, &1))

    cond do
      # Re-entering a family already on the expansion stack — a recursive or
      # mutual occurrence. Greatest-fixpoint: accept (its fields are being
      # verified further up the stack). This is what makes a nested self-call
      # like `Lst(Rose(a))` terminate and admit.
      MapSet.member?(seen, other) ->
        true

      # `fname` is not passed into `other`. Only a direct/mutual reference to
      # `fname` inside `other`'s OWN fields could break positivity; expand and
      # check them (parameters stay bound variables — no instantiation needed).
      not fname_in_args ->
        seen2 = MapSet.put(seen, other)

        env
        |> ctors_of(other)
        |> Enum.all?(fn %{args: fields} ->
          Enum.all?(fields, fn {_n, ty} -> strictly_positive?(env, fname, ty, seen2) end)
        end)

      # `fname` flows into `other`'s arguments, but `other` is opaque
      # (postulate) or constructorless: its parameter polarity is unknowable,
      # so no positive certificate can be issued. Reject (soundly incomplete).
      opaque_or_ctorless?(env, other) ->
        false

      # NESTED positivity (Agda `Positivity.hs` / Coq's "check the instantiated
      # constructors" rule): instantiate `other`'s constructor fields with the
      # ACTUAL arguments and require `fname` to remain strictly positive in each.
      # This drops `fname` into exactly the structural slots where `other` uses
      # each parameter — a negative parameter (`Neg t = t -> Empty`) lands
      # `fname` left of an arrow and is rejected; a positive parameter (`List`,
      # `Option`) keeps it positive.
      true ->
        nt =
          length(param_telescope(env, other) || []) + length(index_telescope(env, other) || [])

        if nt == length(args) do
          seen2 = MapSet.put(seen, other)

          env
          |> ctors_of(other)
          |> Enum.all?(fn ctor ->
            ctor
            |> instantiate_fields(nt, args)
            |> Enum.all?(&strictly_positive?(env, fname, &1, seen2))
          end)
        else
          # Argument arity does not match the declared telescope — the term is
          # malformed for this family; cannot align args to binders. Reject.
          false
        end
    end
  end

  # Any other shape: a type-level application (`Neg Bad`), a type-level λ, a
  # `case`, a bare variable, etc. The kernel has no polarity analysis for these
  # heads, so the family occurring inside one CANNOT be certified strictly
  # positive — `Neg := λt. t -> Empty` makes `Neg Bad` a hidden negative
  # occurrence. The only sound answer is: strictly positive iff the family does
  # not occur at all, mirroring the `:data`-other clause's conservatism (a
  # false-open here admits `False`). An occurrence in a genuinely positive but
  # unanalyzable spot is rejected — soundly incomplete, never unsound.
  defp strictly_positive?(env, fname, other, _seen), do: not occurs?(env, fname, other)

  # An opaque (postulate) or constructorless carrier exposes no constructor
  # fields, so the polarity of its parameters cannot be established. Conservative.
  defp opaque_or_ctorless?(env, other),
    do: opaque?(env, other) or ctors_of(env, other) == []

  # Instantiate a constructor's field telescope by substituting the family's
  # `nt` parameter/index binders with the ACTUAL arguments. Parameters are the
  # outermost binders, so at field position `i` the binder for argument `t`
  # (0-indexed, outermost = 0) sits at de Bruijn index `i + (nt - 1 - t)`; the
  # argument is shifted over the `i` preceding-field binders. `Term.subst` is
  # targeted (it does not renumber the untouched binders) — exactly what the
  # positivity predicates, which match `fname` by head and inspect arrow
  # structure (index-insensitive), require.
  defp instantiate_fields(%{args: field_tele}, nt, args) do
    field_tele
    |> Enum.with_index()
    |> Enum.map(fn {{_n, ty}, i} ->
      Enum.reduce(0..(nt - 1)//1, ty, fn t, acc ->
        j = i + (nt - 1 - t)
        Cure.Core.Term.subst(acc, j, Cure.Core.Term.shift(Enum.at(args, t), i, 0))
      end)
    end)
  end

  # Does `fname` occur anywhere in `ty`, including inside the constructor fields
  # of other families referenced by `ty`? Used for arrow DOMAINS, where any
  # reachable occurrence is a negative position.
  defp occurs_deep?(env, fname, ty, seen) do
    occurs?(env, fname, ty) or
      Enum.any?(data_heads(env, ty), fn other ->
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

  # Every family name appearing as a `{:data, …}` head anywhere in the term,
  # looking THROUGH `{:global, _}` type synonyms — a field written as the bare
  # alias `Wrap` (where `typealias Wrap = W`) must still expose `W` as a head, or
  # `occurs_deep?`'s through-constructor rule never inspects `W`'s fields.
  defp data_heads(env, term),
    do: term |> gather_data_heads(env, MapSet.new(), MapSet.new()) |> MapSet.to_list()

  defp gather_data_heads({:data, n, ps, is}, env, acc, seen),
    do: Enum.reduce(ps ++ is, MapSet.put(acc, n), &gather_data_heads(&1, env, &2, seen))

  defp gather_data_heads({:global, g}, env, acc, seen) do
    if MapSet.member?(seen, g) do
      acc
    else
      case Env.get_def(env, g) do
        %{body: body} when not is_nil(body) ->
          gather_data_heads(body, env, acc, MapSet.put(seen, g))

        _ ->
          acc
      end
    end
  end

  defp gather_data_heads(t, env, acc, seen) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.reduce(acc, &gather_data_heads(&1, env, &2, seen))

  defp gather_data_heads(l, env, acc, seen) when is_list(l),
    do: Enum.reduce(l, acc, &gather_data_heads(&1, env, &2, seen))

  defp gather_data_heads(_t, _env, acc, _seen), do: acc

  # Does the family name `fname` occur anywhere in `term` (as an applied family)?
  #
  # This walker is FAIL-CLOSED: its catch-all descends into any unrecognized
  # tuple/list rather than answering "does not occur". Its callers
  # (`strictly_positive?`, `occurs_deep?`) read `false` as "safe to admit", so a
  # fail-OPEN catch-all here is a soundness hole, not a missing optimization —
  # any Core node shape it failed to enumerate would silently smuggle a negative
  # occurrence past the positivity check. The structural descent makes the
  # enumeration total by construction; it is the same over-approximating pattern
  # `Cure.Core.Kernel.occurs_index?/2` uses. Constructor/family NAMES are atoms,
  # which are leaves, so `fname` is only ever matched against a `{:data, …}` head
  # — never against a name that merely happens to be spelled the same.
  #
  # `{:global, g}` is δ-unfolded before the decision. Agda (`Positivity.hs`),
  # Lean 4 (the `inductive` elaborator) and Idris 2 (`Positivity.idr`) all run
  # the positivity walk over the alias-EXPANDED type, precisely so that
  # `typealias Neg = Bad -> Int` cannot smuggle a negative occurrence of `Bad`
  # into `MkBad : Neg -> Bad` — the classic `MkBad : (Bad -> Nat) -> Bad` paradox
  # constructor, which inhabits `False`.
  #
  # Read the question as: does `fname` occur in `term`'s δ-NORMAL FORM? Then an
  # OPAQUE global (no body, or absent from the signature) normalizes to itself
  # and demonstrably contains no occurrence — `false` is the correct answer, not
  # a fail-open one. This is what keeps `{:app, {:global, :Neg}, Empty}` admitted
  # while `{:app, {:global, :Neg}, Bad}` is still rejected: `Bad` is found in the
  # ARGUMENT by the structural walk, not in the opaque head. A CYCLIC alias has no
  # δ-normal form, so it answers `true` (soundly incomplete, never unsound).
  defp occurs?(env, fname, term), do: occurs?(env, fname, term, MapSet.new())

  defp occurs?(_env, fname, {:data, fname, _ps, _is}, _seen), do: true

  # Defensive: a family is normally referenced as `{:data, fname, _, _}`, never as
  # a bare global, but if the two name spaces ever collide, treat it as an occurrence.
  defp occurs?(_env, fname, {:global, fname}, _seen), do: true

  defp occurs?(env, fname, {:global, g}, seen) do
    if MapSet.member?(seen, g) do
      true
    else
      case Env.get_def(env, g) do
        %{body: body} when not is_nil(body) -> occurs?(env, fname, body, MapSet.put(seen, g))
        _ -> false
      end
    end
  end

  defp occurs?(env, fname, t, seen) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.any?(&occurs?(env, fname, &1, seen))

  defp occurs?(env, fname, l, seen) when is_list(l),
    do: Enum.any?(l, &occurs?(env, fname, &1, seen))

  defp occurs?(_env, _fname, _leaf, _seen), do: false
end
