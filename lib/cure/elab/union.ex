defmodule Cure.Elab.Union do
  @moduledoc """
  Canonicalisation and family generation for anonymous union types (`Int | String`).

  A union's IDENTITY is its canonical member list: flattened, normalised to full
  normal form, keyed by a type-distinguishing printing, deduped, and lexically
  sorted. That sorted key list *names* the generated family, so `Int | String` and
  `String | Int` produce literally the same `{:data, name}` and are definitionally
  equal with **zero kernel involvement** — no new type former, no conversion rule,
  no subtyping, no cast.

  ## Key format

  A **type** member keys as its printed Core type: `Int`, `List(Int)`.

  A **literal** member keys as `<TypeKey>#<printed value>`: `Int#3`, `String#"4"`,
  `Atom#:4`, `Char#'c'`, `Bool#true`, `Float#4.0`. The `<TypeKey>#` prefix is what
  keeps `"4"` (a `String`) and `:4` (an `Atom`) from colliding on `4`, and it makes
  the literal/type-overlap check a pure string comparison.

  ## Constructor names are family-qualified

  `env.ctors` is a **global flat map** (`Cure.Core.Inductive.declare/3`), so a bare
  `:Int` constructor would collide across two different unions that each have an
  `Int` member, and `ctor_to_family` would point at the wrong family. Constructor
  names are therefore `:"<union_key>$<member_key>"`.

  See `docs/superpowers/specs/2026-07-11-anonymous-adts-design.md`.
  """

  alias Cure.Core.{Context, Env, Inductive, Normalise}

  @type member :: %{
          key: String.t(),
          payload: nil | tuple(),
          lit_type_key: nil | String.t()
        }

  @prefix "Union<"

  # ── Public API ─────────────────────────────────────────────────────────────

  @doc "True iff `atom` is a generated union family key."
  @spec union_family?(atom()) :: boolean()
  def union_family?(atom) when is_atom(atom) do
    atom |> Atom.to_string() |> String.starts_with?(@prefix)
  end

  def union_family?(_), do: false

  @doc """
  The generated family key for a canonical member list: `:"Union<k1|k2|...>"`.

  `<`, `>` and `|` are not producible by the type-name lexer, so a generated key can
  never collide with a user-declared type.
  """
  @spec family_key([member()]) :: atom()
  def family_key(members) do
    inner = members |> Enum.map(& &1.key) |> Enum.join("|")
    String.to_atom(@prefix <> inner <> ">")
  end

  @doc "The constructor name for `member` within family `family_key`."
  @spec ctor_key(atom(), member() | %{key: String.t()}) :: atom()
  def ctor_key(family_key, %{key: k}) do
    String.to_atom(Atom.to_string(family_key) <> "$" <> k)
  end

  @doc """
  The canonical key of a literal, from its surface subtype and value.

  Single source of truth: both `lower_member/3` here and the elaborator's
  check-position literal injection call this, so the two can never drift into
  producing a constructor name that does not exist.
  """
  @spec literal_key(atom(), term()) :: {:ok, String.t()} | :error
  def literal_key(:integer, v) when is_integer(v), do: {:ok, "Int#" <> Integer.to_string(v)}
  def literal_key(:float, v) when is_float(v), do: {:ok, "Float#" <> Float.to_string(v)}
  def literal_key(:string, v) when is_binary(v), do: {:ok, "String#" <> ~s("#{v}")}
  def literal_key(:symbol, v) when is_atom(v), do: {:ok, "Atom#:" <> Atom.to_string(v)}
  def literal_key(:char, v) when is_integer(v), do: {:ok, "Char#'" <> <<v::utf8>> <> "'"}
  def literal_key(:boolean, v) when is_boolean(v), do: {:ok, "Bool#" <> to_string(v)}
  def literal_key(_subtype, _value), do: :error

  @doc """
  Canonicalise a list of surface member ASTs into a sorted, deduped member list.

  Returns `{:error, {:union_member_not_ground, ast}}` for a member with a free type
  variable or an unsolved metavariable, and
  `{:error, {:union_member_overlap, lit_key, type_key}}` for a literal that is
  subsumed by a type member (`Int | 3`).
  """
  @spec canonicalise([tuple()], [String.t()], Env.t()) :: {:ok, [member()]} | {:error, term()}
  def canonicalise(asts, scope, env) do
    with {:ok, raw} <- lower_members(asts, scope, env) do
      members =
        raw
        |> Enum.concat()
        |> Enum.uniq_by(& &1.key)
        |> Enum.sort_by(& &1.key)

      case overlap(members) do
        nil -> {:ok, members}
        {lit_key, type_key} -> {:error, {:union_member_overlap, lit_key, type_key}}
      end
    end
  end

  @doc "The type-distinguishing canonical printing of a lowered, nf'd Core type."
  @spec member_key(tuple()) :: String.t()
  def member_key({:int_type}), do: "Int"
  def member_key({:float_type}), do: "Float"
  def member_key({:binary_type}), do: "Binary"
  def member_key({:atom_type}), do: "Atom"
  def member_key({:type, l}), do: "Type" <> Integer.to_string(l)

  def member_key({:data, name, params, indices}) do
    case params ++ indices do
      [] -> Atom.to_string(name)
      args -> Atom.to_string(name) <> "(" <> Enum.map_join(args, ",", &member_key/1) <> ")"
    end
  end

  def member_key({:nat_lit, n}), do: Integer.to_string(n)
  def member_key({:int_lit, n}), do: Integer.to_string(n)
  def member_key({:float_lit, f}), do: Float.to_string(f)
  def member_key({:bounded_lit, k}), do: Integer.to_string(k)
  def member_key({:atom_lit, a}), do: ":" <> Atom.to_string(a)
  def member_key({:ctor, name, []}), do: Atom.to_string(name)
  def member_key({:global, name}), do: Atom.to_string(name)

  # ── FFI boundary: runtime discrimination ───────────────────────────────────

  @doc """
  The ERASED runtime shape of a member, as the Erlang guard that recognises it.

  This is what makes a union-returning `@extern` possible: Erlang hands back an untagged
  value, and the boundary can only re-tag it if each member is recognisable.

  Note `Bool` is `:boolean`, NOT `:atom`. It erases to the atoms `true`/`false`, but
  `is_boolean/1` is a real, total Erlang guard that strictly REFINES `is_atom/1` — so
  `Bool | Atom` is perfectly discriminable *by order* (see `refines?/2`). The question is
  never "do two members share a class", it is "can one member's guard be ordered before
  the other's".

  `:unsupported` for anything whose erasure is not a single recognisable shape — a user
  ADT erases to a bare atom when nullary and a tagged tuple otherwise, so it is BOTH
  shapes at once and no single guard recognises it.
  """
  @spec runtime_class(member()) :: atom()
  def runtime_class(%{payload: nil, lit_type_key: t}), do: class_of_type_key(t)
  def runtime_class(%{payload: ty}), do: class_of_core(ty)

  defp class_of_core({:int_type}), do: :integer
  defp class_of_core({:float_type}), do: :float
  defp class_of_core({:binary_type}), do: :binary
  defp class_of_core({:atom_type}), do: :atom
  defp class_of_core({:data, :Bool, _p, _i}), do: :boolean
  defp class_of_core({:data, :Nat, _p, _i}), do: :integer
  defp class_of_core({:data, :Bounded, _p, _i}), do: :integer
  defp class_of_core({:data, :List, _p, _i}), do: :list
  defp class_of_core(_other), do: :unsupported

  defp class_of_type_key("Int"), do: :integer
  defp class_of_type_key("Nat"), do: :integer
  defp class_of_type_key("Char"), do: :integer
  defp class_of_type_key("Float"), do: :float
  defp class_of_type_key("Binary"), do: :binary
  defp class_of_type_key("Atom"), do: :atom
  defp class_of_type_key("Bool"), do: :boolean
  defp class_of_type_key("String"), do: :list
  defp class_of_type_key(_other), do: :unsupported

  @doc """
  Does guard class `a` strictly REFINE class `b` — i.e. is every value `a` accepts also
  accepted by `b`, so that ordering `a` first discriminates them?

  `is_boolean/1` ⊂ `is_atom/1` is the only such pair among Cure's erased shapes.

  Deliberately NOT extended to `Nat`/`Char` ⊂ `Int`: those would need a range predicate,
  and the resulting precedence ("a small non-negative integer is ALWAYS a Nat, never an
  Int") is surprising in a way "`true` is always a Bool" is not. They stay rejected.
  """
  @spec refines?(atom(), atom()) :: boolean()
  def refines?(:boolean, :atom), do: true
  def refines?(_a, _b), do: false

  @doc """
  Can every member of this union be told apart from an untagged Erlang value?

  Returns `:ok`, or `{:error, reason}` naming the members that cannot be separated.

  Discrimination is ORDERED, most-specific-first:

    1. **Literal** members test the exact value (`R =:= north`). An exact test refines
       every class guard, so a literal may freely share a class with a type member — the
       sentinel pattern `3 | Nat` ("a raw 3 is the sentinel, any other integer is a Nat")
       is admissible and total.
    2. **Type** members test their class guard, ordered so that a refining guard comes
       first — `Bool` (`is_boolean`) before `Atom` (`is_atom`).

  Two TYPE members conflict only when they share a class and neither refines the other:
  `Int | Nat` (both integers), `String | List(Int)` (both lists). No order separates
  those, so they are rejected.
  """
  @spec discriminable([member()]) :: :ok | {:error, term()}
  def discriminable(members) do
    {lits, types} = Enum.split_with(members, &(&1.payload == nil))

    classes = Enum.map(types ++ lits, &{&1.key, runtime_class(&1)})
    unsupported = for {k, :unsupported} <- classes, do: k

    # Only TYPE members can collide: a literal is an exact-value test, which refines any
    # class guard and is emitted first.
    collisions =
      for {ka, ca} <- Enum.map(types, &{&1.key, runtime_class(&1)}),
          {kb, cb} <- Enum.map(types, &{&1.key, runtime_class(&1)}),
          ka < kb,
          ca == cb or (not refines?(ca, cb) and not refines?(cb, ca) and ca == cb),
          do: {ka, kb, ca}

    cond do
      unsupported != [] -> {:error, {:unsupported_member_shape, unsupported}}
      collisions != [] -> {:error, {:same_runtime_shape, collisions}}
      true -> :ok
    end
  end

  @doc """
  Members ordered for runtime discrimination: literals (exact value) first, then type
  members with refining guards ahead of the guards they refine.
  """
  @spec discrimination_order([member()]) :: [member()]
  def discrimination_order(members) do
    {lits, types} = Enum.split_with(members, &(&1.payload == nil))

    sorted_types =
      Enum.sort(types, fn a, b ->
        refines?(runtime_class(a), runtime_class(b))
      end)

    lits ++ sorted_types
  end

  @doc """
  The literal value behind a LITERAL member's key, for building an equality guard.

  The key format is `<TypeKey>#<printed>` and we generated it, so this is a total inverse
  for the six literal type-keys. Only ever called on a NULLARY ctor's key, so a rekeyed
  module-qualified TYPE name (`Std.Foo#Foo`, which also contains `#`) can never reach it.
  """
  @spec literal_value(String.t()) :: {:ok, atom(), term()} | :error
  def literal_value(key) do
    case String.split(key, "#", parts: 2) do
      ["Int", v] -> {:ok, :integer, String.to_integer(v)}
      ["Nat", v] -> {:ok, :integer, String.to_integer(v)}
      ["Float", v] -> {:ok, :float, String.to_float(v)}
      ["Bool", v] -> {:ok, :atom, v == "true"}
      ["Atom", ":" <> v] -> {:ok, :atom, String.to_atom(v)}
      ["Char", <<?', c::utf8, ?'>>] -> {:ok, :integer, c}
      ["String", <<?", rest::binary>>] -> {:ok, :string, String.trim_trailing(rest, "\"")}
      _ -> :error
    end
  end

  # ── Family generation ──────────────────────────────────────────────────────

  @doc """
  Declare the generated family for a union's surface members, idempotently.

  Returns `{:ok, env, {:data, key, [], []}}` for a real union, or `{:ok, env, core}`
  for a one-member union of a TYPE member, which collapses to that member itself —
  no family is generated. A one-member union of a LITERAL member still needs a
  family: there is no Core term for a bare literal in type position.
  """
  @spec declare([tuple()], [String.t()], Env.t()) :: {:ok, Env.t(), tuple()} | {:error, term()}
  def declare(asts, scope, env) do
    with {:ok, members} <- canonicalise(asts, scope, env) do
      case members do
        [%{payload: payload}] when payload != nil -> {:ok, env, payload}
        _ -> declare_family(members, env)
      end
    end
  end

  defp declare_family(members, env) do
    key = family_key(members)

    if Inductive.family?(env, key) do
      # Idempotent: the key is content-derived, so re-declaring an identical family
      # would be an identical Map.put.
      {:ok, env, {:data, key, [], []}}
    else
      ctors =
        Enum.map(members, fn m ->
          cname = ctor_key(key, m)

          case m.payload do
            nil -> Inductive.ctor(cname, [], [], [], [])
            ty -> Inductive.ctor(cname, [{:v, ty}], [], [Cure.Core.Grade.unrestricted()], [])
          end
        end)

      case Cure.Elab.Declarations.declare_generated_family(env, key, ctors) do
        {:ok, env2} -> {:ok, env2, {:data, key, [], []}}
        {:error, _} = err -> err
      end
    end
  end

  @doc """
  Walk a declaration's AST, declaring the family for every `{:union_type, …}` in it.

  This exists as a PRE-PASS because `idx_to_core/5` returns `{:ok, term}` and cannot
  thread a mutated `Env` back out to its callers — so a union family cannot be
  declared as a side-effect of type lowering. `Declarations.elaborate/2` *does*
  return `{:ok, Env.t()}`, so the declaration happens there and lowering merely looks
  the key up.
  """
  @spec predeclare_all(term(), Env.t()) :: {:ok, Env.t()} | {:error, term()}
  def predeclare_all(ast, env) do
    ast
    |> collect_unions()
    |> Enum.reduce_while({:ok, env}, fn {:union_type, _meta, members}, {:ok, env} ->
      case declare(members, [], env) do
        {:ok, env2, _core} -> {:cont, {:ok, env2}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # Innermost-first, so a nested union has its inner family declared before the outer
  # one tries to splice it in.
  defp collect_unions(node) when is_tuple(node) do
    inner = node |> Tuple.to_list() |> Enum.flat_map(&collect_unions/1)
    if match?({:union_type, _, _}, node), do: inner ++ [node], else: inner
  end

  defp collect_unions(list) when is_list(list), do: Enum.flat_map(list, &collect_unions/1)
  defp collect_unions(_other), do: []

  # ── Lowering ───────────────────────────────────────────────────────────────

  defp lower_members(asts, scope, env) do
    Enum.reduce_while(asts, {:ok, []}, fn ast, {:ok, acc} ->
      case lower_member(ast, scope, env) do
        {:ok, ms} -> {:cont, {:ok, acc ++ [ms]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # A LITERAL member becomes a NULLARY constructor: the value is fully determined by
  # the constructor, so there is nothing to store.
  defp lower_member({:literal, meta, value} = ast, _scope, _env) do
    case literal_key(Keyword.get(meta, :subtype), value) do
      {:ok, key} ->
        [type_key, _printed] = String.split(key, "#", parts: 2)
        {:ok, [%{key: key, payload: nil, lit_type_key: type_key}]}

      :error ->
        {:error, {:union_member_not_ground, ast}}
    end
  end

  # A TYPE member is lowered to Core and reduced to FULL normal form.
  #
  # `nf`, not `whnf`: plain evaluation leaves a neutral global application inside an
  # index (`Bounded(1+1)`) stuck rather than folding it to `Bounded(2)`. Without full
  # normal form, two definitionally-equal ground members would print as different
  # keys and silently produce two distinct families for one type.
  defp lower_member(ast, scope, env) do
    with {:ok, core} <- Cure.Elab.Declarations.lower_type(ast, scope, env) do
      case Normalise.nf(Context.empty(env), core, delta: :certified) do
        :fuel_exhausted ->
          {:error, {:union_member_not_ground, ast}}

        nf ->
          cond do
            # A member that is ITSELF a union splices its members in — this is how
            # `(A | B) | C` flattens and how a `typealias P = Int | String` used as a
            # member unfolds.
            match?({:data, _, [], []}, nf) and union_family?(elem(nf, 1)) ->
              {:ok, explode(env, elem(nf, 1))}

            ground?(nf, env) ->
              {:ok, [%{key: member_key(nf), payload: nf, lit_type_key: nil}]}

            true ->
              {:error, {:union_member_not_ground, ast}}
          end
      end
    end
  end

  @doc """
  Recover a union family's canonical members from its registered constructors: a nullary
  ctor is a literal member, a 1-ary ctor is a type member whose payload is its single
  argument's type.
  """
  @spec members_of(Env.t(), atom()) :: [member()]
  def members_of(env, family_key), do: explode(env, family_key)

  defp explode(env, family_key) do
    prefix = Atom.to_string(family_key) <> "$"

    env
    |> Inductive.ctors_of(family_key)
    |> Enum.map(fn ctor ->
      key = ctor.name |> Atom.to_string() |> String.replace_prefix(prefix, "")

      case ctor.args do
        [] -> %{key: key, payload: nil, lit_type_key: lit_type_key_of(key)}
        [{_name, ty}] -> %{key: key, payload: ty, lit_type_key: nil}
      end
    end)
  end

  # "Int#3" -> "Int". Only ever called on a key that came from a NULLARY ctor, i.e. a
  # literal member, which always has the `<TypeKey>#<value>` shape.
  defp lit_type_key_of(key) do
    case String.split(key, "#", parts: 2) do
      [t, _v] -> t
      _ -> nil
    end
  end

  # A member is ground iff its Core term has no free variables and no metavariables.
  # Members are lowered in an empty scope, so any `{:var, _}` is by definition free.
  #
  # A bare lowercase name that resolves to nothing lowers to `{:global, name}` rather
  # than `{:var, _}`, so an unbound `{:global, _}` is also rejected — that is the
  # `a | Int` case.
  defp ground?(term, env) do
    not has?(term, fn
      {:var, _} -> true
      {:meta, _} -> true
      {:global, n} -> not known_global?(env, n)
      _ -> false
    end)
  end

  defp known_global?(env, name) do
    Inductive.family?(env, name) or Env.get_def(env, name) != nil
  end

  defp has?(term, pred) when is_tuple(term) do
    if pred.(term) do
      true
    else
      term |> Tuple.to_list() |> Enum.any?(&has?(&1, pred))
    end
  end

  defp has?(list, pred) when is_list(list), do: Enum.any?(list, &has?(&1, pred))
  defp has?(_other, _pred), do: false

  # ── Admission: literal/type overlap ────────────────────────────────────────

  # Reject iff some literal member's type is itself a type member: `Int | 3` admits
  # two distinct injections for `3` and there is no subtyping to break the tie.
  #
  # Runs on the CANONICAL (post-normalisation) member list, so `typealias T = Int`
  # followed by `T | 3` is caught too — the checker sees the unfolded `Int`, not the
  # opaque alias name.
  defp overlap(members) do
    type_keys = for %{lit_type_key: nil, key: k} <- members, into: MapSet.new(), do: k

    Enum.find_value(members, fn
      %{lit_type_key: nil} ->
        nil

      %{lit_type_key: lt, key: k} ->
        if MapSet.member?(type_keys, lt), do: {k, lt}, else: nil
    end)
  end
end
