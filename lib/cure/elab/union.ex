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

  # Recover a union family's canonical members from its registered constructors: a
  # nullary ctor is a literal member, a 1-ary ctor is a type member whose payload is
  # its single argument's type.
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
