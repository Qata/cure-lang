defmodule Cure.Core.Term do
  @moduledoc """
  Explicit, fully-annotated Core terms for the trusted dependent-type kernel.

  Terms are plain tagged tuples using de Bruijn indices for bound variables.
  This is the soundness-critical representation described in the design spec
  §4.1; it deliberately carries no implicits, holes, or erasure annotations
  (those live only in the surface/elaborator) — a checked Core term is fully
  explicit and fully relevant.

  Node taxonomy (de Bruijn):

    * `{:type, level}`                       universe, `level` in 0..2
    * `{:var, k}`                            bound variable, de Bruijn index `k >= 0`
    * `{:pi, dom, cod}`                      dependent function type (binds in `cod`)
    * `{:lam, dom, body}`                    lambda (binds in `body`)
    * `{:let, ty, val, body}`                let-binding (binds in `body`);
                                             ζ-transparent: the variable is
                                             definitionally `val`. Idris
                                             `Binder.Let`, Lean `Expr.letE`.
    * `{:app, f, a}`                         application
    * `{:data, name, params, indices}`       family applied to params + indices
    * `{:ctor, name, args}`                  data constructor application
    * `{:case, scrut, motive, branches}`     dependent eliminator;
                                             `branches :: [{ctor_name, arity, body}]`
    * `{:global, name}`                      reference to a global def
    * `{:int_type}` / `{:int_lit, n}`        integer type / literal
    * `{:float_type}` / `{:float_lit, f}`    float type / literal
    * `{:binary_type}`                       BEAM binary base type (Int-tier)
    * `{:atom_type}` / `{:atom_lit, a}`      BEAM atom base type / literal (`a`
                                             an atom); the atom is its own
                                             canonical value (Int-tier prim)
    * `{:nat_lit, n}`                        compact Nat literal (`n >= 0`),
                                             definitionally equal to the n-fold
                                             `S`-tower over `Z` (Lean kernel Nat /
                                             Agda BUILTIN NATURAL — a compact
                                             literal form for `Nat` values, not a
                                             separate primitive type)
    (Bool and Nat are real inductive families, not primitive term forms.)
  """

  # Single source of truth for the universe ceiling is `Cure.Core.Universe`; this
  # module only mirrors the value into its compile-time shape-check guards.
  @ceiling Cure.Core.Universe.ceiling()

  @typedoc "A `:case` branch: constructor name, its arity, and the branch body."
  @type branch :: {atom(), non_neg_integer(), t()}

  @typedoc """
  A Core term — the node taxonomy above, as a closed union.

  This is deliberately NOT `tuple()`. Written loosely, Dialyzer and Elixir's
  set-theoretic checker are blind to binder shape: a wrong-arity `{:pi, dom}`
  or a pattern that can never match sails straight through. Written precisely,
  both catch it statically, which is the only cheap net over a taxonomy that is
  reshaped from time to time (the QTT grade reshape being the current one).
  """
  @type t ::
          {:type, non_neg_integer()}
          | {:var, non_neg_integer()}
          | {:pi, t(), t()}
          | {:lam, t(), t()}
          | {:let, t(), t(), t()}
          | {:app, t(), t()}
          | {:data, atom(), [t()], [t()]}
          | {:ctor, atom(), [t()]}
          | {:case, t(), t(), [branch()]}
          | {:global, atom()}
          | {:int_type}
          | {:int_lit, integer()}
          | {:nat_lit, non_neg_integer()}
          | {:bounded_lit, non_neg_integer()}
          | {:float_type}
          | {:float_lit, float()}
          | {:binary_type}
          | {:atom_type}
          | {:atom_lit, atom()}
          | {:hole, atom() | String.t()}
          | {:absurd}

  @doc "Highest universe level (inclusive). The fixed hierarchy is `Type 0 : Type 1 : Type 2`."
  @spec ceiling() :: non_neg_integer()
  def ceiling, do: Cure.Core.Universe.ceiling()

  @doc """
  True when `term` is a structurally well-formed Core term.

  This is a shape check only — it validates node arities, the universe-level
  bound (`0..#{@ceiling}`), and non-negative de Bruijn indices, recursively.
  It does not type-check; that is the kernel's job.
  """
  @spec term?(term()) :: boolean()
  def term?({:type, level}), do: is_integer(level) and level >= 0 and level <= @ceiling
  def term?({:var, k}), do: is_integer(k) and k >= 0
  def term?({:pi, dom, cod}), do: term?(dom) and term?(cod)
  def term?({:lam, dom, body}), do: term?(dom) and term?(body)
  def term?({:let, ty, val, body}), do: term?(ty) and term?(val) and term?(body)
  def term?({:app, f, a}), do: term?(f) and term?(a)

  def term?({:data, name, params, indices}),
    do: is_atom(name) and terms?(params) and terms?(indices)

  def term?({:ctor, name, args}), do: is_atom(name) and terms?(args)

  def term?({:case, scrut, motive, branches}),
    do: term?(scrut) and term?(motive) and branches?(branches)

  def term?({:global, name}), do: is_atom(name)

  def term?({:int_type}), do: true
  def term?({:int_lit, n}), do: is_integer(n)
  def term?({:nat_lit, n}), do: is_integer(n) and n >= 0
  def term?({:bounded_lit, n}), do: is_integer(n) and n >= 0
  def term?({:float_type}), do: true
  def term?({:float_lit, f}), do: is_float(f)
  def term?({:binary_type}), do: true
  def term?({:atom_type}), do: true
  def term?({:atom_lit, a}), do: is_atom(a)

  # A hole is a live Core node — `Kernel.check/3` accepts one at any type, and a definition
  # mid-development legitimately contains them (only the release/emit boundary rejects
  # them). It carries no de Bruijn variables, so it is an inert leaf everywhere below.
  def term?({:hole, name}), do: is_binary(name)

  # Likewise `{:absurd}`: `Kernel.check/3` admits it against any type once the context is
  # inconsistent, `Serialize` encodes and decodes it, and `Validator` has a clause for it.
  def term?({:absurd}), do: true

  def term?(_), do: false

  # -- de Bruijn shift / substitution -----------------------------------------
  #
  # Binder convention: `:pi`/`:lam` introduce exactly one binder in
  # their codomain/body. A `:case` branch `{ctor, arity, body}` binds `arity`
  # variables in `body`. Motives (`:case`/`:rewrite`) are represented as
  # lambda-chains, so their binders are the ordinary `:lam` nodes inside them
  # and need no special counting here (confirmed by the M4 case-eliminator).

  @doc "Lift every free de Bruijn variable (index ≥ `cutoff`) by `amount`."
  @spec shift(t(), integer(), non_neg_integer()) :: t()
  def shift(term, amount, cutoff \\ 0)

  def shift({:var, k}, amount, cutoff) when k >= cutoff, do: {:var, k + amount}
  def shift({:var, _} = v, _amount, _cutoff), do: v
  def shift({:type, _} = t, _amount, _cutoff), do: t
  def shift({:global, _} = t, _amount, _cutoff), do: t

  # Literals / type constants bind nothing and contain no variables: identity.
  def shift({:int_type} = t, _amount, _cutoff), do: t
  def shift({:int_lit, _} = t, _amount, _cutoff), do: t
  def shift({:nat_lit, _} = t, _amount, _cutoff), do: t
  def shift({:bounded_lit, _} = t, _amount, _cutoff), do: t
  def shift({:float_type} = t, _amount, _cutoff), do: t
  def shift({:float_lit, _} = t, _amount, _cutoff), do: t
  def shift({:binary_type} = t, _amount, _cutoff), do: t
  def shift({:atom_type} = t, _amount, _cutoff), do: t
  def shift({:atom_lit, _} = t, _amount, _cutoff), do: t
  def shift({:hole, _} = t, _amount, _cutoff), do: t
  def shift({:pi, dom, cod}, a, c), do: {:pi, shift(dom, a, c), shift(cod, a, c + 1)}
  def shift({:lam, dom, body}, a, c), do: {:lam, shift(dom, a, c), shift(body, a, c + 1)}
  # `ty` and `val` live OUTSIDE the binder; only `body` is one deeper.
  def shift({:let, ty, val, body}, a, c),
    do: {:let, shift(ty, a, c), shift(val, a, c), shift(body, a, c + 1)}
  def shift({:app, f, x}, a, c), do: {:app, shift(f, a, c), shift(x, a, c)}

  def shift({:data, n, ps, is}, a, c),
    do: {:data, n, Enum.map(ps, &shift(&1, a, c)), Enum.map(is, &shift(&1, a, c))}

  def shift({:ctor, n, args}, a, c), do: {:ctor, n, Enum.map(args, &shift(&1, a, c))}

  def shift({:case, s, m, brs}, a, c),
    do: {:case, shift(s, a, c), shift(m, a, c), Enum.map(brs, fn {cn, ar, b} -> {cn, ar, shift(b, a, c + ar)} end)}



  @doc """
  Is `term` closed (no free de Bruijn variables)?

  A closed term has no variable index that escapes its own binders. Only a
  genuine free `{:var, k}` counts as open — non-variable leaves (`{:hole, _}`,
  globals, types, literals) are closed. The binder structure mirrors `shift/3`
  exactly (the trusted source of truth): `:lam`/`:pi` bind one variable
  in their body/codomain, and each `:case` branch binds `arity`; every other form
  is traversed at the same depth. Kept in lockstep with `shift/3` — if a new
  binding form is added there, add it here.
  """
  @spec closed?(t()) :: boolean()
  def closed?(term), do: not has_free_var?(term, 0)

  defp has_free_var?({:var, k}, depth), do: k >= depth
  defp has_free_var?({:lam, d, b}, depth), do: has_free_var?(d, depth) or has_free_var?(b, depth + 1)

  defp has_free_var?({:let, t, v, b}, depth),
    do: has_free_var?(t, depth) or has_free_var?(v, depth) or has_free_var?(b, depth + 1)
  defp has_free_var?({:pi, d, c}, depth), do: has_free_var?(d, depth) or has_free_var?(c, depth + 1)

  defp has_free_var?({:case, s, m, brs}, depth) do
    has_free_var?(s, depth) or has_free_var?(m, depth) or
      Enum.any?(brs, fn {_c, ar, b} -> has_free_var?(b, depth + ar) end)
  end

  # Non-binding forms: recurse into every sub-term at the same depth. Covers
  # :app/:ctor/:data/:eq/:refl/:rewrite/:prim and anything else.
  defp has_free_var?(t, depth) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.any?(&has_free_var?(&1, depth))

  defp has_free_var?(l, depth) when is_list(l), do: Enum.any?(l, &has_free_var?(&1, depth))
  defp has_free_var?(_leaf, _depth), do: false

  @doc """
  Substitute the de Bruijn index `j` with `replacement` everywhere it occurs.

  Descends under binders, incrementing the target index and shifting the
  replacement so its free variables are not captured. This is a targeted
  substitution (it replaces index `j`; it does not renumber the others).
  """
  @spec subst(t(), non_neg_integer(), t()) :: t()
  def subst({:var, k}, j, r) when k == j, do: r
  def subst({:var, _} = v, _j, _r), do: v
  def subst({:type, _} = t, _j, _r), do: t
  def subst({:global, _} = t, _j, _r), do: t

  # Literals / type constants bind nothing and contain no variables: identity.
  def subst({:int_type} = t, _j, _r), do: t
  def subst({:int_lit, _} = t, _j, _r), do: t
  def subst({:nat_lit, _} = t, _j, _r), do: t
  def subst({:bounded_lit, _} = t, _j, _r), do: t
  def subst({:float_type} = t, _j, _r), do: t
  def subst({:float_lit, _} = t, _j, _r), do: t
  def subst({:binary_type} = t, _j, _r), do: t
  def subst({:atom_type} = t, _j, _r), do: t
  def subst({:atom_lit, _} = t, _j, _r), do: t
  def subst({:hole, _} = t, _j, _r), do: t

  def subst({:pi, dom, cod}, j, r),
    do: {:pi, subst(dom, j, r), subst(cod, j + 1, shift(r, 1, 0))}

  def subst({:lam, dom, body}, j, r),
    do: {:lam, subst(dom, j, r), subst(body, j + 1, shift(r, 1, 0))}

  def subst({:let, ty, val, body}, j, r),
    do: {:let, subst(ty, j, r), subst(val, j, r), subst(body, j + 1, shift(r, 1, 0))}

  def subst({:app, f, x}, j, r), do: {:app, subst(f, j, r), subst(x, j, r)}

  def subst({:data, n, ps, is}, j, r),
    do: {:data, n, Enum.map(ps, &subst(&1, j, r)), Enum.map(is, &subst(&1, j, r))}

  def subst({:ctor, n, args}, j, r), do: {:ctor, n, Enum.map(args, &subst(&1, j, r))}

  def subst({:case, s, m, brs}, j, r),
    do:
      {:case, subst(s, j, r), subst(m, j, r),
       Enum.map(brs, fn {cn, ar, b} -> {cn, ar, subst(b, j + ar, shift(r, ar, 0))} end)}


  # -- serialization (commitment C2) ------------------------------------------
  #
  # A language-agnostic, JSON-able encoding (maps / lists / strings / ints) so
  # an independent checker can re-validate the same Core terms. No PIDs, refs,
  # or closures appear in Core terms, so the encoding is total and reversible.

  @doc "Encode a Core term as a JSON-able map."
  @spec to_external(t()) :: map()
  def to_external({:type, l}), do: %{"node" => "type", "level" => l}
  def to_external({:var, k}), do: %{"node" => "var", "index" => k}
  def to_external({:pi, d, c}), do: %{"node" => "pi", "dom" => to_external(d), "cod" => to_external(c)}

  def to_external({:lam, d, b}),
    do: %{"node" => "lam", "dom" => to_external(d), "body" => to_external(b)}

  def to_external({:let, t, v, b}),
    do: %{
      "node" => "let",
      "type" => to_external(t),
      "value" => to_external(v),
      "body" => to_external(b)
    }

  def to_external({:app, f, a}),
    do: %{"node" => "app", "fun" => to_external(f), "arg" => to_external(a)}

  def to_external({:data, n, ps, is}),
    do: %{
      "node" => "data",
      "name" => Atom.to_string(n),
      "params" => Enum.map(ps, &to_external/1),
      "indices" => Enum.map(is, &to_external/1)
    }

  def to_external({:ctor, n, args}),
    do: %{"node" => "ctor", "name" => Atom.to_string(n), "args" => Enum.map(args, &to_external/1)}

  def to_external({:case, s, m, brs}),
    do: %{
      "node" => "case",
      "scrut" => to_external(s),
      "motive" => to_external(m),
      "branches" =>
        Enum.map(brs, fn {cn, ar, b} ->
          %{"ctor" => Atom.to_string(cn), "arity" => ar, "body" => to_external(b)}
        end)
    }

  def to_external({:global, n}), do: %{"node" => "global", "name" => Atom.to_string(n)}

  def to_external({:int_type}), do: %{"node" => "int_type"}
  def to_external({:int_lit, n}), do: %{"node" => "int_lit", "value" => n}
  def to_external({:nat_lit, n}), do: %{"node" => "nat_lit", "value" => n}
  def to_external({:bounded_lit, n}), do: %{"node" => "bounded_lit", "value" => n}
  def to_external({:float_type}), do: %{"node" => "float_type"}
  def to_external({:float_lit, f}), do: %{"node" => "float_lit", "value" => f}
  def to_external({:binary_type}), do: %{"node" => "binary_type"}
  def to_external({:atom_type}), do: %{"node" => "atom_type"}
  def to_external({:atom_lit, a}), do: %{"node" => "atom_lit", "value" => Atom.to_string(a)}
  def to_external({:hole, name}), do: %{"node" => "hole", "name" => name}

  @doc "Decode a JSON-able map produced by `to_external/1` back into a Core term."
  @spec from_external(map()) :: t()
  def from_external(%{"node" => "type", "level" => l}), do: {:type, l}
  def from_external(%{"node" => "var", "index" => k}), do: {:var, k}

  def from_external(%{"node" => "pi", "dom" => d, "cod" => c}),
    do: {:pi, from_external(d), from_external(c)}

  def from_external(%{"node" => "lam", "dom" => d, "body" => b}),
    do: {:lam, from_external(d), from_external(b)}

  def from_external(%{"node" => "let", "type" => t, "value" => v, "body" => b}),
    do: {:let, from_external(t), from_external(v), from_external(b)}

  def from_external(%{"node" => "app", "fun" => f, "arg" => a}),
    do: {:app, from_external(f), from_external(a)}

  def from_external(%{"node" => "data", "name" => n, "params" => ps, "indices" => is}),
    do: {:data, sym_atom(n), Enum.map(ps, &from_external/1), Enum.map(is, &from_external/1)}

  def from_external(%{"node" => "ctor", "name" => n, "args" => args}),
    do: {:ctor, sym_atom(n), Enum.map(args, &from_external/1)}

  def from_external(%{"node" => "case", "scrut" => s, "motive" => m, "branches" => brs}),
    do:
      {:case, from_external(s), from_external(m),
       Enum.map(brs, fn %{"ctor" => cn, "arity" => ar, "body" => b} ->
         {sym_atom(cn), ar, from_external(b)}
       end)}

  def from_external(%{"node" => "global", "name" => n}), do: {:global, sym_atom(n)}

  def from_external(%{"node" => "int_type"}), do: {:int_type}
  def from_external(%{"node" => "int_lit", "value" => n}), do: {:int_lit, n}
  def from_external(%{"node" => "nat_lit", "value" => n}), do: {:nat_lit, n}
  def from_external(%{"node" => "bounded_lit", "value" => n}), do: {:bounded_lit, n}
  def from_external(%{"node" => "float_type"}), do: {:float_type}
  def from_external(%{"node" => "float_lit", "value" => f}), do: {:float_lit, f}
  def from_external(%{"node" => "binary_type"}), do: {:binary_type}
  def from_external(%{"node" => "atom_type"}), do: {:atom_type}
  def from_external(%{"node" => "atom_lit", "value" => a}), do: {:atom_lit, String.to_atom(a)}
  def from_external(%{"node" => "hole", "name" => name}) when is_binary(name), do: {:hole, name}

  # -- helpers ----------------------------------------------------------------

  # Bounded symbol interning (K12 / spec §D): decode names into EXISTING atoms
  # only, so untrusted JSON `from_external` input cannot exhaust the atom table
  # (it never shrinks). An unknown symbol raises here — consistent with this
  # function's already-partial contract (a malformed map hits no clause and
  # raises too) — rather than minting a permanent atom. Every symbol in a real
  # term is already interned by the compiler, so valid terms still decode.
  defp sym_atom(n), do: String.to_existing_atom(n)

  defp terms?(list) when is_list(list), do: Enum.all?(list, &term?/1)
  defp terms?(_), do: false

  defp branches?(list) when is_list(list), do: Enum.all?(list, &branch?/1)
  defp branches?(_), do: false

  defp branch?({ctor_name, arity, body})
       when is_atom(ctor_name) and is_integer(arity) and arity >= 0,
       do: term?(body)

  defp branch?(_), do: false
end
