defmodule Cure.Types.Reduce do
  @moduledoc """
  Type-level expression normalization for the Cure type system.

  Many dependent-type idioms in Cure require comparing types up to
  *definitional equality*. For example:

      fn append(xs: Vector(T, m), ys: Vector(T, n)) -> Vector(T, m + n)

  At the call site `append(a, b)` where `a : Vector(T, 3)` and
  `b : Vector(T, 5)`, we want the inferred result type
  `Vector(T, 3 + 5)` to be considered equal to `Vector(T, 8)` without
  ever leaving the type checker.

  This module performs a small, terminating, syntactic reduction over
  type-level expressions:

  - **Arithmetic**: `+`, `-`, `*`, `/` on integer literals.
  - **Boolean**: `and`, `or`, `not`, comparisons over literals.
  - **Substitution**: replace free variables with concrete value ASTs.
  - **Sigma projection**: `pair.0`, `pair.1` when `pair` is a literal
    tuple.

  Anything not reducible is left untouched. The result is *always*
  syntactically smaller-or-equal to the input.

  ## Usage

      iex> ast = {:binary_op, [operator: :+], [
      ...>   {:literal, [subtype: :integer], 3},
      ...>   {:literal, [subtype: :integer], 5}
      ...> ]}
      iex> Cure.Types.Reduce.normalize(ast, %{})
      {:literal, [subtype: :integer], 8}

      iex> ast = {:binary_op, [operator: :+], [
      ...>   {:variable, [], "n"},
      ...>   {:literal, [subtype: :integer], 1}
      ...> ]}
      iex> Cure.Types.Reduce.normalize(ast, %{"n" => {:literal, [subtype: :integer], 4}})
      {:literal, [subtype: :integer], 5}

  ## Definitional equality

  `equal?/3` compares two type-level expressions after normalization.
  This is the workhorse that makes dependent-type return signatures
  feel "smart" without dragging in a full SMT call for trivial cases.
  """

  alias Cure.Core.{Builtins, Context, Env, Normalise}
  alias Cure.Types.CoreBridge

  @type ast :: tuple() | atom() | number() | binary()
  @type bindings :: %{optional(String.t()) => ast()}

  # -- Public API --------------------------------------------------------------

  @doc """
  Normalize a type-level expression AST under the given bindings.

  Bindings map free variable names to their concrete AST values.
  Unknown variables are left as-is.
  """
  @spec normalize(ast(), bindings()) :: ast()
  def normalize(ast, bindings \\ %{}) do
    ast |> do_substitute(bindings) |> kernel_normalize()
  end

  # The Boolean connectives `and`/`or`/`not` are no longer `Cure.Core` primitives
  # (they were retired to Std.Bool `case`-defs). `Cure.Core.Eval` therefore no
  # longer folds them, so this non-dependent type-level reducer folds Boolean
  # LITERAL connectives itself — reproducing the deleted primitive fold exactly
  # (strict: folds only when both operands are concrete booleans; otherwise the
  # node is rebuilt with normalized children). Arithmetic and numeric comparisons
  # still fold in the kernel via `Cure.Core.Eval`.
  defp kernel_normalize({:binary_op, meta, [l, r]} = ast) do
    case Keyword.get(meta, :operator) do
      op when op in [:and, :or] -> fold_bool_binop(op, kernel_normalize(l), kernel_normalize(r), ast)
      _ -> kernel_normalize_via_core(ast)
    end
  end

  defp kernel_normalize({:unary_op, meta, [operand]} = ast) do
    case Keyword.get(meta, :operator) do
      :not -> fold_bool_not(kernel_normalize(operand), ast)
      _ -> kernel_normalize_via_core(ast)
    end
  end

  defp kernel_normalize(ast), do: kernel_normalize_via_core(ast)

  # Every other reduction happens in the trusted kernel (normalization-by-
  # evaluation). A node inside the dependent-index grammar is translated,
  # normalized under the SIGNATURE-CARRYING kernel engine (K2 §1.4: builtin-op
  # global spines fold only via the certified-δ hook, which needs the seeded op
  # defs — bare `Eval.eval([])` leaves them stuck), and read back; an
  # irreducible type former (named ref, refinement, n-ary tuple) has no kernel
  # reduction, so we keep its shape and normalize each child through the kernel
  # in turn. No arithmetic is folded outside `Cure.Core`.
  defp kernel_normalize_via_core(ast) do
    case CoreBridge.to_core(ast) do
      {:ok, core} ->
        Context.empty(seeded_env())
        |> Normalise.nf(core, delta: :certified)
        |> CoreBridge.from_core()

      :error ->
        structural_congruence(ast)
    end
  end

  # Recomputed per call: seeding is cheap map-building, a module attribute would
  # add a Builtins compile-order coupling, and persistent_term is banned.
  defp seeded_env, do: Builtins.seed(Env.empty())

  defp fold_bool_binop(:and, {:literal, m, a}, {:literal, _, b}, _ast)
       when is_boolean(a) and is_boolean(b),
       do: {:literal, m, a and b}

  defp fold_bool_binop(:or, {:literal, m, a}, {:literal, _, b}, _ast)
       when is_boolean(a) and is_boolean(b),
       do: {:literal, m, a or b}

  defp fold_bool_binop(_op, l, r, {tag, meta, _}), do: {tag, meta, [l, r]}

  defp fold_bool_not({:literal, m, a}, _ast) when is_boolean(a), do: {:literal, m, not a}
  defp fold_bool_not(operand, {tag, meta, _}), do: {tag, meta, [operand]}

  defp structural_congruence({tag, meta, children}) when is_list(children),
    do: {tag, meta, Enum.map(children, &kernel_normalize/1)}

  defp structural_congruence(other), do: other

  @doc """
  True when two type-level expressions reduce to the same normal form.

  This is the definitional-equality predicate the type checker uses
  before falling back to SMT.
  """
  @spec equal?(ast(), ast(), bindings()) :: boolean()
  def equal?(a, b, bindings \\ %{}) do
    normalize(a, bindings) == normalize(b, bindings)
  end

  @doc """
  Substitute every occurrence of free variables matching `bindings`.

  Unlike `normalize/2`, no arithmetic reduction is performed.
  """
  @spec substitute(ast(), bindings()) :: ast()
  def substitute(ast, bindings) do
    do_substitute(ast, bindings)
  end

  # -- Substitution (no folding) -----------------------------------------------

  defp do_substitute({:variable, _meta, name} = ast, bindings) when is_binary(name) do
    Map.get(bindings, name, ast)
  end

  defp do_substitute({tag, meta, children}, bindings) when is_list(children) do
    {tag, meta, Enum.map(children, &do_substitute(&1, bindings))}
  end

  defp do_substitute(other, _bindings), do: other

end
