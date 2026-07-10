defmodule Cure.Core.Builtins do
  @moduledoc """
  Canonical builtin-inductive schemas and the programmatic seeder.

  Schema validation checks constructor NAMES and arities, not arity alone:
  the literal wiring (true/false -> True/False) and erasure atom mapping
  (False/True -> false/true; Z/S -> int) key off these exact names, so a
  shape-conformant but name-mismatched binding (e.g. `Coin = Heads | Tails`
  tagged `@builtin(:bool)`) is a real miscompile risk and must be rejected.
  """
  alias Cure.Core.{Env, Inductive}

  # key => list of {ctor_name, arity}. Names are load-bearing.
  @schemas %{
    bool: [{:False, 0}, {:True, 0}],
    nat: [{:Z, 0}, {:S, 1}],
    eq: [{:reflexive, 1}],
    sigma: [{:mk_pair, 2}],
    list: [{:Nil, 0}, {:Cons, 2}],
    # First/Next each carry an erased implicit index binder `{m : Nat}` (like
    # Equivalent's erased witness `w`), so their STORED arities are 1 and 2 —
    # First: {m}; Next: {m}, Bounded(m). The erased `m` drops at emit, leaving
    # the runtime shape First->0 / Next(pred)->pred+1 (Nat's Z/S erasure).
    bounded: [{:First, 1}, {:Next, 2}]
  }

  # Builtin arithmetic/comparison op globals (K2 wave, spec 2026-07-09). Each is
  # a BODY-LESS def carrying a `builtin_op` marker; the certified-δ engine folds
  # a saturated literal spine via the audited `Eval.fold` table (Lean reduce_nat
  # / Idris Builtin-op analog). Monomorphic per-type (Lean-aligned): the
  # elaborator type-directs `+`/`==`/… to the int_* or float_* twin. `{name,
  # op_key}`. Comparisons (@cmp_ops) have a Bool codomain; arithmetic/neg return
  # the operand type. int_rem is Int-only (no float_rem — matches infer_prim).
  @cmp_ops [:lt, :le, :gt, :ge, :eq, :ne]

  @int_binops [
    {:int_add, :add},
    {:int_sub, :sub},
    {:int_mul, :mul},
    {:int_div, :div},
    {:int_rem, :rem},
    {:int_lt, :lt},
    {:int_le, :le},
    {:int_gt, :gt},
    {:int_ge, :ge},
    {:int_eq, :eq},
    {:int_ne, :ne},
    # Int-only bitwise (no float twin). Codomain is Int (not in @cmp_ops).
    {:int_band, :band},
    {:int_bor, :bor},
    {:int_bxor, :bxor},
    {:int_bsl, :bsl},
    {:int_bsr, :bsr}
  ]

  # NOTE `float_div` carries its OWN op key `:fdiv`, not `:div`. The op key is what
  # `Eval.fold/2` and `Emit.erl_binop/1` dispatch on, and Erlang's `div` is INTEGER
  # division (`7.0 div 2.0` raises badarith) while `/` is float division. `add`/`sub`/
  # `mul` and the comparisons can safely share a key with their int twins because the
  # corresponding BEAM operators (`+ - * < =< > >= == /=`) are int/float polymorphic;
  # division is the sole operator where they are NOT the same instruction.
  @float_binops [
    {:float_add, :add},
    {:float_sub, :sub},
    {:float_mul, :mul},
    {:float_div, :fdiv},
    {:float_lt, :lt},
    {:float_le, :le},
    {:float_gt, :gt},
    {:float_ge, :ge},
    {:float_eq, :eq},
    {:float_ne, :ne}
  ]

  @int_unops [{:int_neg, :neg}, {:int_bnot, :bnot}]
  @float_unops [{:float_neg, :neg}]

  # Amendment A1 (spec §1-A): polymorphic STRUCTURAL equality —
  # struct_eq/struct_ne : Pi(a: Type0). a -> a -> Bool (explicit ω-present type
  # argument; emit drops it). Transitional representation of the retiring
  # {:prim, :eq/:ne} on non-int/float/bool operands: the hook folds only two
  # literal VALUE args (late-instantiated polymorphic operands), stays NEUTRAL
  # on ADTs (R8c). Distinct marker atoms so hook/emit/lint never conflate them
  # with the monomorphic :eq/:ne. Op set is therefore 25, not 23.
  @struct_ops [{:struct_eq, :struct_eq}, {:struct_ne, :struct_ne}]

  @doc "The expected schema descriptor for a builtin key. Raises for an unknown key."
  @spec schema(atom()) :: [{atom(), non_neg_integer()}]
  def schema(key), do: Map.fetch!(@schemas, key)

  @doc """
  Validate that `family_id` in `env` conforms to `key`'s canonical schema —
  by constructor NAME and arity (not arity alone). `:ok` or raises `ArgumentError`.
  """
  @spec validate!(Env.t(), atom(), atom()) :: :ok
  def validate!(%Env{} = env, key, family_id) do
    expected = Enum.sort(schema(key))
    ctors = Inductive.ctors_of(env, family_id) || []

    actual =
      ctors
      |> Enum.map(fn c -> {c.name, length(Map.get(c, :args, []))} end)
      |> Enum.sort()

    if actual == expected do
      :ok
    else
      raise ArgumentError,
            "@builtin(#{inspect(key)}) on #{inspect(family_id)}: expected constructors " <>
              "#{inspect(expected)} (name and arity), got #{inspect(actual)}"
    end
  end

  @doc """
  Seed an env with the canonical `Bool` (`False | True`) and `Nat` (`Z | S(Nat)`)
  families, each validated against its schema and registered under its builtin
  key. This is the base env for kernel unit tests and the conformance harness
  (the prelude compile obtains the same families via its `@builtin` declarations;
  Task 4 pins the two representations equal).
  """
  @spec seed(Env.t(), MapSet.t()) :: Env.t()
  def seed(%Env{} = env, exclude \\ MapSet.new()) do
    env
    |> maybe_seed(:bool, bool_family(), bool_ctors(), exclude)
    |> maybe_seed(:nat, nat_family(), nat_ctors(), exclude)
    |> maybe_seed(:eq, eq_family(), eq_ctors(), exclude)
    |> maybe_seed(:sigma, sigma_family(), sigma_ctors(), exclude)
    |> maybe_seed(:list, list_family(), list_ctors(), exclude)
    |> seed_ops()
  end

  @doc """
  Seed the 31 builtin-op globals (16 int binary [11 arith/cmp + 5 bitwise] +
  10 float binary + int_neg/int_bnot/float_neg + the A1 polymorphic
  struct_eq/struct_ne) as body-less defs carrying a `builtin_op` marker. Public
  so the Antigen generator envs (SigMenu v1, Generators.Totality) can reuse it.
  Run AFTER the inductive seeds so the Bool codomain resolves through the
  registry.
  """
  @spec seed_ops(Env.t()) :: Env.t()
  def seed_ops(%Env{} = env) do
    bool_ty = {:data, bool_family_id(env), [], []}

    env
    |> seed_binops(@int_binops, {:int_type}, bool_ty)
    |> seed_binops(@float_binops, {:float_type}, bool_ty)
    |> seed_unops(@int_unops, {:int_type})
    |> seed_unops(@float_unops, {:float_type})
    |> seed_struct_ops(bool_ty)
  end

  # The family id to bake into every comparison / structural-equality codomain.
  #
  # `seed_ops/1` snapshots this as a plain Core term, not a live registry lookup, so it has to
  # be right at the moment it runs — and `seed/2` runs it unconditionally, as its last step.
  # Reading it only out of `Inductive.builtin(env, :bool)` got `nil` in exactly the scenario
  # `seed_ops`'s own doc describes: a module that declares its own `Bool` has `:Bool` in
  # `seed/2`'s `exclude` set, so `maybe_seed(:bool, …)` never registered anything, and the
  # module's `@builtin(:bool)` declaration only registers the real family LATER, in
  # `elaborate_declarations`. All 12 comparison ops and both struct ops were left with
  # `{:data, nil, [], []}` as their codomain — a type `Kernel.infer/2` rejects with
  # `{:error, {:unknown_family, nil}}`, which propagates to `check_def/2`'s builtin-op clause
  # whose own comment promises those ops are "Total by fiat".
  #
  # `maybe_seed/5` excludes precisely on `family.name`, so the family the module goes on to
  # declare carries the same name the seed would have used. The canonical name is therefore the
  # correct snapshot under both orders, and the op signatures no longer vary with seeding order.
  defp bool_family_id(env), do: Inductive.builtin(env, :bool) || bool_family().name

  # struct_eq/struct_ne : Pi(a: Type0). Pi(_: a). Pi(_: a). Bool — under the
  # second binder the type param a is {:var, 0}; under the third it is {:var, 1}.
  # The type argument is computationally irrelevant (BEAM `==` is polymorphic and
  # emit drops it), so it is ERASED: a caller may pass its own erased type
  # parameter there without a relevance violation (#26). Erasure drops the type
  # argument, so the emitted spine is the two value operands.
  defp seed_struct_ops(env, bool_ty) do
    ty = {:pi, {:type, 0}, {:pi, {:var, 0}, {:pi, {:var, 1}, bool_ty}}}

    Enum.reduce(@struct_ops, env, fn {name, op_key}, acc ->
      acc
      |> Env.add_def(name, ty, nil, [:erased, :present, :present])
      |> Env.register_builtin_op(name, op_key)
    end)
  end

  defp seed_binops(env, ops, dom, bool_ty) do
    Enum.reduce(ops, env, fn {name, op_key}, acc ->
      cod = if op_key in @cmp_ops, do: bool_ty, else: dom
      ty = {:pi, dom, {:pi, dom, cod}}

      acc
      |> Env.add_def(name, ty, nil)
      |> Env.register_builtin_op(name, op_key)
    end)
  end

  defp seed_unops(env, ops, dom) do
    Enum.reduce(ops, env, fn {name, op_key}, acc ->
      ty = {:pi, dom, dom}

      acc
      |> Env.add_def(name, ty, nil)
      |> Env.register_builtin_op(name, op_key)
    end)
  end

  # A builtin whose bare family name is locally declared by the compiled module
  # is NOT seeded: the module's own declaration is the canonical family, and
  # pre-seeding a same-named family would leave the seed's constructors in
  # `ctor_to_family` (so a `match` on the local family reads as non-exhaustive).
  defp maybe_seed(env, key, family, ctors, exclude) do
    if MapSet.member?(exclude, family.name) do
      env
    else
      declare_and_register(env, key, family, ctors)
    end
  end

  defp declare_and_register(env, key, family, ctors) do
    fid = family.name
    env = Inductive.declare(env, family, ctors)
    :ok = validate!(env, key, fid)
    Inductive.register_builtin(env, key, fid)
  end

  # Bool : Type0 = False | True  (both nullary)
  defp bool_family, do: Inductive.family(:Bool, [], [], 0)

  defp bool_ctors,
    do: [
      Inductive.ctor(:False, [], []),
      Inductive.ctor(:True, [], [])
    ]

  # Nat : Type0 = Z | S(Nat)  (S's field references the Nat family)
  defp nat_family, do: Inductive.family(:Nat, [], [], 0)

  defp nat_ctors,
    do: [
      Inductive.ctor(:Z, [], []),
      Inductive.ctor(:S, [{:n, {:data, :Nat, [], []}}], [])
    ]

  # Equivalent : (a : Type) -> a -> a -> Type   (1 param `a`, 2 indices `x y : a`)
  #   reflexive : {w : a} -> Equivalent(a, w, w)  (single ctor, witness `w` erased)
  #
  # The genuine inductive identity type (spec 2026-07-04), retiring the primitive
  # `{:eq}`/`{:refl}`/`{:rewrite}` Core forms. The user-facing source of truth is
  # the `@builtin(:eq)` declaration in `Std.Equivalent` (lib/std/equivalent.cure);
  # this programmatic seed is its byte-for-byte mirror and the two are pinned equal
  # by the conformance harness. `w` is erased (quantity 0) so it is forced by index
  # unification when matching `reflexive` and dropped at runtime, while the surface
  # still supplies it explicitly at construction (`reflexive(x)`). K/UIP is
  # inherited from the existing index unifier — operator-signed-off 2026-07-04.
  defp eq_family,
    do: Inductive.family(:Equivalent, [a: {:type, 0}], [x: {:var, 0}, y: {:var, 1}], 0)

  defp eq_ctors,
    do: [
      Inductive.ctor(:reflexive, [w: {:var, 0}], [{:var, 0}, {:var, 0}], [:erased], [{:var, 1}])
    ]

  # Sigma : (a : Type) -> (b : (a) -> Type) -> Type   (2 params, no indices)
  #   mk_pair : (x : a) -> b(x) -> Sigma(a, b)
  # The library dependent pair (spec 2026-07-09-sigma-retirement), replacing the
  # primitive {:sigma}/{:pair}/{:fst}/{:snd} Core forms. Level-0 like Equivalent.
  # Source of truth is the @builtin(:sigma) decl in Std.Sigma; this seed is its
  # byte-for-byte mirror, pinned by the conformance drift test.
  defp sigma_family,
    do: Inductive.family(:Sigma, [a: {:type, 0}, b: {:pi, {:var, 0}, {:type, 0}}], [], 0)

  defp sigma_ctors,
    do: [
      Inductive.ctor(
        :mk_pair,
        # Second field `b(x)` is anonymous in the surface ctor sig, so the
        # elaborator auto-names it `_a1` (positional; the drift test pins this).
        [x: {:var, 1}, _a1: {:app, {:var, 1}, {:var, 0}}],
        [],
        [:present, :present],
        [{:var, 3}, {:var, 2}]
      )
    ]

  # List : (a : Type) -> Type   (1 param, no indices)
  #   Nil  : List(a)
  #   Cons : (x : a) -> (xs : List(a)) -> List(a)
  # First parametrized + self-referential builtin family (Cons's second field
  # references List itself, like nat's S). Source of truth is the @builtin(:list)
  # decl in Std.List; this seed is its byte-for-byte mirror, pinned by
  # builtin_list_drift_test.exs.
  defp list_family, do: Inductive.family(:List, [a: {:type, 0}], [], 0)

  # Field names auto-generated positionally by the elaborator (`_a0`/`_a1`); the
  # result-param term is the family's own param `a` reindexed under the ctor's
  # field binders (Nil: {:var, 0}; Cons: {:var, 2} beneath its two fields). The
  # drift test pins both spellings against the source declaration.
  defp list_ctors,
    do: [
      Inductive.ctor(:Nil, [], [], [], [{:var, 0}]),
      Inductive.ctor(
        :Cons,
        [_a0: {:var, 0}, _a1: {:data, :List, [{:var, 1}], []}],
        [],
        [:present, :present],
        [{:var, 2}]
      )
    ]
end
