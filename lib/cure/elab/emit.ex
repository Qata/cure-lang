defmodule Cure.Elab.Emit do
  @moduledoc """
  BEAM emission for the erased Core (design spec §8, M9.3).

  The final leg of the pipeline: an elaborated, totality-certified definition is
  erased (its `:erased` index arguments dropped, M9.1) and lowered to Erlang
  abstract forms, which `:compile.forms/2` turns into real bytecode.

  The supported runtime fragment is the non-dependent residue of a checked
  program — exactly what survives erasure:

    * a nullary constructor becomes its atom (`Causal` → `:Causal`, `prim` → `:prim`);
    * an n-ary constructor becomes a tagged tuple of its *present* fields
      (`seq(l, r)` → `{:seq, L, R}`);
    * a dependent `case` becomes an Erlang `case` whose patterns bind only the
      present fields; erased fields carry no runtime slot;
    * a Sigma pair becomes a 2-tuple, `fst`/`snd` become `element/2`.

  A definition whose erased body still contains a hole is refused (§6 negative #5):
  it typechecks but must not be emitted.
  """

  alias Cure.Compiler.BeamWriter
  alias Cure.Core.{Env, Inductive, Validator}
  alias Cure.Elab.Erase

  @line 1

  @doc """
  Emit `functions` from `env` as a module named `module`, compile, and load it.

  Returns `{:ok, module}` on success, `{:error, {:unfilled_hole, name}}` when a
  requested function still contains a hole, or `{:error, reason}` if the Erlang
  compiler rejects the forms.
  """
  @spec compile_and_load(Env.t(), keyword()) :: {:ok, module()} | {:error, term()}
  def compile_and_load(%Env{} = env, opts) do
    module = Keyword.fetch!(opts, :module)
    names = Keyword.fetch!(opts, :functions)

    with :ok <- reject_holes(env, names) do
      BeamWriter.compile_and_load(module_forms(env, module, names))
    end
  end

  @doc """
  Erlang abstract forms for *every* definition in `env`, as module `module`.

  This is the codegen entry the real compiler pipeline calls for a dependent
  module. Refuses the whole module if any definition still contains a hole
  (§6 negative #5) and reports a definition the runtime fragment cannot express
  rather than crashing the pipeline.
  """
  @spec compile_forms(Env.t(), module()) :: {:ok, [tuple()]} | {:error, term()}
  def compile_forms(%Env{defs: defs} = env, module) do
    # Builtin-op defs are body-less (K2): nothing to emit — saturated uses
    # inline to BEAM operators and first-class uses become local wrappers.
    # (`function_form` would crash on the nil body.) The live pipeline calls
    # /3 with local_defs, so this all-defs entry filters defensively.
    names = for {name, d} <- defs, is_nil(Map.get(d, :builtin_op)), do: name

    compile_forms(env, module, names)
  end

  @doc """
  Erlang abstract forms for a selected set of definitions in `env`.

  Imported definitions may be present in the Core env so conversion can unfold
  them, but an importing module should emit only its own local definitions.
  """
  @spec compile_forms(Env.t(), module(), [atom()]) :: {:ok, [tuple()]} | {:error, term()}
  def compile_forms(%Env{} = env, module, names) do
    with :ok <- reject_holes(env, names) do
      try do
        {:ok, module_forms(env, module, names)}
      rescue
        e in ArgumentError -> {:error, {:cannot_emit, Exception.message(e)}}
      end
    end
  end

  @doc "The Erlang abstract forms for `functions` in `env`, as module `module`."
  @spec module_forms(Env.t(), module(), [atom()]) :: [tuple()]
  def module_forms(%Env{} = env, module, names) do
    fn_forms = Enum.map(names, &function_form(env, &1))
    exports = Enum.map(fn_forms, fn {:function, _l, name, arity, _cls} -> {name, arity} end)

    [
      {:attribute, @line, :module, module},
      {:attribute, @line, :export, exports}
      | fn_forms
    ]
  end

  # -- functions --------------------------------------------------------------

  # The single trusted enforcement point for "no unfilled obligation ships" (K3).
  # Validates the *pre-erase* Core body against the strict release config: the
  # validator descends into erased subterms (rewrite proof/motive, eq/refl args)
  # that `Erase.erase` drops, so a hole hidden in an erased position is caught
  # here rather than shipped silently (#102). A `no_hole` rejection maps to the
  # public `{:unfilled_hole, name}` contract; any other release-clause rejection
  # surfaces as a `{:final_core_violation, name, _}` rather than crashing codegen.
  defp reject_holes(env, names) do
    Enum.reduce_while(names, :ok, fn name, :ok ->
      case Validator.validate(def_body(env, name), Validator.release_config()) do
        {:ok, _warnings} ->
          {:cont, :ok}

        {:error, rejections} ->
          if Enum.any?(rejections, &(&1.clause == :no_hole)),
            do: {:halt, {:error, {:unfilled_hole, name}}},
            else: {:halt, {:error, {:final_core_violation, name, rejections}}}
      end
    end)
  end

  defp def_body(env, name) do
    case Env.get_def(env, name) do
      %{body: body} -> body
      nil -> raise ArgumentError, "no such definition: #{inspect(name)}"
    end
  end

  defp function_form(env, name) do
    %{body: body, quantities: quantities} = Env.get_def(env, name)
    qs = quantities || []
    {param_names, inner} = peel_params(Erase.erase(env, body), qs, 0, [])

    ctx = Enum.reverse(param_names)
    body_form = lower(env, inner, ctx)

    params =
      for {n, :present} <- Enum.zip(param_names, qs),
          do: underscore_if_unused({:var, @line, n}, body_form)

    clause = {:clause, @line, params, [], [body_form]}
    {:function, @line, name, length(params), [clause]}
  end

  # Peel one binder per declared parameter, naming present binders `V<pos>` (bound
  # as Erlang params) and erased binders `_e<pos>` (dead after erasure).
  defp peel_params(term, [], _pos, acc), do: {Enum.reverse(acc), term}

  defp peel_params({:lam, _dom, body}, [q | qs], pos, acc) do
    name = if q == :present, do: :"V#{pos}", else: :"_e#{pos}"
    peel_params(body, qs, pos + 1, [name | acc])
  end

  defp peel_params(term, _qs, _pos, acc), do: {Enum.reverse(acc), term}

  # -- expressions ------------------------------------------------------------

  # `ctx` lists the in-scope Erlang variable atoms with de Bruijn index 0 first.
  defp lower(_env, {:var, k}, ctx) do
    case Enum.at(ctx, k) do
      nil -> raise ArgumentError, "de Bruijn index #{k} out of range"
      name -> {:var, @line, name}
    end
  end

  defp lower(env, {:ctor, name, args}, ctx) do
    cond do
      args == [] and bool_ctor?(env, name) ->
        {:atom, @line, bool_atom(name)}

      nat_ctor?(env, name) ->
        case args do
          [] -> {:integer, @line, 0}
          [n] -> {:op, @line, :+, lower(env, n, ctx), {:integer, @line, 1}}
        end

      sigma_ctor?(env, name) ->
        {:tuple, @line, Enum.map(args, &lower(env, &1, ctx))}

      true ->
        case Enum.map(args, &lower(env, &1, ctx)) do
          [] -> {:atom, @line, name}
          forms -> {:tuple, @line, [{:atom, @line, name} | forms]}
        end
    end
  end

  defp lower(env, {:case, scrut, _motive, branches}, ctx) do
    {:case, @line, lower(env, scrut, ctx), Enum.map(branches, &branch_clause(env, &1, ctx))}
  end

  defp lower(_env, {:int_lit, n}, _ctx), do: {:integer, @line, n}
  defp lower(_env, {:float_lit, f}, _ctx), do: {:float, @line, f}

  # A first-class lambda erases to a curried 1-argument BEAM fun; its parameter
  # takes de Bruijn index 0 in the body's frame.
  defp lower(env, {:lam, _dom, body}, ctx) do
    var = :"Fn#{length(ctx)}"
    clause = {:clause, @line, [{:var, @line, var}], [], [lower(env, body, [var | ctx])]}
    {:fun, @line, {:clauses, [clause]}}
  end

  defp lower(env, {:app, _, _} = app, ctx) do
    {head, args} = spine(app, [])

    case builtin_op_form(head, args, env, ctx) do
      {:ok, form} ->
        form

      :no ->
        case connective_inline(head, args, env, ctx) do
          {:ok, form} ->
            form

          :no ->
            lower_app_spine(env, head, args, ctx)
        end
    end
  end

  # Builtin-op global spines (K2 spec 2026-07-09 §1.5 + A1 §1-A), keyed via the
  # def-record registry (`Env.builtin_op/2`) — a user def named int_add carries
  # no marker and takes the ordinary global path. Saturated → the SAME BEAM
  # operator as the retired prim lowering (struct ops DROP the type argument).
  # Partial (0 < n < arity) must NOT reach `lower_app_spine`'s generic global
  # branch (present_arity reads nil quantities as 0 and would emit a call to a
  # nonexistent `int_add()`): route as wrapper + curried applications, same as
  # the closure branch. The function-value ABI is curried 1-arg funs (lambdas
  # lower so; closures apply one arg at a time), so wrappers nest 1-arg funs.
  defp builtin_op_form({:global, g}, args, env, ctx) do
    case Env.builtin_op(env, g) do
      nil -> :no
      op -> {:ok, lower_builtin_op(op, args, env, ctx)}
    end
  end

  defp builtin_op_form(_head, _args, _env, _ctx), do: :no

  defp lower_builtin_op(op, args, env, ctx) when op in [:struct_eq, :struct_ne] do
    case args do
      [_ty, l, r] ->
        erl = if op == :struct_eq, do: :==, else: :"/="
        {:op, @line, erl, lower(env, l, ctx), lower(env, r, ctx)}

      _ ->
        curry_apply(builtin_op_wrapper(op), args, env, ctx)
    end
  end

  defp lower_builtin_op(:neg, args, env, ctx) do
    case args do
      [a] -> {:op, @line, :-, lower(env, a, ctx)}
      _ -> curry_apply(builtin_op_wrapper(:neg), args, env, ctx)
    end
  end

  defp lower_builtin_op(op, args, env, ctx) do
    case args do
      [a, b] -> {:op, @line, erl_binop(op), lower(env, a, ctx), lower(env, b, ctx)}
      _ -> curry_apply(builtin_op_wrapper(op), args, env, ctx)
    end
  end

  defp curry_apply(base, args, env, ctx),
    do: Enum.reduce(args, base, fn arg, acc -> {:call, @line, acc, [lower(env, arg, ctx)]} end)

  # A first-class/partial builtin-op use: a local curried fun computing the op.
  # Param names use a dedicated prefix (ctx vars are V<pos>/Fn<n>/_e<pos>), so
  # no shadowing. The struct wrapper accepts and ignores the type argument.
  defp builtin_op_wrapper(op) when op in [:struct_eq, :struct_ne] do
    erl = if op == :struct_eq, do: :==, else: :"/="
    body = {:op, @line, erl, {:var, @line, :BopL}, {:var, @line, :BopR}}

    fun1(:_BopT, fun1(:BopL, fun1(:BopR, body)))
  end

  defp builtin_op_wrapper(:neg),
    do: fun1(:BopA, {:op, @line, :-, {:var, @line, :BopA}})

  defp builtin_op_wrapper(op) do
    body = {:op, @line, erl_binop(op), {:var, @line, :BopL}, {:var, @line, :BopR}}
    fun1(:BopL, fun1(:BopR, body))
  end

  defp fun1(param, body),
    do: {:fun, @line, {:clauses, [{:clause, @line, [{:var, @line, param}], [], [body]}]}}

  # A SATURATED application of a `Std.Bool` connective def inlines to the native
  # BEAM boolean op — byte-for-byte the retired primitive's codegen (strict
  # `:and`/`:or`/`:not`; `:==`/`:"/="` for Bool equality). An UNSATURATED use
  # (wrong arg count) returns `:no` and falls through to an ordinary call to the
  # def. Recognised by exact def name (the connectives are the canonical Std.Bool
  # prelude functions).
  defp connective_inline({:global, name}, [a, b], env, ctx)
       when name in [:and, :or, :eq, :ne] do
    {:ok, {:op, @line, connective_binop(name), lower(env, a, ctx), lower(env, b, ctx)}}
  end

  defp connective_inline({:global, :not}, [a], env, ctx) do
    {:ok, {:op, @line, :not, lower(env, a, ctx)}}
  end

  # Saturated Sigma projection: `sigma_first(p)`/`sigma_second(p)` — after erasure
  # of the `{a}`/`{b}` implicits leaves a single-argument spine — inline to
  # `element(1|2, P)`, keeping `.1`/`.2` zero-cost and the bare-2-tuple ABI (spec
  # §1.5 / §2.3). The bare global passed as a value (0 args) is untouched.
  defp connective_inline({:global, :sigma_first}, [p], env, ctx),
    do: {:ok, element(1, lower(env, p, ctx))}

  defp connective_inline({:global, :sigma_second}, [p], env, ctx),
    do: {:ok, element(2, lower(env, p, ctx))}

  defp connective_inline(_head, _args, _env, _ctx), do: :no

  defp connective_binop(:and), do: :and
  defp connective_binop(:or), do: :or
  defp connective_binop(:eq), do: :==
  defp connective_binop(:ne), do: :"/="

  defp lower_app_spine(env, head, args, ctx) do
    case head do
      # A named function takes its declared arity in one BEAM call; any further
      # arguments apply (curried) to the function it returns — `mk()(z)`.
      {:global, name} ->
        {direct, extra} = Enum.split(args, present_arity(env, name))
        base = {:call, @line, {:atom, @line, name}, Enum.map(direct, &lower(env, &1, ctx))}
        Enum.reduce(extra, base, fn arg, acc -> {:call, @line, acc, [lower(env, arg, ctx)]} end)

      # Applying a closure value (a lambda or a function-typed binder) is curried:
      # apply one argument at a time to the BEAM fun.
      _ ->
        Enum.reduce(args, lower(env, head, ctx), fn arg, acc ->
          {:call, @line, acc, [lower(env, arg, ctx)]}
        end)
    end
  end

  # A bare global: a nullary definition is called (`name()`); a definition with
  # present parameters used as a *value* (passed to a higher-order function)
  # becomes a function reference `fun name/arity`. A BUILTIN-OP global has no
  # compiled top-level function to reference (body-less; present_arity would
  # read its nil quantities as 0 and emit a bogus `name()` call) — it becomes a
  # local curried fun wrapper computing the op (K2 §1.5b).
  defp lower(env, {:global, name}, _ctx) do
    case Env.builtin_op(env, name) do
      nil ->
        case present_arity(env, name) do
          0 -> {:call, @line, {:atom, @line, name}, []}
          n -> {:fun, @line, {:function, name, n}}
        end

      op ->
        builtin_op_wrapper(op)
    end
  end

  defp present_arity(env, name) do
    case Env.get_def(env, name) do
      %{quantities: qs} when is_list(qs) -> Enum.count(qs, &(&1 == :present))
      _ -> 0
    end
  end

  # {:absurd} is deleted from produced Core (K4 §H: the elaborator omits impossible
  # branches; the validator release-rejects it; Term.term? excludes it). Retained
  # only as a defensive stub — a hand-crafted {:absurd} reaching emit lowers to a
  # crash rather than the raising catch-all. Not produced in practice.
  defp lower(_env, {:absurd}, _ctx),
    do: {:call, @line, {:atom, @line, :error}, [{:atom, @line, :absurd}]}

  defp lower(_env, term, _ctx), do: raise(ArgumentError, "cannot emit #{inspect(term)}")

  defp erl_binop(:add), do: :+
  defp erl_binop(:sub), do: :-
  defp erl_binop(:mul), do: :*
  defp erl_binop(:div), do: :div
  defp erl_binop(:rem), do: :rem
  defp erl_binop(:eq), do: :==
  defp erl_binop(:ne), do: :"/="
  defp erl_binop(:lt), do: :<
  defp erl_binop(:le), do: :"=<"
  defp erl_binop(:gt), do: :>
  defp erl_binop(:ge), do: :">="
  defp erl_binop(:and), do: :and
  defp erl_binop(:or), do: :or

  defp element(n, tuple_form) do
    {:call, @line, {:atom, @line, :element}, [{:integer, @line, n}, tuple_form]}
  end

  defp spine({:app, f, x}, acc), do: spine(f, [x | acc])
  defp spine(head, acc), do: {head, acc}

  # A dependent-`case` branch. The scrutinee at runtime is the *erased* value, so
  # the pattern binds only present fields; the body's de Bruijn frame still counts
  # every field (index 0 = last field), so erased fields keep a (dead) context slot.
  defp branch_clause(env, {cname, arity, body}, ctx) do
    cond do
      nat_ctor?(env, cname) -> nat_branch_clause(env, {cname, arity, body}, ctx)
      sigma_ctor?(env, cname) -> sigma_branch_clause(env, {cname, arity, body}, ctx)
      true -> generic_branch_clause(env, {cname, arity, body}, ctx)
    end
  end

  # case-on-Sigma (spec §2.3): `mk_pair(x, y)` matches a bare 2-tuple `{X, Y}` (both
  # fields present), binding both into the de Bruijn frame exactly as the generic
  # tagged form would — but without the leading ctor-name atom, so the value stays
  # the untagged 2-tuple the ABI requires.
  defp sigma_branch_clause(env, {_mk_pair, 2, body}, ctx) do
    base = length(ctx)
    vx = :"V#{base}"
    vy = :"V#{base + 1}"
    body_form = lower(env, body, [vy, vx | ctx])
    px = underscore_if_unused({:var, @line, vx}, body_form)
    py = underscore_if_unused({:var, @line, vy}, body_form)
    {:clause, @line, [{:tuple, @line, [px, py]}], [], [body_form]}
  end

  # case-on-Nat (spec §2.2): the zero ctor's branch matches literal 0; the succ
  # ctor's branch matches a fresh N with guard `N > 0` (belt-and-braces: a rep
  # bug crashes loudly instead of binding k = -1) and binds the predecessor as
  # the body's first statement — Erlang patterns/guards cannot compute-and-bind,
  # so `K = N - 1` must open the body, making it a two-form list. The body's
  # de Bruijn frame still counts the field (index 0 = predecessor), exactly as
  # the tuple form would have bound it.
  defp nat_branch_clause(env, {_zero, 0, body}, ctx) do
    {:clause, @line, [{:integer, @line, 0}], [], [lower(env, body, ctx)]}
  end

  defp nat_branch_clause(env, {_succ, 1, body}, ctx) do
    base = length(ctx)
    k = :"V#{base}"
    n = :"N#{base}"
    body_form = lower(env, body, [k | ctx])
    k_var = underscore_if_unused({:var, @line, k}, body_form)
    bind = {:match, @line, k_var, {:op, @line, :-, {:var, @line, n}, {:integer, @line, 1}}}
    guard = [[{:op, @line, :>, {:var, @line, n}, {:integer, @line, 0}}]]
    {:clause, @line, [{:var, @line, n}], guard, [bind, body_form]}
  end

  defp generic_branch_clause(env, {cname, arity, body}, ctx) do
    quantities = Inductive.ctor_quantities(env, cname) || List.duplicate(:present, arity)
    base = length(ctx)

    fields =
      for i <- indices(arity) do
        q = Enum.at(quantities, i, :present)
        if q == :present, do: {:present, :"V#{base + i}"}, else: {:erased, :"_f#{base + i}"}
      end

    field_names = Enum.map(fields, fn {_q, n} -> n end)
    new_ctx = Enum.reverse(field_names) ++ ctx
    body_form = lower(env, body, new_ctx)

    present =
      for {:present, n} <- fields,
          do: underscore_if_unused({:var, @line, n}, body_form)

    pattern =
      case present do
        [] -> {:atom, @line, bool_atom_or_self(env, cname)}
        _ -> {:tuple, @line, [{:atom, @line, cname} | present]}
      end

    {:clause, @line, [pattern], [], [body_form]}
  end

  # `erl_lint` flags a bound-but-unused variable (`unused_var`). An erased proof
  # discards its parameters — an equality proof erases to the runtime-irrelevant
  # `:refl`, so a *present* function parameter or matched ctor field can go
  # unreferenced. Rename such a binder to a `_`-prefixed name: still a real,
  # referenceable variable, but exempt from the warning. Binder names are
  # depth-unique (`V<ctx-depth>`), so a plain occurrence check over the lowered
  # body is a sound "is it used?" test (no shadowing to confuse it).
  defp underscore_if_unused({:var, l, name} = v, body_form) do
    if used_var?(name, body_form), do: v, else: {:var, l, :"_#{name}"}
  end

  defp used_var?(name, {:var, _, name}), do: true

  defp used_var?(name, form) when is_tuple(form),
    do: Enum.any?(Tuple.to_list(form), &used_var?(name, &1))

  defp used_var?(name, form) when is_list(form),
    do: Enum.any?(form, &used_var?(name, &1))

  defp used_var?(_name, _other), do: false

  defp indices(0), do: []
  defp indices(arity), do: Enum.to_list(0..(arity - 1))

  # The canonical Bool inductive erases to native BEAM booleans: its nullary
  # constructors `True`/`False` lower to the atoms `true`/`false` (matching what
  # `{:prim}` comparisons already return at runtime), and a `:case` on Bool tests
  # those same lowercase atoms.
  defp bool_ctor?(env, name), do: Inductive.builtin(env, :bool) == Inductive.ctor_family(env, name)

  # The canonical Std.Nat family (registry-keyed, nominal): its values are BEAM
  # machine integers (spec 2026-07-08-nat-int-erasure). A locally-redeclared
  # structural twin has a different family-id and keeps tuples.
  defp nat_ctor?(env, name) do
    fam = Inductive.builtin(env, :nat)
    fam != nil and Inductive.ctor_family(env, name) == fam
  end

  # The canonical Sigma family (registry-keyed, nominal): its values are the bare
  # BEAM 2-tuples the primitive pair always compiled to (spec 2026-07-09 D2 §1.5) —
  # Std.Pair's element/2 interop and AtomVM depend on the untagged shape.
  defp sigma_ctor?(env, name) do
    fam = Inductive.builtin(env, :sigma)
    fam != nil and Inductive.ctor_family(env, name) == fam
  end

  defp bool_atom(:True), do: true
  defp bool_atom(:False), do: false

  defp bool_atom_or_self(env, name) do
    if bool_ctor?(env, name), do: bool_atom(name), else: name
  end
end
