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
  alias Cure.Core.{Grade, Env, Inductive, Validator}
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
    origins = Keyword.get(opts, :origins, %{})

    with :ok <- reject_holes(env, names) do
      BeamWriter.compile_and_load(module_forms(env, module, names, origins))
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
  def compile_forms(%Env{} = env, module, names), do: compile_forms(env, module, names, %{})

  @doc """
  As `compile_forms/3`, but with an `origins` map (`%{fun_atom => Cure.<Module>}`,
  from `Cure.Elab.Program.import_origins/1`) routing `use`-imported cross-module
  `{:global, name}` references to REMOTE calls instead of undefined local ones.
  An empty map (the /3 default) preserves the all-local behaviour of a
  self-contained module.
  """
  @spec compile_forms(Env.t(), module(), [atom()], map()) :: {:ok, [tuple()]} | {:error, term()}
  def compile_forms(%Env{} = env, module, names, origins) do
    # Type-level definitions — those whose type ends in a universe (`… -> Type`) —
    # are type synonyms / type-level computations (a large-elim kind selector, a
    # `Lens(s, a) = Optic(LensKind, s, a)` alias). They are computationally
    # irrelevant: their body is a type value (`{:data, LensOptic, …}`) with no BEAM
    # representation, so lowering one crashes emission. Erase them wholesale — no
    # BEAM function, no export — exactly as Idris/Agda/Lean drop type-level
    # definitions. Ordinary value functions that merely MENTION those types in
    # their signatures are unaffected (their codomain is a data type, not `Type`).
    # Hole-check the FULL name set first — an unfilled obligation in a type-level
    # def is still refused (#102 firewall) — then drop the type-level defs from the
    # set that actually reaches emission.
    with :ok <- reject_holes(env, names) do
      emit_names = Enum.reject(names, &type_level_def?(env, &1))

      try do
        {:ok, module_forms(env, module, emit_names, origins)}
      rescue
        e in ArgumentError -> {:error, {:cannot_emit, Exception.message(e)}}
      end
    end
  end

  # A definition is TYPE-LEVEL when its type's ultimate codomain (after peeling the
  # parameter Π telescope) is a universe `{:type, _}` — i.e. it RETURNS a type. A
  # value function returns a value, so its codomain is a data type / Π / primitive,
  # never a universe.
  defp type_level_def?(env, name) do
    case Env.get_def(env, name) do
      %{type: type} -> universe_codomain?(type)
      _ -> false
    end
  end

  defp universe_codomain?({:pi, _g, _dom, cod}), do: universe_codomain?(cod)
  defp universe_codomain?({:type, _}), do: true
  defp universe_codomain?(_), do: false

  @doc "The Erlang abstract forms for `functions` in `env`, as module `module`."
  @spec module_forms(Env.t(), module(), [atom()]) :: [tuple()]
  def module_forms(%Env{} = env, module, names), do: module_forms(env, module, names, %{})

  @doc "As `module_forms/3`, with an import-`origins` map (see `compile_forms/4`)."
  @spec module_forms(Env.t(), module(), [atom()], map()) :: [tuple()]
  def module_forms(%Env{} = env, module, names, origins) do
    # Stash the import origins for the two `{:global, name}` lowering sites; the
    # de Bruijn `ctx` list threaded through `lower/3` has no room for a
    # module-level constant, and the Core `Env` is TCB. Reset on every call
    # (the /3 default passes `%{}`) so a self-contained module never inherits a
    # previous module's origins.
    Process.put(:cure_emit_origins, origins)

    try do
      fn_forms = Enum.map(names, &function_form(env, &1))
      exports = Enum.map(fn_forms, fn {:function, _l, name, arity, _cls} -> {name, arity} end)

      [
        {:attribute, @line, :module, module},
        {:attribute, @line, :export, exports}
        | no_auto_import_attr(exports) ++ fn_forms
      ]
    after
      Process.delete(:cure_emit_origins)
    end
  end

  # A module that defines a function whose `{name, arity}` matches an Erlang
  # auto-imported BIF (e.g. `size/1`, `byte_size/1`, `length/1` — common `@extern`
  # wrapper or stdlib helper names) shadows that BIF. An unqualified call to it
  # then trips `erl_lint`'s `call_to_redefined_bif` warning. Emit an explicit
  # `-compile({no_auto_import, […]}).` so the local definition unambiguously wins
  # and the warning is silenced — exactly how a hand-written Erlang module handles
  # a BIF-named export. Safe here because every such wrapper's body is a *qualified*
  # remote call (`:erlang.byte_size/1`, `:maps.size/1`), never an unqualified
  # self-call, so re-binding the bare name to the local def cannot loop.
  defp no_auto_import_attr(exports) do
    case Enum.filter(exports, fn {name, arity} -> :erl_internal.bif(name, arity) end) do
      [] -> []
      bifs -> [{:attribute, @line, :compile, {:no_auto_import, bifs}}]
    end
  end

  # The import-origins map for the module currently being emitted (see
  # `module_forms/4`); `%{}` outside an emit or for a self-contained module.
  defp emit_origins, do: Process.get(:cure_emit_origins, %{})

  # Resolve a source `{:global, name}` to a REMOTE `{module, fun}` target or
  # `:local`. A `#`-mangled qualified name (`Std.List#map`, from a qualified
  # call or an `implementation` method body) carries its owner in the name; a
  # bare name is looked up in the import `origins`; everything else stays local
  # (this module's own def, or an auto-imported BEAM BIF).
  defp remote_target(name, origins) do
    s = Atom.to_string(name)

    cond do
      String.contains?(s, "#") ->
        [mod, fun] = String.split(s, "#", parts: 2)
        {String.to_atom("Cure." <> mod), String.to_atom(fun)}

      (mod = Map.get(origins, name)) != nil ->
        {mod, name}

      true ->
        :local
    end
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
    case Env.get_def(env, name) do
      %{body: {:extern, {mod, fun, _arity}}} -> extern_form(name, {mod, fun}, present_arity(env, name))
      def -> real_function_form(name, def, env)
    end
  end

  # Wave-3: emit a direct Erlang remote call, mirroring codegen.ex:691-705 (NOT
  # calling it). Params are synthesized from the arity — a bodyless extern has no
  # {:lam, Cure.Core.Grade.unrestricted(),…} chain to peel, so peel_params/4 would yield zero params for arity>0.
  # `0..(arity-1)//1` yields `[]` at arity 0 → `mod:fun()`, correct.
  #
  # The arity is the def's PRESENT count, as in `real_function_form/3` and at every call site
  # (`present_arity/2`), never the raw literal from `@extern(…)` — an erased parameter never
  # reaches the BEAM. `Declarations.check_extern_arity/2` rejects a literal that disagrees, so
  # the two agree by construction; reading the quantities here keeps that true by construction
  # rather than by convention.
  defp extern_form(fn_atom, {mod, fun}, arity) do
    param_forms = for i <- 0..(arity - 1)//1, do: {:var, @line, :"V#{i}"}
    remote = {:call, @line, {:remote, @line, {:atom, @line, mod}, {:atom, @line, fun}}, param_forms}
    {:function, @line, fn_atom, arity, [{:clause, @line, param_forms, [], [remote]}]}
  end

  defp real_function_form(name, %{body: body, quantities: quantities}, env) do
    qs = quantities || []
    {param_names, inner} = peel_params(Erase.erase(env, body), qs, 0, [])

    ctx = Enum.reverse(param_names)
    body_form = lower(env, inner, ctx)

    params =
      for {n, :unrestricted} <- Enum.zip(param_names, qs),
          do: underscore_if_unused({:var, @line, n}, body_form)

    clause = {:clause, @line, params, [], [body_form]}
    {:function, @line, name, length(params), [clause]}
  end

  # Peel one binder per declared parameter, naming present binders `V<pos>` (bound
  # as Erlang params) and erased binders `_e<pos>` (dead after erasure).
  defp peel_params(term, [], _pos, acc), do: {Enum.reverse(acc), term}

  defp peel_params({:lam, _g, _dom, body}, [q | qs], pos, acc) do
    name = if Grade.present?(q), do: :"V#{pos}", else: :"_e#{pos}"
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

      # Bounded erases exactly like Nat — `First` → 0, `Next(pred)` → pred+1 — so a
      # codepoint is a native integer at runtime (matches `{:bounded_lit, _}`). But
      # Bounded is INDEXED: each ctor app also carries an erased implicit index `m`,
      # so drop the erased args and keep only the present predecessor (if any).
      bounded_ctor?(env, name) ->
        case bounded_present_args(env, name, args) do
          [] -> {:integer, @line, 0}
          [n] -> {:op, @line, :+, lower(env, n, ctx), {:integer, @line, 1}}
        end

      sigma_ctor?(env, name) ->
        # A UNIT-TERMINATED `mk_pair` spine `mk_pair(e1, … mk_pair(en, unit))` is a
        # flat telescope `Tuple(T1,…,Tn)` — lower it to ONE flat BEAM tuple
        # `{e1,…,en}`, dropping the `unit`. Each car is lowered independently, so an
        # inner telescope car flattens on its own (opt-in nesting: `%[1,%[2,3]]` →
        # `{1,{2,3}}`). A NON-unit-terminated pair (a bare `Sigma(x:T,U)`) keeps the
        # structural nested 2-tuple emit. The `unit` marker is thus consumed here and
        # never appears at runtime.
        case telescope_cars(env, {:ctor, name, args}) do
          {:telescope, cars} -> {:tuple, @line, Enum.map(cars, &lower(env, &1, ctx))}
          :not_telescope -> {:tuple, @line, Enum.map(args, &lower(env, &1, ctx))}
        end

      list_ctor?(env, name) ->
        case {name, args} do
          {:Nil, []} -> {nil, @line}
          {:Cons, [h, t]} -> {:cons, @line, lower(env, h, ctx), lower(env, t, ctx)}
        end

      true ->
        case Enum.map(args, &lower(env, &1, ctx)) do
          [] -> {:atom, @line, otp_tag(name)}
          forms -> {:tuple, @line, [{:atom, @line, otp_tag(name)} | forms]}
        end
    end
  end

  defp lower(env, {:case, scrut, _motive, branches}, ctx) do
    scrut_form = lower(env, scrut, ctx)
    clauses = Enum.map(branches, &branch_clause(env, &1, ctx))
    irrefutable_projection(scrut_form, clauses) || {:case, @line, scrut_form, clauses}
  end

  defp lower(_env, {:int_lit, n}, _ctx), do: {:integer, @line, n}
  # A compact Nat literal emits as a raw BEAM integer — identical to the existing
  # Nat-ctor erasure (`Z` → 0, `S(n)` → n+1), so `{:nat_lit, 2}` and `S(S(Z))`
  # compile to the same value `2` and interoperate with nat `case` clauses.
  defp lower(_env, {:nat_lit, n}, _ctx), do: {:integer, @line, n}
  # A compact Bounded literal erases to its raw codepoint integer — identical to
  # the `First` → 0 / `Next(n)` → n+1 constructor erasure, so `{:bounded_lit, 97}`
  # and `Next(...First)` compile to the same value 97.
  defp lower(_env, {:bounded_lit, n}, _ctx), do: {:integer, @line, n}
  defp lower(_env, {:float_lit, f}, _ctx), do: {:float, @line, f}
  # An atom literal is its own BEAM value.
  defp lower(_env, {:atom_lit, a}, _ctx), do: {:atom, @line, a}

  # A first-class lambda erases to a curried 1-argument BEAM fun; its parameter
  # takes de Bruijn index 0 in the body's frame.
  defp lower(env, {:lam, _g, _dom, body}, ctx) do
    var = :"Fn#{length(ctx)}"
    body_form = lower(env, body, [var | ctx])
    clause = {:clause, @line, [{:var, @line, unused_underscore(var, body_form)}], [], [body_form]}
    {:fun, @line, {:clauses, [clause]}}
  end

  # `let x := v in body`  ⟶  `begin Lk = <v>, <body> end`. This is the whole
  # payoff of the `:let` binder: `v` is emitted ONCE and bound to a BEAM variable,
  # where surface substitution emitted it at every use site (and not at all at
  # zero uses). Its parameter takes de Bruijn index 0 in the body's frame.
  defp lower(env, {:let, _g, _ty, val, body}, ctx) do
    var = :"L#{length(ctx)}"
    body_form = lower(env, body, [var | ctx])
    bind = {:match, @line, {:var, @line, unused_underscore(var, body_form)}, lower(env, val, ctx)}
    {:block, @line, [bind, body_form]}
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
          0 ->
            case remote_target(name, emit_origins()) do
              :local -> {:call, @line, {:atom, @line, name}, []}
              {mod, fun} -> {:call, @line, {:remote, @line, {:atom, @line, mod}, {:atom, @line, fun}}, []}
            end

          n ->
            case remote_target(name, emit_origins()) do
              :local ->
                {:fun, @line, {:function, name, n}}

              {mod, fun} ->
                {:fun, @line,
                 {:function, {:atom, @line, mod}, {:atom, @line, fun}, {:integer, @line, n}}}
            end
        end

      op ->
        builtin_op_wrapper(op)
    end
  end

  # {:absurd} is deleted from produced Core (K4 §H: the elaborator omits impossible
  # branches; the validator release-rejects it; Term.term? excludes it). Retained
  # only as a defensive stub — a hand-crafted {:absurd} reaching emit lowers to a
  # crash rather than the raising catch-all. Not produced in practice.
  defp lower(_env, {:absurd}, _ctx),
    do: {:call, @line, {:atom, @line, :error}, [{:atom, @line, :absurd}]}

  defp lower(_env, term, _ctx), do: raise(ArgumentError, "cannot emit #{inspect(term)}")

  # A single-clause `case` whose one clause is a tuple pattern and whose body is
  # exactly a variable bound by that pattern is an irrefutable field projection —
  # e.g. the dictionary-method extraction the typeclass elaborator emits
  # (`case Dict of {Comparable, Compare} -> Compare end`). Lowered as a `case`, the
  # bound variable is "exported" from the case, and when that case sits inside an
  # operator subexpression (`compare(x, y) == LessThan`, from `min`/`max`/`clamp`)
  # `erl_lint` raises `export_var_subexpr`. Emit `erlang:element(Idx, Scrut)`
  # instead: a pure call that binds nothing — same value, no warning, no needless
  # case. Semantics-preserving because the match is irrefutable (single, total
  # clause over a well-typed value).
  defp irrefutable_projection(scrut_form, [
         {:clause, _, [{:tuple, _, elems}], [], [{:var, _, v}]}
       ]) do
    case Enum.find_index(elems, &match?({:var, _, ^v}, &1)) do
      nil ->
        nil

      idx ->
        {:call, @line, {:remote, @line, {:atom, @line, :erlang}, {:atom, @line, :element}},
         [{:integer, @line, idx + 1}, scrut_form]}
    end
  end

  defp irrefutable_projection(_scrut_form, _clauses), do: nil

  # An emit-generated binder (lambda param `Fn<n>` / let binder `L<n>`) that never
  # appears in its lowered body — e.g. a catch-all `match` branch whose join-point
  # ignores the scrutinee — must be spelled `_Fn<n>` so `erl_lint` does not flag it
  # as an unused variable (which the stdlib gate treats as a failure). Renaming is
  # sound precisely because the var is absent from the body: no reference to rewrite.
  defp unused_underscore(var, body_form) do
    if var_in_form?(body_form, var), do: var, else: :"_#{var}"
  end

  defp var_in_form?({:var, _, v}, v), do: true
  defp var_in_form?(t, v) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&var_in_form?(&1, v))
  defp var_in_form?(l, v) when is_list(l), do: Enum.any?(l, &var_in_form?(&1, v))
  defp var_in_form?(_, _), do: false

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
    # The type argument is erased, so a saturated call reaches emit as the two
    # value operands `[l, r]`; the `[_ty, l, r]` form is kept only for a term that
    # bypassed erasure (defensive). Anything else is a partial application.
    erl = if op == :struct_eq, do: :==, else: :"/="

    case args do
      [l, r] -> {:op, @line, erl, lower(env, l, ctx), lower(env, r, ctx)}
      [_ty, l, r] -> {:op, @line, erl, lower(env, l, ctx), lower(env, r, ctx)}
      _ -> curry_apply(builtin_op_wrapper(op), args, env, ctx)
    end
  end

  defp lower_builtin_op(:neg, args, env, ctx) do
    case args do
      [a] -> {:op, @line, :-, lower(env, a, ctx)}
      _ -> curry_apply(builtin_op_wrapper(:neg), args, env, ctx)
    end
  end

  defp lower_builtin_op(:bnot, args, env, ctx) do
    case args do
      [a] -> {:op, @line, :bnot, lower(env, a, ctx)}
      _ -> curry_apply(builtin_op_wrapper(:bnot), args, env, ctx)
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
  # no shadowing. The struct wrapper takes the two value operands — the erased
  # type argument is dropped before emit, so it never reaches the wrapper.
  defp builtin_op_wrapper(op) when op in [:struct_eq, :struct_ne] do
    erl = if op == :struct_eq, do: :==, else: :"/="
    body = {:op, @line, erl, {:var, @line, :BopL}, {:var, @line, :BopR}}

    fun1(:BopL, fun1(:BopR, body))
  end

  defp builtin_op_wrapper(:neg),
    do: fun1(:BopA, {:op, @line, :-, {:var, @line, :BopA}})

  defp builtin_op_wrapper(:bnot),
    do: fun1(:BopA, {:op, @line, :bnot, {:var, @line, :BopA}})

  defp builtin_op_wrapper(op) do
    body = {:op, @line, erl_binop(op), {:var, @line, :BopL}, {:var, @line, :BopR}}
    fun1(:BopL, fun1(:BopR, body))
  end

  defp fun1(param, body),
    do: {:fun, @line, {:clauses, [{:clause, @line, [{:var, @line, param}], [], [body]}]}}

  # A SATURATED application of a `Std.Bool` connective def inlines to the native
  # BEAM boolean op — byte-for-byte the retired primitive's codegen (strict
  # `:and`/`:or`/`:not`; `:==`/`:"/="` for Bool equality) — and a saturated
  # Sigma projection `sigma_first(p)`/`sigma_second(p)` (a single-argument
  # spine after implicit erasure) inlines to `element(1|2, P)`, keeping
  # `.1`/`.2` zero-cost on the bare-2-tuple ABI (spec §1.5 / §2.3). An
  # UNSATURATED use (wrong arg count, or the bare global passed as a value)
  # returns `:no` and falls through to an ordinary call/reference. Recognised
  # via the `inline_hint` marker on the def RECORD (set only by the
  # `Std.Bool`/`Std.Sigma` import path), never by bare global atom — a user
  # def shadowing `eq`/`sigma_first`/… carries no marker and is never inlined
  # (R1 discipline, same as the builtin-op registry).
  defp connective_inline({:global, name}, args, env, ctx) do
    case Env.inline_hint(env, name) do
      nil -> :no
      hint -> inline_hint_form(hint, args, env, ctx)
    end
  end

  defp connective_inline(_head, _args, _env, _ctx), do: :no

  defp inline_hint_form(hint, [a, b], env, ctx) when hint in [:and, :or, :eq, :ne],
    do: {:ok, {:op, @line, connective_binop(hint), lower(env, a, ctx), lower(env, b, ctx)}}

  defp inline_hint_form(:not, [a], env, ctx),
    do: {:ok, {:op, @line, :not, lower(env, a, ctx)}}

  defp inline_hint_form(:sigma_first, [p], env, ctx),
    do: {:ok, element(1, lower(env, p, ctx))}

  defp inline_hint_form(:sigma_second, [p], env, ctx),
    do: {:ok, element(2, lower(env, p, ctx))}

  # Flat-telescope positional projections `tproj_i(p)` inline to `element(i, P)`
  # — the i-th slot of the flat BEAM tuple. The final `[p]` spine (one explicit
  # argument after the erased type/tail implicits) is what reaches here.
  defp inline_hint_form(:tproj2, [p], env, ctx), do: {:ok, element(2, lower(env, p, ctx))}
  defp inline_hint_form(:tproj3, [p], env, ctx), do: {:ok, element(3, lower(env, p, ctx))}
  defp inline_hint_form(:tproj4, [p], env, ctx), do: {:ok, element(4, lower(env, p, ctx))}
  defp inline_hint_form(:tproj5, [p], env, ctx), do: {:ok, element(5, lower(env, p, ctx))}
  defp inline_hint_form(:tproj6, [p], env, ctx), do: {:ok, element(6, lower(env, p, ctx))}
  defp inline_hint_form(:tproj7, [p], env, ctx), do: {:ok, element(7, lower(env, p, ctx))}
  defp inline_hint_form(:tproj8, [p], env, ctx), do: {:ok, element(8, lower(env, p, ctx))}

  defp inline_hint_form(_hint, _args, _env, _ctx), do: :no

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

        callee =
          case remote_target(name, emit_origins()) do
            :local -> {:atom, @line, name}
            {mod, fun} -> {:remote, @line, {:atom, @line, mod}, {:atom, @line, fun}}
          end

        base = {:call, @line, callee, Enum.map(direct, &lower(env, &1, ctx))}
        Enum.reduce(extra, base, fn arg, acc -> {:call, @line, acc, [lower(env, arg, ctx)]} end)

      # Applying a closure value (a lambda or a function-typed binder) is curried:
      # apply one argument at a time to the BEAM fun.
      _ ->
        Enum.reduce(args, lower(env, head, ctx), fn arg, acc ->
          {:call, @line, acc, [lower(env, arg, ctx)]}
        end)
    end
  end

  defp present_arity(env, name) do
    case Env.get_def(env, name) do
      %{quantities: qs} when is_list(qs) -> Enum.count(qs, &Grade.present?/1)
      _ -> 0
    end
  end

  defp erl_binop(:add), do: :+
  defp erl_binop(:sub), do: :-
  defp erl_binop(:mul), do: :*
  # `div` is Erlang INTEGER division; `/` is float division. `Builtins` gives
  # float_div the distinct op key `:fdiv` precisely so this mapping can tell them
  # apart — do not collapse them.
  defp erl_binop(:div), do: :div
  defp erl_binop(:fdiv), do: :/
  defp erl_binop(:rem), do: :rem
  defp erl_binop(:band), do: :band
  defp erl_binop(:bor), do: :bor
  defp erl_binop(:bxor), do: :bxor
  defp erl_binop(:bsl), do: :bsl
  defp erl_binop(:bsr), do: :bsr
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

  # Classify a Core term as a UNIT-TERMINATED Σ-telescope spine, returning its car
  # list `[e1, …, en]` (the flat components, `unit` dropped) — or `:not_telescope`
  # for a bare `Sigma(x:T,U)` pair (whose tail is an ordinary value, not `unit`).
  # This is the emit-time reader of the `unit` marker: it decides flat-vs-nested for
  # BOTH values (here) and telescope patterns (`telescope_pattern_cars/2`).
  defp telescope_cars(_env, {:ctor, :unit, []}), do: {:telescope, []}

  defp telescope_cars(env, {:ctor, name, [car, cdr]}) do
    if sigma_ctor?(env, name) do
      case telescope_cars(env, cdr) do
        {:telescope, rest} -> {:telescope, [car | rest]}
        :not_telescope -> :not_telescope
      end
    else
      :not_telescope
    end
  end

  defp telescope_cars(_env, _other), do: :not_telescope

  defp spine({:app, f, x}, acc), do: spine(f, [x | acc])
  defp spine(head, acc), do: {head, acc}

  # A dependent-`case` branch. The scrutinee at runtime is the *erased* value, so
  # the pattern binds only present fields; the body's de Bruijn frame still counts
  # every field (index 0 = last field), so erased fields keep a (dead) context slot.
  defp branch_clause(env, {cname, arity, body}, ctx) do
    cond do
      nat_ctor?(env, cname) -> nat_branch_clause(env, {cname, arity, body}, ctx)
      bounded_ctor?(env, cname) -> bounded_branch_clause(env, {cname, arity, body}, ctx)
      sigma_ctor?(env, cname) -> sigma_branch_clause(env, {cname, arity, body}, ctx)
      list_ctor?(env, cname) -> list_branch_clause(env, {cname, arity, body}, ctx)
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

  # case-on-List: Nil matches [], Cons(h,t) matches [H|T], binding both fields
  # into the de Bruijn frame exactly as the generic tagged form would (index 0 =
  # last field, so `[tail, head | ctx]`). A nested list pattern is lowered by the
  # elaborator's matrix compiler into a chain of these single-level Cons/Nil
  # branches, so native cons cells select correctly at every level.
  defp list_branch_clause(env, {:Nil, 0, body}, ctx) do
    {:clause, @line, [{nil, @line}], [], [lower(env, body, ctx)]}
  end

  defp list_branch_clause(env, {:Cons, 2, body}, ctx) do
    base = length(ctx)
    vh = :"V#{base}"
    vt = :"V#{base + 1}"
    body_form = lower(env, body, [vt, vh | ctx])
    ph = underscore_if_unused({:var, @line, vh}, body_form)
    pt = underscore_if_unused({:var, @line, vt}, body_form)
    {:clause, @line, [{:cons, @line, ph, pt}], [], [body_form]}
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

  # case-on-Bounded: erases to native integers like Nat (`First`≙`Z`,
  # `Next`≙`S`), but — unlike Nat — Bounded is an INDEXED family: each ctor also
  # binds an erased implicit index `{m : Nat}`, so the Core branch arity is 1
  # (First: {m}) / 2 (Next: {m}, pred), not 0 / 1. The erased binders keep a dead
  # de Bruijn slot but are never matched at runtime; the single PRESENT field
  # (Next's predecessor) is the one that carries data. So: no present field ->
  # `First`, matching literal 0; one present field -> `Next`, matching a fresh N
  # with guard `N > 0` and binding the predecessor `pred = N - 1`.
  defp bounded_branch_clause(env, {name, arity, body}, ctx) do
    quantities = Inductive.ctor_quantities(env, name) || List.duplicate(:unrestricted, arity)
    base = length(ctx)
    field_names = for i <- indices(arity), do: :"V#{base + i}"
    new_ctx = Enum.reverse(field_names) ++ ctx
    body_form = lower(env, body, new_ctx)

    case Enum.find_index(quantities, &Grade.present?/1) do
      nil ->
        # `First`: only the erased index -> matches literal 0.
        {:clause, @line, [{:integer, @line, 0}], [], [body_form]}

      present_idx ->
        # `Next`: the present field is the predecessor = N - 1.
        n = :"N#{base}"
        pred_name = Enum.at(field_names, present_idx)
        pred_var = underscore_if_unused({:var, @line, pred_name}, body_form)
        bind = {:match, @line, pred_var, {:op, @line, :-, {:var, @line, n}, {:integer, @line, 1}}}
        guard = [[{:op, @line, :>, {:var, @line, n}, {:integer, @line, 0}}]]
        {:clause, @line, [{:var, @line, n}], guard, [bind, body_form]}
    end
  end

  defp generic_branch_clause(env, {cname, arity, body}, ctx) do
    quantities = Inductive.ctor_quantities(env, cname) || List.duplicate(:unrestricted, arity)
    base = length(ctx)

    fields =
      for i <- indices(arity) do
        q = Enum.at(quantities, i, :unrestricted)
        if q == :unrestricted, do: {:unrestricted, :"V#{base + i}"}, else: {:erased, :"_f#{base + i}"}
      end

    field_names = Enum.map(fields, fn {_q, n} -> n end)
    new_ctx = Enum.reverse(field_names) ++ ctx
    body_form = lower(env, body, new_ctx)

    present =
      for {:unrestricted, n} <- fields,
          do: underscore_if_unused({:var, @line, n}, body_form)

    pattern =
      case present do
        [] -> {:atom, @line, otp_tag(bool_atom_or_self(env, cname))}
        _ -> {:tuple, @line, [{:atom, @line, otp_tag(cname)} | present]}
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

  # The canonical Std.Bounded family (registry-keyed, nominal): its `First`/`Next`
  # values erase to native BEAM integers (Fin-as-int), like Nat's Z/S.
  defp bounded_ctor?(env, name) do
    fam = Inductive.builtin(env, :bounded)
    fam != nil and Inductive.ctor_family(env, name) == fam
  end

  # Keep only the runtime-present args of a Bounded ctor app, dropping the erased
  # implicit index `m`. If erasure already stripped the args (their count matches
  # the present-quantity count) they are already the present ones; otherwise
  # filter the full arg list against the ctor's declared quantities.
  defp bounded_present_args(env, name, args) do
    case Inductive.ctor_quantities(env, name) do
      qs when is_list(qs) and length(qs) == length(args) ->
        for {a, :unrestricted} <- Enum.zip(args, qs), do: a

      _ ->
        args
    end
  end

  # The canonical Sigma family (registry-keyed, nominal): its values are the bare
  # BEAM 2-tuples the primitive pair always compiled to (spec 2026-07-09 D2 §1.5) —
  # Std.Pair's element/2 interop and AtomVM depend on the untagged shape.
  defp sigma_ctor?(env, name) do
    fam = Inductive.builtin(env, :sigma)
    fam != nil and Inductive.ctor_family(env, name) == fam
  end

  # The canonical Std.List family (registry-keyed, nominal): its values are native
  # BEAM lists — Nil is [], Cons(h,t) is [H|T] — so Erlang/AtomVM list NIFs interop.
  defp list_ctor?(env, name) do
    fam = Inductive.builtin(env, :list)
    fam != nil and Inductive.ctor_family(env, name) == fam
  end

  defp bool_atom(:True), do: true
  defp bool_atom(:False), do: false

  defp bool_atom_or_self(env, name) do
    if bool_ctor?(env, name), do: bool_atom(name), else: name
  end

  # The OTP-conventional constructors erase to their lowercase BEAM atoms so a
  # Cure `Result`/`Option` value is a native `{:ok, _}` / `{:error, _}` /
  # `{:some, _}` / `:none` term — the shape Erlang, Elixir, and (critically)
  # AtomVM FFI expect. `lib/std/core.cure` documents exactly this representation
  # (`Ok(value) -> {:ok, value}`, `None() -> :none`). Applied at BOTH the
  # construction and the pattern site so the tags agree. Every other constructor
  # keeps its declared (PascalCase) tag; records stay tagged tuples `{:Point,…}`.
  defp otp_tag(:Ok), do: :ok
  defp otp_tag(:Error), do: :error
  defp otp_tag(:Some), do: :some
  defp otp_tag(:None), do: :none
  defp otp_tag(name), do: name
end
