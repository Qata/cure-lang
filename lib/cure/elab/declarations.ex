defmodule Cure.Elab.Declarations do
  @moduledoc """
  Elaborate surface type declarations into `Cure.Core` inductive families
  (design spec §5; mirrors Idris `TTImp/ProcessData.idr`).

  Untrusted: it builds candidate `Inductive.family`/`Inductive.ctor` signatures
  and submits them to the kernel (`check_family`/`check_ctor` + strict
  positivity), so only well-formed families are registered.

  Handles the surface ADT form the parser produces today —
  `type X = A(T) | B | …` (`{:container, [container_type: :enum, …], variants}`).
  The family's universe level is inferred as the least level (0..ceiling) at
  which every constructor field type fits (the two-universe rule, §2): a field of
  type `Type` pushes the family to level 1. Indexed-GADT surface syntax
  (`indexed type … where`) is a separate parser extension (not yet in the
  grammar); the kernel-side indexed-family machinery it targets is complete (M3).
  """

  alias Cure.Core.{Context, Env, Eval, Inductive, Kernel}
  alias Cure.Elab.{Elaborator, Relevance}

  @ceiling 2

  @doc "Elaborate one declaration AST, returning the augmented signature."
  @spec elaborate(tuple(), Env.t()) :: {:ok, Env.t()} | {:error, term()}
  def elaborate({:function_def, _meta, _body} = decl, env) do
    with {:ok, env1} <- register_signature(decl, env) do
      elaborate_function_body(decl, env1)
    end
  end

  def elaborate({:container, meta, variants}, env) do
    case Keyword.get(meta, :container_type) do
      :enum ->
        name = meta |> Keyword.fetch!(:name) |> String.to_atom()

        case Keyword.get(meta, :type_params, []) do
          [] ->
            case build_ctors(variants) do
              {:ok, ctors} -> declare_at_min_level(env, name, ctors, 0)
              {:error, _} = err -> err
            end

          type_params ->
            # Parameterized ADT (`type List(a) = Nil | Cons(a, List(a))`). Each
            # positional variant is an implicit constructor signature returning the
            # family applied to its own parameters; reuse the parameterized-family
            # (GADT) machinery with an empty index telescope.
            params = Enum.map(type_params, fn p -> {:param, [], p} end)
            sigs = Enum.map(variants, &variant_to_gadt_sig(&1, name, type_params))
            declare_parameterized(name, params, [], sigs, env)
        end

      :struct ->
        # A record `rec Point\n  x: T\n  y: U` is a single-constructor family whose
        # constructor shares the family name and whose argument telescope is named by
        # the fields. The field names carried on the constructor telescope are what
        # record construction (`Point{x: .., y: ..}`) and projection (`p.x`) read to
        # map names to positions — no separate registry, and the kernel treats the
        # argument names as plain labels.
        name = meta |> Keyword.fetch!(:name) |> String.to_atom()

        with :ok <- check_no_duplicate_fields(variants) do
          case Keyword.get(meta, :type_params, []) do
            [] ->
              # Route through the GADT-ctor machinery with NAMED field domains so a
              # field's type may reference an EARLIER field (a dependent record):
              # `elaborate_gadt_ctor`'s named-binder scope-threading binds each field
              # name for subsequent field types. Non-dependent records are unaffected —
              # the resulting ctor telescope is still named by the fields, which is what
              # construction/projection read.
              sig = struct_ctor_sig(name, [], variants)
              working_env = Inductive.declare(env, Inductive.family(name, [], [], 0), [])

              with {:ok, [ctor]} <- elaborate_gadt_ctors([sig], name, [], [], working_env) do
                declare_at_min_level(env, name, [ctor], 0)
              end

            type_params ->
              declare_parameterized_struct(name, type_params, variants, env)
          end
        end

      other ->
        {:error, {:unsupported_container, other}}
    end
  end

  # Indexed (GADT) family: `type NAME(params) indices (idx) <ctor sigs>`. Head
  # `(params)` are uniform parameters (restated, never matched); the `indices`
  # clause lists the refined indices. Each constructor signature is an
  # `{:arrow_chain, [dom…, result]}`; the implicit index-variable telescope is
  # inferred from the signature (§5.2). A parameter-free family omits `(params)`.
  # Type alias `type Name = RHS`: a nullary definition `Name : Type := RHS`.
  # Conversion δ-unfolds `Name` to its right-hand side (a non-recursive alias is
  # trivially total, so it certifies and δ becomes available). No new type former.
  def elaborate({:type_annotation, meta, [rhs]}, env) do
    name = meta |> Keyword.fetch!(:name) |> String.to_atom()

    with {:ok, rhs_core} <- idx_to_core(rhs, [], nil, env) do
      env1 = Env.add_def(env, name, {:type, 0}, rhs_core, [])
      {:ok, maybe_certify(env1, name)}
    end
  end

  def elaborate({:indexed_type, meta, ctor_sigs}, env) do
    name = meta |> Keyword.fetch!(:name) |> String.to_atom()
    params = Keyword.get(meta, :params, [])
    index_params = Keyword.get(meta, :indices, [])
    declare_parameterized(name, params, index_params, ctor_sigs, env)
  end

  def elaborate({:interface, _meta, _methods} = decl, env) do
    Cure.Elab.Interface.elaborate(decl, env)
  end

  def elaborate(other, _env), do: {:error, {:unsupported_declaration, elem(other, 0)}}

  defp maybe_certify(env, name) do
    case Kernel.validate_certificate(env, name) do
      {:ok, certified} -> certified
      {:error, _} -> env
    end
  end

  # Elaborate a function's signature to its Π type and register it (with a
  # placeholder body) so that later-defined functions and mutually-recursive peers
  # resolve as globals. Called for every function in a first pass, before any body
  # is elaborated (see `Program.elaborate_declarations`).
  def register_signature({:function_def, meta, _body}, env) do
    with {:ok, sig} <- function_signature(meta, env) do
      {:ok, Env.add_def(env, sig.name, sig.pi, {:hole, "__pending__"}, sig.quantities)}
    end
  end

  # Elaborate a function's body against its (already registered) signature and
  # replace the placeholder with the real lambda. The environment already carries
  # every function's signature, so forward references and mutual recursion resolve.
  def elaborate_function_body({:function_def, meta, body}, env) do
    case Keyword.get(meta, :extern) do
      {mod, fun, arity} when is_atom(mod) and is_atom(fun) and is_integer(arity) ->
        # Wave-3: a bodyless @extern is a typed FFI postulate — the signature IS
        # the type; there is no term to elaborate/check. Mark the def with an
        # extern sentinel (NOT a hole, so emit.reject_holes passes; NOT
        # builtin_op, which is overloaded). emit lowers it to a remote call;
        # TotalityClosure skips it. Do NOT call elaborate_body / Kernel.check /
        # Relevance.check (no term exists).
        with {:ok, sig} <- function_signature(meta, env) do
          {:ok, Env.add_def(env, sig.name, sig.pi, {:extern, {mod, fun, arity}}, sig.quantities)}
        end

      _ ->
        elaborate_real_body(meta, body, env)
    end
  end

  defp elaborate_real_body(meta, body, env) do
    body_expr = single_body(body)

    with {:ok, sig} <- function_signature(meta, env) do
      ctx = build_context(env, sig.telescope)
      return_value = Eval.eval(sig.return_core, Context.env(ctx))

      with {:ok, body_term} <-
             elaborate_body(body_expr, sig.return_core, sig.scope, ctx, env, sig.params),
           :ok <- Kernel.check(ctx, body_term, return_value),
           # {0,ω} relevance check (M8.3): erasure will drop the `:erased` parameter
           # slots, so reject any body that uses one relevantly (returned / passed
           # in a present position / scrutinised / applied). E-layer; the kernel
           # stays quantity-blind. See `Cure.Elab.Relevance`.
           :ok <- Relevance.check(env, sig.name, sig.quantities, body_term) do
        lambda = wrap_binders(:lam, sig.telescope, body_term)
        final = Env.add_def(env, sig.name, sig.pi, lambda, sig.quantities)
        # Best-effort totality certification, eagerly and in declaration order, so a
        # later def's type may δ-reduce this one (e.g. `plus` in `Vec(a, plus(m,n))`
        # must unfold while `append`'s body is checked). A function that fails the
        # kernel's totality check simply stays uncertified — opaque to δ, never a
        # soundness hole (§7). Whole-program enforcement of the *required* set still
        # happens in TotalityClosure.certify_type_level.
        {:ok, maybe_certify(final, sig.name)}
      end
    end
  end

  # Shared signature elaboration: auto-generalize free type variables, build the
  # parameter telescope and the Π type. Deterministic in the type environment, so
  # the signature computed in the registration pass and the body pass agree.
  defp function_signature(meta, env) do
    name = meta |> Keyword.fetch!(:name) |> String.to_atom()
    params0 = Keyword.get(meta, :params, [])
    return_expr = Keyword.fetch!(meta, :return_type)

    # Idris-style auto-generalization: a free lowercase type variable in the
    # signature (`fn id(x: a) -> a`) is bound as a leading implicit `{a: Type}`
    # (erased), in order of first appearance. Restricted to occurrences provably of
    # kind Type, so an index variable (`Vec(_, n)`, `n : Nat`) is NOT mis-bound.
    params = auto_generalize(params0, return_expr, env) ++ params0

    with {:ok, telescope, quantities, scope} <- elaborate_param_telescope(params, env),
         ctx = build_context(env, telescope),
         {:ok, return_core} <- idx_to_core(return_expr, scope, nil, env, ctx) do
      {:ok,
       %{
         name: name,
         params: params,
         telescope: telescope,
         quantities: quantities,
         scope: scope,
         return_core: return_core,
         pi: wrap_binders(:pi, telescope, return_core)
       }}
    end
  end

  # A parameterized record `rec Box(a)\n  val: a` is a single-constructor
  # parameterized family. Build the constructor through the shared GADT-ctor
  # machinery from a NAMED-domain signature (`struct_ctor_sig`), which handles the
  # parameter telescope and the de-Bruijn-correct result parameters AND names the
  # ctor telescope by the fields (so construction/projection find them) while
  # threading each field into scope for the following field types (a dependent
  # record — `rec Box(a)\n  n: Nat\n  v: Vec(a, n)`).
  defp declare_parameterized_struct(name, type_params, fields, env) do
    params = Enum.map(type_params, fn p -> {:param, [], p} end)
    sig = struct_ctor_sig(name, type_params, fields)

    with {:ok, param_tele} <- elaborate_index_telescope(params, name, env, [], :duplicate_parameter),
         working_env = Inductive.declare(env, Inductive.family(name, param_tele, [], 0), []),
         {:ok, [ctor]} <- elaborate_gadt_ctors([sig], name, param_tele, [], working_env) do
      declare_indexed_at_min_level(env, name, param_tele, [], [ctor], 0)
    end
  end

  # A record `rec R(params)\n f1: T1\n f2: T2` as a single GADT-constructor signature
  # with NAMED field domains, so `elaborate_gadt_ctor`'s named-binder scope-threading
  # binds each field for the following field types (a dependent record) and names the
  # resulting ctor telescope by the fields (what construction/projection read).
  defp struct_ctor_sig(name, type_params, fields) do
    named_doms =
      Enum.map(fields, fn {:param, m, fname} ->
        {:named_dom, fname, Keyword.fetch!(m, :type)}
      end)

    {:gadt_ctor, [name: Atom.to_string(name)], {:arrow_chain, named_doms ++ [family_app(name, type_params)]}}
  end

  # A positional enum variant, seen as a GADT constructor signature that returns
  # the family applied to its own parameters. `Nil` → `Nil : List(a)`;
  # `Cons(a, List(a))` → `Cons : a -> List(a) -> List(a)`.
  defp variant_to_gadt_sig({:variable, _meta, vname}, fam, type_params) do
    {:gadt_ctor, [name: vname], {:arrow_chain, [family_app(fam, type_params)]}}
  end

  defp variant_to_gadt_sig({:function_def, cmeta, _body}, fam, type_params) do
    cname = Keyword.fetch!(cmeta, :name)
    field_asts = Keyword.fetch!(cmeta, :params)
    {:gadt_ctor, [name: cname], {:arrow_chain, field_asts ++ [family_app(fam, type_params)]}}
  end

  defp family_app(fam, type_params) do
    args = Enum.map(type_params, fn p -> {:variable, [scope: :local], p} end)
    {:function_call, [name: Atom.to_string(fam)], args}
  end

  # Declare a family with a parameter telescope and (optionally) an index
  # telescope from GADT-style constructor signatures. Shared by indexed types and
  # parameterized enums (the latter pass no indices).
  defp declare_parameterized(name, params, index_params, ctor_sigs, env) do
    # Parameters are the outer binders: elaborate the param telescope first, then
    # the index telescope in the scope of the parameters (most-recent first).
    param_scope = params |> Enum.map(fn {:param, _m, n} -> n end) |> Enum.reverse()

    with {:ok, param_tele} <- elaborate_index_telescope(params, name, env, [], :duplicate_parameter),
         {:ok, index_tele} <- elaborate_index_telescope(index_params, name, env, param_scope),
         # Pre-register the family signature (empty ctors, tentative level) so
         # self-references in constructor signatures — e.g. `Vector(a, n)` as a
         # `prepend` domain — resolve their parameter arity via param_count when
         # converted to Core. The authoritative declaration happens below.
         working_env = Inductive.declare(env, Inductive.family(name, param_tele, index_tele, 0), []),
         {:ok, ctors} <- elaborate_gadt_ctors(ctor_sigs, name, param_tele, index_tele, working_env) do
      declare_indexed_at_min_level(env, name, param_tele, index_tele, ctors, 0)
    end
  end

  # -- function elaboration ---------------------------------------------------

  defp single_body([expr]), do: expr
  defp single_body(expr), do: expr

  # A `match` body needs the declared return type to build its motive (checking
  # mode); every other body is elaborated in inference mode.
  defp elaborate_body({:pattern_match, _meta, [scrut | arms]}, return_core, scope, ctx, env, _params) do
    Elaborator.elaborate_match(scrut, arms, return_core, scope, ctx, env)
  end

  # A `with <expr>` body (capability A): like `match`, but its motive
  # value-abstracts the scrutinee EXPRESSION out of the goal, so each branch's
  # goal is refined to the branch constructor's value (goal refinement plain
  # `match` cannot do). Checking mode — the declared return type is the goal.
  defp elaborate_body({:with_abs, meta, [scrut | arms]}, return_core, scope, ctx, env, params) do
    proof = Keyword.get(meta, :proof)
    Elaborator.elaborate_with(scrut, arms, proof, return_core, scope, ctx, env, params)
  end

  defp elaborate_body({:rewrite_expr, _meta, _children} = expr, return_core, scope, ctx, env, _params) do
    Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)
  end

  defp elaborate_body({:function_call, meta, _args} = expr, return_core, scope, ctx, env, _params) do
    name = Keyword.get(meta, :name)
    atom = if is_binary(name), do: String.to_atom(name)

    cond do
      name == "reflexive" ->
        Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)

      atom && Inductive.get_ctor(env, atom) ->
        # A constructor body is checked against the declared return type, so a
        # nullary or otherwise underdetermined constructor (`Nil()` at
        # `-> List(Nat)`) can pin its implicit parameters from the goal rather than
        # failing with unsolved metavariables under pure inference.
        Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)

      true ->
        # A non-constructor call body is inferred, then (mirroring the constructor
        # branch above) retried in *checking* mode when inference fails only because
        # an implicit stayed unsolved. This lets an implicit determined by NEITHER
        # argument — only by the declared return type (`mk(Z()) : Const(Nat, Bool)`,
        # whose phantom `{b}` no argument fixes) — be solved from the goal. Additive:
        # the checked retry runs only after inference errored with
        # `:unsolved_metavariables`, and the original error is surfaced if it too
        # fails, so every currently-accepted or -rejected body is unchanged.
        case Elaborator.elaborate_expr_typed(expr, scope, ctx, env) do
          {:ok, term, _type} ->
            {:ok, term}

          {:error, {:unsolved_metavariables, _}} = orig ->
            case Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env) do
              {:ok, term} -> {:ok, term}
              {:error, _} -> orig
            end

          {:error, _} = orig ->
            orig
        end
    end
  end

  # A pair `%[a, b]` is a dependent-pair introduction; the kernel checks it
  # against the declared Σ return type.
  defp elaborate_body({:tuple, _meta, [a_ast, b_ast]} = expr, return_core, scope, ctx, env, _params) do
    # Check the pair against the declared return type first, so a *dependent* pair
    # (`Sigma(n: Nat, Vector(a, n))`) elaborates its second component against the
    # codomain instantiated at the first — otherwise a component like
    # `prepend(x, empty())` is inferred and its underdetermined parts are left as
    # unsolved metavariables. Fall back to inferring both components when the
    # return type is not a Σ the checker can use (preserving the prior behaviour).
    case Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env) do
      {:ok, term} ->
        {:ok, term}

      {:error, _} ->
        with {:ok, a_term, _} <- Elaborator.elaborate_expr_typed(a_ast, scope, ctx, env),
             {:ok, b_term, _} <- Elaborator.elaborate_expr_typed(b_ast, scope, ctx, env) do
          {:ok, {:ctor, sigma_mk_pair(env), [a_term, b_term]}}
        end
    end
  end

  # A hole body `?name` elaborates to a `:hole` term (accepted at the declared
  # return type by the kernel; it blocks codegen until filled).
  defp elaborate_body({:hole, meta, _}, _return_core, _scope, _ctx, _env, _params) do
    {:ok, {:hole, Keyword.get(meta, :name, "")}}
  end

  # A `let … ⏎ body` block: check it against the declared return type (there is
  # no `:let` in Core — the elaborator desugars each binding to a β-redex).
  defp elaborate_body({:block, _meta, _stmts} = expr, return_core, scope, ctx, env, _params) do
    Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)
  end

  # `if …` as a function body: check it against the declared return type so both
  # branches inherit the expected type (a constant-motive `:case` on the inductive Bool).
  defp elaborate_body({:conditional, _meta, _} = expr, return_core, scope, ctx, env, _params) do
    Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)
  end

  # A lambda body has untyped parameters, so it must be *checked* against the
  # declared return type (a Π) rather than inferred — `fn(y) -> …` returning a
  # function type. Other bodies stay on the inference path below.
  defp elaborate_body({:lambda, _meta, _} = expr, return_core, scope, ctx, env, _params) do
    Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)
  end

  # A `[]`/`[h|t]`/`[a,b,c]` body: check it against the declared return type so a
  # bare `[]` (which desugars to `Nil` with a metavariable element type) pins that
  # element type from the goal instead of failing `{:unsolved_metavariables, :Nil}`
  # (Finding A). `elaborate_expr_checked` self-desugars the `:list` node.
  defp elaborate_body({:list, _, _} = expr, return_core, scope, ctx, env, _params),
    do: Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)

  # A `pickup …` body: check it against the declared return type so a first clause
  # whose then-branch is bare `[]` (the `take` shape) pins its element type from
  # the goal rather than being elaborated infer-only first.
  defp elaborate_body({:pickup, _, _} = expr, return_core, scope, ctx, env, _params),
    do: Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)

  # A bare literal body is checked against the declared return type so a numeric
  # literal at `Nat`/`Bounded(n)` lowers to its compact `{:nat_lit,_}`/
  # `{:bounded_lit,_}` form (`fn a() -> Char = 97`), instead of inferring `Int` and
  # then failing conversion. Non-numeric / Int/Float literals fall through the
  # checked path to the same infer-and-convert behavior as before.
  defp elaborate_body({:literal, _meta, _value} = expr, return_core, scope, ctx, env, _params),
    do: Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)

  defp elaborate_body(expr, _return_core, scope, ctx, env, _params) do
    with {:ok, term, _type} <- Elaborator.elaborate_expr_typed(expr, scope, ctx, env) do
      {:ok, term}
    end
  end

  # The registered Sigma constructor name (canonically `:mk_pair`), via the builtin
  # registry; defaults to `:mk_pair` when no Sigma family is registered.
  defp sigma_mk_pair(env) do
    with fam when not is_nil(fam) <- Inductive.builtin(env, :sigma),
         [%{name: n} | _] <- Inductive.ctors_of(env, fam) do
      n
    else
      _ -> :mk_pair
    end
  end

  # Convert the parameter list into a Core telescope + {0,ω} quantities, with each
  # parameter type elaborated in the scope of the preceding parameters. Implicit
  # (`{name}`) parameters are erased. Returns the scope (names, most-recent first).
  # Collect the signature's free type variables (lowercase, unbound, not a known
  # family) that occur in a kind-`Type` position, and return them as leading
  # implicit parameters in order of first appearance.
  defp auto_generalize(params, return_expr, env) do
    bound = params |> Enum.map(fn {:param, _m, n} -> n end) |> MapSet.new()

    type_asts =
      Enum.map(params, fn {:param, m, _n} -> Keyword.get(m, :type) end) ++ [return_expr]

    {ordered, _seen} =
      type_asts
      |> Enum.reject(&is_nil/1)
      |> Enum.reduce({[], MapSet.new()}, fn ast, acc -> collect_type_vars(ast, bound, env, acc) end)

    Enum.map(ordered, fn n -> {:param, [implicit: true], n} end)
  end

  # A type variable occurs here at kind `Type`: collect it if lowercase, unbound,
  # not `Type`, and not a known family.
  defp collect_type_vars({:variable, _m, name}, bound, env, {ordered, seen} = acc) do
    cond do
      not type_var_name?(name) -> acc
      name == "Type" -> acc
      MapSet.member?(bound, name) -> acc
      MapSet.member?(seen, name) -> acc
      Inductive.family?(env, String.to_atom(name)) -> acc
      true -> {ordered ++ [name], MapSet.put(seen, name)}
    end
  end

  # A function type `(A) -> B`: every domain and the codomain is a type (kind Type).
  # A family/type application `F(args)`: only the leading parameter slots whose kind
  # is `Type` are kind-`Type` positions; index slots (e.g. `Vec(a, n)`'s `n : Nat`)
  # are not, so they are skipped and their variables are left to normal resolution.
  defp collect_type_vars({:function_call, meta, args}, bound, env, acc) do
    if Keyword.get(meta, :function_type) do
      Enum.reduce(args, acc, &collect_type_vars(&1, bound, env, &2))
    else
      fam = String.to_atom(Keyword.get(meta, :name, ""))

      {pc, ptele} =
        if Inductive.family?(env, fam),
          do: {Inductive.param_count(env, fam), Inductive.param_telescope(env, fam) || []},
          else: {0, []}

      args
      |> Enum.with_index()
      |> Enum.reduce(acc, fn {arg, i}, acc2 ->
        if i < pc and match?({:type, _}, elem(Enum.at(ptele, i, {nil, nil}), 1)),
          do: collect_type_vars(arg, bound, env, acc2),
          else: acc2
      end)
    end
  end

  defp collect_type_vars({:sigma_type, _m, children}, bound, env, acc) when is_list(children) do
    Enum.reduce(children, acc, &collect_type_vars(&1, bound, env, &2))
  end

  defp collect_type_vars(_other, _bound, _env, acc), do: acc

  defp type_var_name?(<<c, _::binary>>) when c in ?a..?z, do: true
  defp type_var_name?(_), do: false

  # A record must not declare the same field name twice: fields become the named
  # constructor telescope (and records compile to BEAM maps keyed by field name), so
  # a duplicate silently collapses one field. Idris/Agda/Lean reject duplicate record
  # fields.
  defp check_no_duplicate_fields(fields) do
    names =
      Enum.flat_map(fields, fn
        {:param, _m, fname} -> [fname]
        _ -> []
      end)

    case names -- Enum.uniq(names) do
      [] -> :ok
      [dup | _] -> {:error, {:duplicate_field, String.to_atom(dup)}}
    end
  end

  # The first repeated (non-wildcard) binder name in a `{:param, _, name}` list,
  # or nil if the telescope is linear. Shared by every telescope builder — a
  # repeated binder makes later types / bodies that reference it ambiguous.
  defp duplicate_param_name(params) do
    names =
      params
      |> Enum.flat_map(fn
        {:param, _m, n} -> [n]
        _ -> []
      end)
      |> Enum.reject(&(&1 == "_"))

    case names -- Enum.uniq(names) do
      [] -> nil
      [dup | _] -> dup
    end
  end

  defp elaborate_param_telescope(params, env) do
    # A telescope must not bind the same parameter name twice: a later parameter's
    # type (and the body) can refer to an earlier binder by name, so a duplicate
    # silently shadows the first and makes the reference ambiguous. Idris/Agda/Lean
    # reject repeated binder names in a telescope.
    # The bare wildcard `_` binds nothing, so it is exempt — several ignored
    # arguments may all be `_`.
    pnames =
      params
      |> Enum.map(fn {:param, _m, n} -> n end)
      |> Enum.reject(&(&1 == "_"))

    case pnames -- Enum.uniq(pnames) do
      [dup | _] ->
        {:error, {:duplicate_parameter, String.to_atom(dup)}}

      [] ->
        elaborate_param_telescope_rec(params, env)
    end
  end

  defp elaborate_param_telescope_rec(params, env) do
    params
    |> Enum.reduce_while({:ok, [], [], []}, fn {:param, pmeta, pname}, {:ok, tele, quants, scope} ->
      case Keyword.get(pmeta, :type) do
        nil ->
          if Keyword.get(pmeta, :implicit) do
            # A bare implicit parameter `{a}` (no kind) is a type variable ranging
            # over `Type`; it is erased, exactly like `{a: Type}`.
            {:cont, {:ok, tele ++ [{String.to_atom(pname), {:type, 0}}], quants ++ [:erased], [pname | scope]}}
          else
            {:halt, {:error, {:untyped_parameter, pname}}}
          end

        type_expr ->
          case idx_to_core(type_expr, scope, nil, env) do
            {:ok, core} ->
              q = if Keyword.get(pmeta, :implicit), do: :erased, else: :present
              {:cont, {:ok, tele ++ [{String.to_atom(pname), core}], quants ++ [q], [pname | scope]}}

            {:error, _} = err ->
              {:halt, err}
          end
      end
    end)
    |> case do
      {:ok, tele, quants, scope} -> {:ok, tele, quants, scope}
      {:error, _} = err -> err
    end
  end

  defp build_context(env, telescope) do
    Enum.reduce(telescope, Context.empty(env), fn {_name, type_core}, ctx ->
      # Weak-head-normalise each binder type so a type alias (`type Endo = (Nat) ->
      # Nat`, a certified δ-def) is stored as the underlying Π/Σ/data value the
      # kernel inspects — e.g. applying an `Endo`-typed parameter reaches a Π. This
      # is conversion-preserving (the alias is definitionally its right-hand side)
      # and idempotent for a type already in head form.
      type_value =
        type_core
        |> Eval.eval(Context.env(ctx))
        |> Cure.Core.Normalise.whnf_value(env)

      Context.extend(ctx, type_value)
    end)
  end

  defp wrap_binders(tag, telescope, inner) do
    Enum.reduce(Enum.reverse(telescope), inner, fn {_name, type}, acc -> {tag, type, acc} end)
  end

  # -- indexed families -------------------------------------------------------

  # The family's index telescope, converting each `i: T` in the scope of the
  # preceding index binders (most-recently-bound first).
  # `dup_tag` names the binder kind for the linearity error — this builder is shared
  # by the family PARAMETER telescope (`:duplicate_parameter`) and the INDEX
  # telescope (`:duplicate_index`).
  defp elaborate_index_telescope(params, fam, env, init_scope, dup_tag \\ :duplicate_index) do
    case duplicate_param_name(params) do
      nil -> elaborate_index_telescope_rec(params, fam, env, init_scope)
      dup -> {:error, {dup_tag, String.to_atom(dup)}}
    end
  end

  defp elaborate_index_telescope_rec(params, fam, env, init_scope) do
    params
    |> Enum.reduce_while({:ok, [], init_scope}, fn {:param, pmeta, pname}, {:ok, tele, scope} ->
      # A bare type parameter (`type Box(a)` → `{:param, [], "a"}`) carries no
      # explicit kind; it ranges over types, so default its kind to `Type`.
      type_ast = Keyword.get(pmeta, :type, {:variable, [scope: :local], "Type"})

      case idx_to_core(type_ast, scope, fam, env) do
        {:ok, core} ->
          {:cont, {:ok, tele ++ [{String.to_atom(pname), core}], [pname | scope]}}

        {:error, _} = err ->
          {:halt, err}
      end
    end)
    |> case do
      {:ok, tele, _scope} -> {:ok, tele}
      {:error, _} = err -> err
    end
  end

  defp elaborate_gadt_ctors(sigs, fam, param_tele, index_tele, env) do
    Enum.reduce_while(sigs, {:ok, []}, fn sig, {:ok, acc} ->
      case elaborate_gadt_ctor(sig, fam, param_tele, index_tele, env) do
        {:ok, ctor} -> {:cont, {:ok, acc ++ [ctor]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp elaborate_gadt_ctor({:gadt_ctor, cmeta, {:arrow_chain, atoms}}, fam, param_tele, index_tele, env) do
    cname = cmeta |> Keyword.fetch!(:name) |> String.to_atom()
    {dom_exprs, result_expr} = split_last(atoms)

    # The family's parameters are bound OUTSIDE this constructor's telescope (the
    # kernel binds them first, then the ctor args). Referencing a parameter from
    # a ctor arg type or the result therefore reaches past all ctor args into the
    # param region — model that by appending the params (most-recent first, so
    # they occupy the highest de Bruijn levels) to every local scope.
    param_count = length(param_tele)
    param_scope = param_tele |> Enum.map(fn {n, _t} -> Atom.to_string(n) end) |> Enum.reverse()

    with :ok <- ensure_linear_named_doms(dom_exprs),
         {:ok, applied_exprs} <- family_index_args(result_expr, fam) do
      # Implicit index variables are inferred from every family application in
      # the signature (domains + the result), positionally typed by the family's
      # index telescope. Ordered by first appearance → the leading telescope.
      # Parameters are NOT inference candidates (see infer_implicits' skip).
      # Names bound explicitly by a NAMED dependent domain `(k: Nat)`. Such a
      # binder is a runtime argument, not an inferred index variable, so it must
      # be excluded from implicit inference even though it appears in later
      # domain types / the result index (`SNat(k)`, `NVv(S(k))`).
      explicit_names =
        for {:named_dom, name, _inner} <- dom_exprs, into: MapSet.new(), do: name

      infer_exprs = Enum.map(dom_exprs, &strip_named_dom/1) ++ [result_expr]

      implicits =
        infer_exprs
        |> infer_implicits(fam, index_tele, env, param_count)
        |> Enum.reject(fn {n, _t} -> MapSet.member?(explicit_names, n) end)

      impl_names = Enum.map(implicits, &elem(&1, 0))

      case build_explicit_tele(dom_exprs, impl_names, param_scope, fam, env) do
        {:ok, expl_tele, expl_names} ->
          full_scope = Enum.reverse(impl_names ++ expl_names) ++ param_scope
          {param_exprs, index_exprs} = Enum.split(applied_exprs, param_count)

          with {:ok, result_params} <- map_idx_to_core(param_exprs, full_scope, fam, env),
               {:ok, result_indices} <- map_idx_to_core(index_exprs, full_scope, fam, env) do
            impl_tele = Enum.map(implicits, fn {n, ty} -> {String.to_atom(n), ty} end)
            # Inferred index variables are erased (quantity 0); the explicit
            # arguments are runtime-relevant (quantity ω). See M8.3 / M9.
            quantities =
              List.duplicate(:erased, length(impl_tele)) ++
                List.duplicate(:present, length(expl_tele))

            {:ok, Inductive.ctor(cname, impl_tele ++ expl_tele, result_indices, quantities, result_params)}
          end

        {:error, _} = err ->
          err
      end
    end
  end

  defp split_last(list), do: {Enum.slice(list, 0..-2//1), List.last(list)}

  # For implicit-variable inference we scan a named binder `(k: Nat)` by its
  # inner type (`Nat`); the binder name itself is handled as an explicit arg.
  defp strip_named_dom({:named_dom, _name, inner}), do: inner
  defp strip_named_dom(other), do: other

  # A constructor's named dependent domains must be linear: a repeated binder
  # (`(x: Nat) -> (x: Nat) -> …`) shadows and makes later references ambiguous,
  # exactly like a duplicate function parameter. The bare `_` binds nothing.
  defp ensure_linear_named_doms(dom_exprs) do
    named = for {:named_dom, n, _} <- dom_exprs, n != "_", do: n

    case named -- Enum.uniq(named) do
      [] -> :ok
      [dup | _] -> {:error, {:duplicate_parameter, String.to_atom(dup)}}
    end
  end

  defp family_index_args({:function_call, fmeta, args}, fam) do
    if String.to_atom(Keyword.fetch!(fmeta, :name)) == fam,
      do: {:ok, args},
      else: {:error, {:result_type_not_family, fam}}
  end

  defp family_index_args({:variable, _, name}, fam) do
    if String.to_atom(name) == fam,
      do: {:ok, []},
      else: {:error, {:result_type_not_family, fam}}
  end

  defp family_index_args(other, _fam), do: {:error, {:bad_result_type, other}}

  # Explicit-argument telescope: convert each domain in the scope of all
  # preceding binders (implicits, then earlier explicits). Anonymous names.
  defp build_explicit_tele(dom_exprs, impl_names, param_scope, fam, env) do
    dom_exprs
    |> Enum.with_index()
    |> Enum.reduce_while({:ok, [], Enum.reverse(impl_names) ++ param_scope, []}, fn {dom, i},
                                                                                    {:ok, tele, scope, names} ->
      # A NAMED dependent binder `(k: Nat)` uses its declared name (so later
      # domains and the result index can reference it); an unnamed arg keeps its
      # anonymous `_aN` name byte-for-byte. Either way the scope is threaded so
      # the next domain's de Bruijn indices resolve this binder.
      {argname, type_expr} =
        case dom do
          {:named_dom, name, inner} -> {name, inner}
          _ -> {"_a#{i}", dom}
        end

      case idx_to_core(type_expr, scope, fam, env) do
        {:ok, core} ->
          {:cont, {:ok, tele ++ [{String.to_atom(argname), core}], [argname | scope], names ++ [argname]}}

        {:error, _} = err ->
          {:halt, err}
      end
    end)
    |> case do
      {:ok, tele, _scope, names} -> {:ok, tele, names}
      {:error, _} = err -> err
    end
  end

  # -- implicit index-variable inference --------------------------------------

  defp infer_implicits(exprs, fam, index_tele, env, self_param_count) do
    {ordered, _seen} =
      Enum.reduce(exprs, {[], MapSet.new()}, fn e, acc ->
        collect_implicit_vars(e, fam, index_tele, env, self_param_count, acc)
      end)

    ordered
  end

  defp collect_implicit_vars({:function_call, fmeta, args}, fam, index_tele, env, self_param_count, acc) do
    name = String.to_atom(Keyword.fetch!(fmeta, :name))
    index_types = family_index_types(name, fam, index_tele, env)

    # A family application's leading `param_count` arguments are parameters, not
    # index-typed positions — skip them so the remaining args align 0-based with
    # the index telescope (and parameters are never collected as implicits).
    app_param_count =
      cond do
        name == fam -> self_param_count
        Inductive.family?(env, name) -> Inductive.param_count(env, name)
        true -> 0
      end

    acc =
      cond do
        index_types ->
          args
          |> Enum.drop(app_param_count)
          |> Enum.with_index()
          |> Enum.reduce(acc, fn {arg, pos}, a ->
            collect_index_expr_vars(a, arg, Enum.at(index_types, pos), fam, env)
          end)

        # A COMPUTED index expression: a non-family global function (`app`,
        # `dmeet`, `∧`, …) used inside an index. An index variable that appears
        # ONLY here (e.g. the fed-back `cv` in `app(av, cv)` inside a `loop`
        # constructor's ARGUMENT type) must still be inferred as an implicit,
        # typed by the function's domain telescope. Non-dependent domains only
        # (our index functions are non-dependent); a mistyped binder would fail
        # the kernel check, never silently mis-accept.
        dom = global_domain_types(name, env) ->
          args
          |> Enum.with_index()
          |> Enum.reduce(acc, fn {arg, pos}, a ->
            case arg do
              {:variable, _, vname} -> maybe_add_implicit(a, vname, Enum.at(dom, pos), fam, env)
              _ -> a
            end
          end)

        true ->
          acc
      end

    Enum.reduce(args, acc, fn a, ac -> collect_implicit_vars(a, fam, index_tele, env, self_param_count, ac) end)
  end

  defp collect_implicit_vars(_other, _fam, _index_tele, _env, _self_param_count, acc), do: acc

  # Collect free variables from an index EXPRESSION typed by `type`, recursing into
  # constructor applications so a variable that appears only *inside* a constructor
  # in the result index — `m` in `fz : Fin(S(m))` / `FZ : Fin (S n)` — is inferred
  # as an implicit, typed by the enclosing constructor's field type. Idris binds
  # these automatically; without it the variable is unbound (`:index_mismatch`). A
  # bare variable is added directly (the pre-existing behaviour).
  defp collect_index_expr_vars(acc, {:variable, _, vname}, type, fam, env),
    do: maybe_add_implicit(acc, vname, type, fam, env)

  defp collect_index_expr_vars(acc, {:function_call, cmeta, cargs}, _type, fam, env) do
    cname = cmeta |> Keyword.fetch!(:name) |> String.to_atom()

    case Inductive.get_ctor(env, cname) do
      %{args: fields} ->
        field_types = Enum.map(fields, fn {_n, t} -> t end)

        cargs
        |> Enum.with_index()
        |> Enum.reduce(acc, fn {carg, i}, a ->
          collect_index_expr_vars(a, carg, Enum.at(field_types, i), fam, env)
        end)

      _ ->
        acc
    end
  end

  defp collect_index_expr_vars(acc, _other, _type, _fam, _env), do: acc

  # Domain (argument) types of a defined global function, peeled from its Pi
  # type, or nil if `name` is not a defined global. Used to type index variables
  # occurring inside a computed index expression (see `collect_implicit_vars`).
  defp global_domain_types(name, env) do
    case Env.get_def(env, name) do
      %{type: ty} -> pi_domains(ty)
      _ -> nil
    end
  end

  defp pi_domains({:pi, dom, cod}), do: [dom | pi_domains(cod)]
  defp pi_domains(_), do: []

  # The positional index types of family `name` (self or already registered).
  defp family_index_types(name, fam, index_tele, env) do
    cond do
      name == fam -> Enum.map(index_tele, &elem(&1, 1))
      Inductive.family?(env, name) -> Enum.map(Inductive.index_telescope(env, name) || [], &elem(&1, 1))
      true -> nil
    end
  end

  defp maybe_add_implicit({ordered, seen} = acc, vname, type, fam, env) do
    atom = String.to_atom(vname)

    cond do
      type == nil -> acc
      MapSet.member?(seen, vname) -> acc
      vname == "Type" -> acc
      atom == fam -> acc
      Inductive.get_ctor(env, atom) -> acc
      Inductive.family?(env, atom) -> acc
      Env.get_def(env, atom) -> acc
      true -> {ordered ++ [{vname, type}], MapSet.put(seen, vname)}
    end
  end

  # -- surface index/type expr → Core, with a de Bruijn scope -----------------

  # `ctx` (5th arg, spec 2026-07-08 §7.3): the kernel typing context for the
  # enclosing fn's parameters, threaded ONLY by the return-type lowering in
  # `function_signature` (every other caller keeps the 4-arg form → nil). When
  # present, a function-call node whose head is a term-level global carrying
  # implicit (erased) parameters delegates to the term-position implicit-app
  # machinery instead of lowering as a bare explicit-args spine. Crossing a
  # binder-introducing form (pi/sigma/arrow) NULLs the ctx for that sub-lowering
  # (the scope gains binders the kernel context lacks — §7.3 item 4).
  @doc """
  The single canonical type→Core lowering, shared by the live signature path
  (`register_signature`/`elaborate_param_telescope`) and the legacy
  `Elaborator.elaborate_type/3`, which delegates here. `scope` names the binders
  in de Bruijn order (most-recent first); there is no family-relative context, so
  `fam`/`ctx` are `nil` (used only defensively for family self-reference and
  return-type implicit insertion). Lowers a type expression — including a numeric
  index like `Bounded(5)` → `{:nat_lit, 5}` — to a Core term.
  """
  @spec lower_type(tuple(), [String.t()], Env.t()) :: {:ok, tuple()} | {:error, term()}
  def lower_type(ast, scope, env), do: idx_to_core(ast, scope, nil, env, nil)

  # Classify an index NAME node as a numeral, since a name STARTING WITH A DIGIT
  # can only be a stringified numeric token from the type parser (Cure identifiers
  # never start with a digit) — never a binder. Returns:
  #   {:ok, n}     — a non-negative integer Nat index (compact `nat_lit`)
  #   {:error, r}  — a numeral-shaped name that is not a valid Nat index
  #                  (fractional or negative), an error rather than a phantom global
  #   :not_numeric — a real (non-numeric) name; fall through to binder/global lookup
  #
  # The lexer already normalizes hex (`0x…`), binary (`0b…`) and underscored
  # integers to a decimal digit-string, so those arrive as all-digits. Scientific
  # notation lexes as a float and arrives stringified (`1e6` → "1.0e6"); an
  # integer-valued float is a valid index, a genuinely fractional one is rejected.
  defp numeric_index_value(name) when is_binary(name) do
    cond do
      String.match?(name, ~r/\A[0-9]+\z/) ->
        {:ok, String.to_integer(name)}

      String.match?(name, ~r/\A[0-9]/) ->
        case Float.parse(name) do
          {f, ""} when f >= 0.0 ->
            t = trunc(f)
            if t * 1.0 == f, do: {:ok, t}, else: {:error, {:non_integer_index, name}}

          _ ->
            {:error, {:non_integer_index, name}}
        end

      true ->
        :not_numeric
    end
  end

  defp numeric_index_value(_), do: :not_numeric

  defp idx_to_core(ast, scope, fam, env, ctx \\ nil)

  defp idx_to_core({:variable, _meta, "Type"}, _scope, _fam, _env, _ctx), do: {:ok, {:type, 0}}

  defp idx_to_core({:variable, _meta, name}, scope, _fam, env, _ctx) do
    # A numeric literal in a dependent type index — the `5` in `Bounded(5)`, the
    # `0x110000` Char bound in `Bounded(1114112)`, a scientific `1e6`. The lexer's
    # numeric token is stringified into a NAME node by the type parser. It can never
    # be a binder (you cannot bind `5`), so it is unambiguously a compact `Nat`
    # literal regardless of scope — the surface half of the compact-Nat kernel path
    # (Lean/Agda: a numeral in index position is a `Nat`). Without this it fell
    # through to a phantom `{:global, :"5"}`.
    case numeric_index_value(name) do
      {:ok, n} ->
        {:ok, {:nat_lit, n}}

      {:error, reason} ->
        {:error, reason}

      :not_numeric ->
        cond do
          (idx = Enum.find_index(scope, &(&1 == name))) != nil ->
            {:ok, {:var, idx}}

          true ->
            case resolve_index_name(name, env) do
              {:ambiguous_name, atom, mods} -> {:error, {:ambiguous_name, atom, mods}}
              node -> {:ok, node}
            end
        end
    end
  end

  defp idx_to_core({:function_call, fmeta, args}, scope, fam, env, ctx) do
    if Keyword.get(fmeta, :function_type) do
      arrow_to_pi(args, scope, fam, env)
    else
      name = Keyword.fetch!(fmeta, :name)
      atom = String.to_atom(name)

      # Type-position implicit insertion (spec §7): a term-level global whose
      # signature carries erased (implicit) parameters cannot lower as a bare
      # explicit-args spine — the kernel would see an under-applied application
      # (the `b(first(p))` motive gap). With a typing context threaded in
      # (return-type lowering only), delegate the whole application to the
      # term-position machinery. A local binder of the same name shadows the
      # global (mirrors the applied-bound-var cond branch below), and families/
      # ctors never carry def quantities, so this misses them by construction.
      if ctx != nil and Enum.find_index(scope, &(&1 == name)) == nil and
           implicit_global?(env, atom) do
        with {:ok, term, _result_type} <-
               Cure.Elab.Elaborator.elaborate_implicit_global_app(env, atom, args, scope, ctx) do
          {:ok, term}
        end
      else
        with {:ok, core_args} <- map_idx_to_core(args, scope, fam, env, ctx) do
          qualified =
            if String.contains?(name, ".") do
              Cure.Elab.Resolution.resolve_qualified(env, name, :type)
            else
              :error
            end

          cond do
            match?({:ok, _}, qualified) ->
              {:ok, key} = qualified
              {params, indices} = Enum.split(core_args, Inductive.param_count(env, key))
              {:ok, {:data, key, params, indices}}

            # An applied BOUND variable — e.g. a higher-order parameter used as
            # `F(n)` where `F` is an implicit type-family parameter in scope. Resolve
            # the head against the de Bruijn scope; a local binder shadows a global,
            # so this is checked first. Without it `F(n)` became a dangling
            # `{:global, :F}`, and the call site's implicit substitution could never
            # turn `F` into a solvable metavariable (ledger #10 prerequisite).
            idx = Enum.find_index(scope, &(&1 == name)) ->
              {:ok, Enum.reduce(core_args, {:var, idx}, fn a, acc -> {:app, acc, a} end)}

            atom == fam or Inductive.family?(env, atom) ->
              # Split the applied arguments into the family's parameters (prefix) and
              # indices (suffix); the kernel checks each slot against its own
              # telescope. param_count is 0 for parameter-free families (all indices).
              {params, indices} = Enum.split(core_args, Inductive.param_count(env, atom))
              {:ok, {:data, atom, params, indices}}

            Inductive.get_ctor(env, atom) ->
              {:ok, {:ctor, atom, core_args}}

            true ->
              {:ok, Enum.reduce(core_args, {:global, atom}, fn a, acc -> {:app, acc, a} end)}
          end
        end
      end
    end
  end

  # Binder-introducing forms (sigma/pi/arrow) sub-lower with the 4-arg form:
  # the ctx is NULLed under their binders (spec §7.3 item 4). `Sigma(x: D, U)`
  # lowers to the builtin inductive `Sigma(D, λx:D. U)`: `body` was elaborated with
  # `bname` in scope, so it is already in the frame of one new lambda binder, and
  # wrapping it under `{:lam, dom, body}` is exactly that frame. `:Sigma` is the
  # canonical family name (only Std.Sigma registers `@builtin(:sigma)`), used as a
  # literal so `Sigma(..)` lowers even in a raw-`Env.empty()` elaboration.
  defp idx_to_core({:sigma_type, [binder: bname], [dom_ast, body_ast]}, scope, fam, env, _ctx) do
    with {:ok, dom} <- idx_to_core(dom_ast, scope, fam, env),
         {:ok, body} <- idx_to_core(body_ast, [bname | scope], fam, env) do
      {:ok, {:data, :Sigma, [dom, {:lam, dom, body}], []}}
    end
  end

  # A dependent function type `(x1: D1, …, xn: Dn) -> R` becomes the Π
  # `Π(x1:D1). … Π(xn:Dn). R`. Each domain is elaborated with the earlier binders
  # in scope, and the codomain with all of them, so `(n: N) -> P(n)` resolves the
  # `n` in `P(n)` as the Π-bound variable (de Bruijn `{:var, 0}`). Direct analog of
  # the `sigma_type` binder threading above; `nil` binders (anonymous domains, from
  # a mixed `(a, x: B) -> …`) push a placeholder so indices stay aligned.
  defp idx_to_core({:pi_type, [binders: names], asts}, scope, fam, env, _ctx) do
    {domains, [ret_ast]} = Enum.split(asts, length(asts) - 1)

    folded =
      Enum.zip(names, domains)
      |> Enum.reduce_while({:ok, [], scope}, fn {name, dom_ast}, {:ok, rev, sc} ->
        case idx_to_core(dom_ast, sc, fam, env) do
          {:ok, dom} -> {:cont, {:ok, [dom | rev], [name || :_ | sc]}}
          {:error, _} = err -> {:halt, err}
        end
      end)

    with {:ok, rev_doms, inner_scope} <- folded,
         {:ok, ret} <- idx_to_core(ret_ast, inner_scope, fam, env) do
      {:ok, Enum.reduce(rev_doms, ret, fn dom, acc -> {:pi, dom, acc} end)}
    end
  end

  # A qualified TYPE reference (`Std.Nat` / `Std.Nat.Nat`, no call parens) OR a
  # projection `p.1` / `p.2` used in a type position (e.g. `SF(as, bs, p.1)`).
  # For a projection, lower to the Std.Sigma projection global exactly as the
  # term-position `sigma_projection` does — the ctx threaded from the return-type
  # position (spec 2026-07-08 §7.3) is REQUIRED to solve the erased implicits, so
  # `ctx` must not be discarded. A `.1`/`.2` reached with `ctx == nil` (a non-
  # return-type index/telescope position that does not thread ctx) has no frame to
  # solve the implicits and errors precisely — a spec §7.5-class residual.
  defp idx_to_core({:attribute_access, meta, [inner_ast]} = node, scope, _fam, env, ctx) do
    attr = Keyword.fetch!(meta, :attribute)
    dotted = Cure.Compiler.Parser.dotted_path_of(node)

    cond do
      # A qualified TYPE reference like Std.Nat / Std.Nat.Nat (no call parens).
      is_binary(dotted) and match?({:ok, _}, Cure.Elab.Resolution.resolve_qualified(env, dotted, :type)) ->
        {:ok, key} = Cure.Elab.Resolution.resolve_qualified(env, dotted, :type)
        {:ok, {:data, key, [], []}}

      attr in ["1", "2"] and not is_nil(ctx) ->
        gname = if attr == "1", do: :sigma_first, else: :sigma_second

        with {:ok, term, _type} <-
               Cure.Elab.Elaborator.elaborate_implicit_global_app(env, gname, [inner_ast], scope, ctx) do
          {:ok, term}
        end

      attr in ["1", "2"] ->
        {:error, {:sigma_projection_needs_ctx, attr}}

      true ->
        {:error, {:bad_projection, attr}}
    end
  end

  defp idx_to_core(other, _scope, _fam, _env, _ctx), do: {:error, {:unsupported_index_expr, other}}

  # `(D1, …, Dn) -> R` (surface `Function(D1,…,Dn,R)`, tagged `function_type`)
  # becomes the non-dependent Π `Π(_:D1). … Π(_:Dn). R` — the native Core arrow the
  # kernel applies (`f(x)`) and checks lambdas against. Each type is elaborated in
  # the outer scope, then shifted past the arrow binders standing above it in the
  # nest (those binders are anonymous and unreferenced, so the shift only relocates
  # genuine outer-scope de Bruijn references).
  defp arrow_to_pi(args, scope, fam, env) do
    {domains, [ret]} = Enum.split(args, length(args) - 1)

    with {:ok, dom_cores} <- map_idx_to_core(domains, scope, fam, env),
         {:ok, ret_core} <- idx_to_core(ret, scope, fam, env) do
      pi =
        dom_cores
        |> Enum.with_index()
        |> Enum.reverse()
        |> Enum.reduce(Cure.Core.Term.shift(ret_core, length(dom_cores), 0), fn {dom, i}, acc ->
          {:pi, Cure.Core.Term.shift(dom, i, 0), acc}
        end)

      {:ok, pi}
    end
  end

  # A term-level global whose registered signature carries at least one erased
  # (implicit) parameter — the only shape the bare-spine lowering mis-handles.
  # Families and constructors are not defs, so they return false here. Mirrors
  # the precedent `implicit_def?/2` (elaborator.ex:1278-1283) exactly, including
  # its `is_list(q)` guard: `Env.add_def/4` (the 4-arg form used by some Antigen
  # synthetic environments, e.g. `lib/antigen/generators/closure_env.ex`) defaults
  # quantities to `nil`, and `:erased in nil` raises (`nil` is not Enumerable) —
  # the guard is required for the same reason it is in the precedent function.
  defp implicit_global?(env, atom) do
    case Env.get_def(env, atom) do
      %{quantities: q} when is_list(q) -> :erased in q
      _ -> false
    end
  end

  defp resolve_index_name(name, env) do
    atom = String.to_atom(name)

    # This runs only in a *type* position (`idx_to_core`), so a name that is both a
    # family and a constructor — a record, whose constructor shares the family name
    # — resolves to the family. A name that is only a constructor (a nullary value
    # like `Z` used as an index argument) still resolves to the constructor.
    cond do
      primitive_type(name) != nil ->
        primitive_type(name)

      Inductive.family?(env, atom) ->
        {:data, atom, [], []}

      Inductive.get_ctor(env, atom) ->
        {:ctor, atom, []}

      # A bare name reachable only under a single re-keyed `:"Mod#name"` variant
      # (shadowed-but-present, spec §3.3). Exactly-one resolves; ≥2 (ambiguous)
      # falls through to `{:global, atom}` here and is caught by R7 (Task 10).
      match?({:ok, _}, Cure.Elab.Resolution.resolve_bare_shadowed(env, atom)) ->
        {:ok, key} = Cure.Elab.Resolution.resolve_bare_shadowed(env, atom)
        if Inductive.family?(env, key), do: {:data, key, [], []}, else: {:ctor, key, []}

      # ≥2 distinct re-keyed origins, no local/unshadowed winner: unqualified use
      # is ambiguous (R7). The caller turns this marker into an error.
      length(Cure.Elab.Resolution.ambiguous_modules(env, atom)) >= 2 ->
        {:ambiguous_name, atom, Cure.Elab.Resolution.ambiguous_modules(env, atom)}

      true ->
        {:global, atom}
    end
  end

  # The built-in primitive types that map to Core type-constants (not opaque
  # globals). `Int`/`Float` stay irreducibly primitive (BEAM machine types).
  # `Bool` is NO LONGER here: it is a real inductive family (Std.Bool, seeded
  # into every env0), so a `Bool` annotation falls through to the ordinary
  # family lookup `{:data, :Bool, [], []}` — exactly as `Nat` always has.
  defp primitive_type("Int"), do: {:int_type}
  defp primitive_type("Float"), do: {:float_type}
  defp primitive_type(_), do: nil

  # Threads the ctx to NESTED argument positions (spec §7.3 item 3): in
  # `b(first(p))` the head `b` is a bound var; the implicit-carrying global
  # `first` sits one level down, in an argument position.
  defp map_idx_to_core(exprs, scope, fam, env, ctx \\ nil) do
    Enum.reduce_while(exprs, {:ok, []}, fn e, {:ok, acc} ->
      case idx_to_core(e, scope, fam, env, ctx) do
        {:ok, core} -> {:cont, {:ok, acc ++ [core]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp declare_indexed_at_min_level(env, name, param_tele, index_tele, ctors, level) when level <= @ceiling do
    family = Inductive.family(name, param_tele, index_tele, level)
    env2 = Inductive.declare(env, family, ctors)
    family2 = Inductive.get_family(env2, name)

    with :ok <- Kernel.check_family(env2, family2),
         :ok <- check_all_ctors(env2, family2, ctors),
         :ok <- Inductive.positive?(env2, family2) do
      {:ok, env2}
    else
      {:error, :universe_level} ->
        declare_indexed_at_min_level(env, name, param_tele, index_tele, ctors, level + 1)

      {:error, _} = err ->
        err
    end
  end

  defp declare_indexed_at_min_level(_env, _name, _param_tele, _index_tele, _ctors, _level),
    do: {:error, :universe_ceiling}

  # -- constructors -----------------------------------------------------------

  defp build_ctors(variants) do
    Enum.reduce_while(variants, {:ok, []}, fn variant, {:ok, acc} ->
      case variant_to_ctor(variant) do
        {:ok, ctor} -> {:cont, {:ok, acc ++ [ctor]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # Nullary constructor: `None`
  defp variant_to_ctor({:variable, _meta, vname}),
    do: {:ok, Inductive.ctor(String.to_atom(vname), [], [])}

  # Constructor with fields: `Some(T)` / `SVCons(Sig, SVDesc)`
  defp variant_to_ctor({:function_def, meta, _body}) do
    vname = meta |> Keyword.fetch!(:name) |> String.to_atom()
    field_asts = Keyword.fetch!(meta, :params)

    case fields_to_telescope(field_asts) do
      {:ok, tele} -> {:ok, Inductive.ctor(vname, tele, [])}
      {:error, _} = err -> err
    end
  end

  defp variant_to_ctor(other), do: {:error, {:unsupported_variant, other}}

  defp fields_to_telescope(field_asts) do
    field_asts
    |> Enum.with_index()
    |> Enum.reduce_while({:ok, []}, fn {ast, i}, {:ok, acc} ->
      case type_to_core(ast) do
        {:ok, core} -> {:cont, {:ok, acc ++ [{:"f#{i}", core}]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # -- surface type expr → Core type term -------------------------------------

  defp type_to_core({:variable, _meta, "Type"}), do: {:ok, {:type, 0}}

  defp type_to_core({:variable, _meta, name}) do
    case primitive_type(name) do
      nil -> {:ok, {:data, String.to_atom(name), [], []}}
      prim -> {:ok, prim}
    end
  end

  defp type_to_core({:function_call, meta, params}) do
    cond do
      Keyword.get(meta, :function_type) ->
        {:error, {:unsupported_field_type, :function}}

      true ->
        name = meta |> Keyword.fetch!(:name) |> String.to_atom()

        with {:ok, core_params} <- map_type_to_core(params) do
          # A saturated family application becomes a `:data` with index args.
          {:ok, {:data, name, [], core_params}}
        end
    end
  end

  # A pair/Σ field type `MkW(Sigma(a: T, U))`. Field telescopes here are
  # non-dependent (each field is elaborated without the earlier fields in scope),
  # so the Σ codomain carries no reference to the bound component — `U` has no free
  # de Bruijn index and needs no shift. A genuinely dependent Σ field (`U`
  # mentioning `a`) would map `a` to a spurious family name and be rejected by
  # `Kernel.check_family`; it is not admitted here. Lowers to the builtin inductive
  # `Sigma(D, λ_:D. U)`; because `U` is closed w.r.t. the binder, the wrapping
  # lambda is trivially constant (it ignores its argument), which is still
  # well-formed. The assembled `{:data, :Sigma, …}` goes into the constructor
  # telescope and is validated by the kernel.
  defp type_to_core({:sigma_type, [binder: _bname], [dom_ast, body_ast]}) do
    with {:ok, dom} <- type_to_core(dom_ast),
         {:ok, body} <- type_to_core(body_ast) do
      {:ok, {:data, :Sigma, [dom, {:lam, dom, body}], []}}
    end
  end

  defp type_to_core(other), do: {:error, {:unsupported_field_type, other}}

  defp map_type_to_core(asts) do
    Enum.reduce_while(asts, {:ok, []}, fn ast, {:ok, acc} ->
      case type_to_core(ast) do
        {:ok, core} -> {:cont, {:ok, acc ++ [core]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # -- declaration at the least well-formed universe level --------------------

  defp declare_at_min_level(env, name, ctors, level) when level <= @ceiling do
    family = Inductive.family(name, [], [], level)
    env2 = Inductive.declare(env, family, ctors)
    family2 = Inductive.get_family(env2, name)

    with :ok <- Kernel.check_family(env2, family2),
         :ok <- check_all_ctors(env2, family2, ctors),
         :ok <- Inductive.positive?(env2, family2) do
      {:ok, env2}
    else
      {:error, :universe_level} -> declare_at_min_level(env, name, ctors, level + 1)
      {:error, _} = err -> err
    end
  end

  defp declare_at_min_level(_env, _name, _ctors, _level), do: {:error, :universe_ceiling}

  defp check_all_ctors(env, family, ctors) do
    Enum.reduce_while(ctors, :ok, fn ctor, :ok ->
      case Kernel.check_ctor(env, family, ctor) do
        :ok -> {:cont, :ok}
        err -> {:halt, err}
      end
    end)
  end
end
