defmodule Cure.Elab.Program do
  @moduledoc """
  Whole-program elaboration (design spec §5, M9.2 wiring): lex + parse a source
  string, elaborate every declaration into the `Cure.Core` signature, then run
  the type-level totality closure so that any function reduced by the type
  checker is kernel-certified total (§7). Returns the fully-elaborated,
  totality-certified signature.
  """

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.{Env, Validator}
  alias Cure.Elab.{Declarations, Erase, Resolution, TotalityClosure}
  alias Cure.Stdlib.Paths

  @spec elaborate(String.t()) :: {:ok, Env.t()} | {:error, term()}
  def elaborate(source) when is_binary(source) do
    Cure.Elab.GuardLint.reset_warnings()

    with {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      check_ast(ast)
    end
  end

  @doc """
  Elaborate + totality-certify an already-parsed module/declaration AST. Unwraps
  a `mod ... end` container to its body. This is the entry the real compiler's
  type checker calls for dependent modules.
  """
  @spec check_ast(tuple() | list()) :: {:ok, Env.t()} | {:error, term()}
  def check_ast(ast), do: check_ast(ast, [])

  @spec check_ast(tuple() | list(), keyword()) :: {:ok, Env.t()} | {:error, term()}
  def check_ast(ast, _opts) do
    with :ok <- check_no_duplicate_defs(ast),
         :ok <- check_no_duplicate_types(ast),
         :ok <- check_no_duplicate_ctors(ast) do
      check_ast_elixir_core(ast)
    end
  end

  # Each top-level module is its own namespace — it compiles to its own BEAM module
  # (`Cure.A`, `Cure.B`), so two SIBLING modules may legitimately share a type /
  # constructor / function name (the stdlib has `map` in five modules). Cross-module
  # collisions are resolved by the E-layer resolution/rekey machinery (LOCKED
  # type-shadowing Approach B), not by rejection. The duplicate checks below
  # therefore run PER MODULE: only a repeat WITHIN one module is the silent
  # `Map.put` overwrite bug. `module_decl_groups/1` returns one declaration list per
  # module (an AST with no module wrapper is a single namespace).
  defp module_decl_groups(ast) do
    case top_modules(ast) do
      [] -> [declarations(ast)]
      mods -> Enum.map(mods, &declarations/1)
    end
  end

  defp top_modules({:block, _meta, items}) when is_list(items),
    do: Enum.flat_map(items, &top_modules/1)

  defp top_modules({:container, meta, _body} = node) when is_list(meta) do
    if Keyword.get(meta, :container_type) == :module, do: [node], else: []
  end

  defp top_modules(_), do: []

  # Runs `extract` over each module's declarations independently; the first
  # within-module duplicate becomes {:error, {tag, norm.(name)}}.
  defp first_dup_per_module(ast, extract, tag, norm) do
    ast
    |> module_decl_groups()
    |> Enum.reduce_while(:ok, fn decls, :ok ->
      names = Enum.flat_map(decls, extract)

      case names -- Enum.uniq(names) do
        [] -> {:cont, :ok}
        [dup | _] -> {:halt, {:error, {tag, norm.(dup)}}}
      end
    end)
  end

  # A module must not declare the same type name twice: `env.families` is a silent
  # `Map.put`, so the second would overwrite the first.
  @spec check_no_duplicate_types(tuple() | list()) :: :ok | {:error, term()}
  defp check_no_duplicate_types(ast) do
    extract = fn
      {tag, meta, _} when tag in [:container, :indexed_type, :type_annotation] and is_list(meta) ->
        case Keyword.get(meta, :name) do
          n when is_binary(n) -> [String.to_atom(n)]
          n when is_atom(n) and not is_nil(n) -> [n]
          _ -> []
        end

      _ ->
        []
    end

    first_dup_per_module(ast, extract, :duplicate_type, & &1)
  end

  # A module must not bind the same constructor name twice — within one type
  # (`A | A`) or across two types in the same module (`env.ctor_to_family` maps each
  # ctor to ONE family, so a shared name silently loses one family, an unsound state
  # since Cure has no type-directed constructor disambiguation).
  @spec check_no_duplicate_ctors(tuple() | list()) :: :ok | {:error, term()}
  defp check_no_duplicate_ctors(ast) do
    first_dup_per_module(ast, &ctor_names/1, :duplicate_constructor, & &1)
  end

  # A module must not bind the same top-level function name twice: `Env.add_def`
  # is a silent `Map.put` overwrite, so a duplicate would let a program typecheck
  # against one body and run another. Every real dependent language rejects this.
  # Separate signatures parse as `:type_annotation` (not `:function_def`), so
  # counting `:function_def` names has no sig+body false positives.
  @spec check_no_duplicate_defs(tuple() | list()) :: :ok | {:error, term()}
  defp check_no_duplicate_defs(ast) do
    extract = fn
      {:function_def, meta, _body} ->
        case Keyword.get(meta, :name) do
          name when is_binary(name) -> [name]
          _ -> []
        end

      _ ->
        []
    end

    first_dup_per_module(ast, extract, :duplicate_definition, &String.to_atom/1)
  end

  @doc false
  @spec check_ast_elixir_core(tuple() | list()) :: {:ok, Env.t()} | {:error, term()}
  def check_ast_elixir_core(ast) do
    with {:ok, imported, _ambiguous} <- shadow_resolved_imports(ast),
         seeded = Cure.Core.Builtins.seed(Env.empty(), declared_type_names(ast)),
         env0 = merge_env(seeded, imported),
         {:ok, env} <- elaborate_declarations(declarations(ast), env0, prelude_source?(ast)),
         {:ok, certified} <- TotalityClosure.certify_type_level(env) do
      # Self-compilation of a hinted module (Std.Bool/Std.Sigma) marks its own
      # defs so their intra-module uses keep inlining; any other module name
      # is a no-op here (its hinted imports were marked slice-side).
      {:ok, mark_inline_hints(certified, find_module_name(ast))}
    end
  end

  @doc false
  @spec local_def_names(tuple() | list()) :: [atom()]
  def local_def_names(ast) do
    ast
    |> declarations()
    |> Enum.flat_map(fn
      {:function_def, meta, _body} ->
        case Keyword.get(meta, :name) do
          name when is_binary(name) -> [String.to_atom(name)]
          _ -> []
        end

      _ ->
        []
    end)
  end

  # Family/type names the module declares itself. A builtin (Bool/Nat) is NOT
  # seeded into env0 when the module declares its own same-named type — the local
  # declaration is canonical, and seeding a look-alike would pollute its ctor set.
  defp declared_type_names(ast) do
    ast
    |> declarations()
    |> Enum.flat_map(fn
      {tag, meta, _} when tag in [:container, :indexed_type, :type_annotation] and is_list(meta) ->
        case Keyword.get(meta, :name) do
          n when is_binary(n) -> [String.to_atom(n)]
          n when is_atom(n) and not is_nil(n) -> [n]
          _ -> []
        end

      _ ->
        []
    end)
    |> MapSet.new()
  end

  # Constructor names declared directly by the module. Type-name shadowing does
  # not shadow constructors; constructor-name shadowing is decided independently.
  defp declared_ctor_names(ast) do
    ast
    |> declarations()
    |> Enum.flat_map(&ctor_names/1)
    |> MapSet.new()
  end

  defp ctor_names({:container, meta, variants}) when is_list(meta) do
    case Keyword.get(meta, :container_type) do
      :enum -> Enum.flat_map(variants, &variant_ctor_names/1)
      :struct -> [meta |> Keyword.fetch!(:name) |> String.to_atom()]
      _ -> []
    end
  end

  defp ctor_names({:indexed_type, _meta, ctor_sigs}), do: Enum.flat_map(ctor_sigs, &gadt_ctor_names/1)
  defp ctor_names(_decl), do: []

  defp variant_ctor_names({:variable, _meta, name}) when is_binary(name), do: [String.to_atom(name)]
  defp variant_ctor_names({:function_def, meta, _body}), do: [meta |> Keyword.fetch!(:name) |> String.to_atom()]
  defp variant_ctor_names(_variant), do: []

  defp gadt_ctor_names({:gadt_ctor, meta, _body}) when is_list(meta),
    do: [meta |> Keyword.fetch!(:name) |> String.to_atom()]

  defp gadt_ctor_names(_sig), do: []

  # A source is a designated prelude source iff its own declared module name is
  # a key of the stdlib module registry. Only such sources may register a
  # `@builtin(:key)`; ordinary user code declaring the same decorator is ignored
  # (spec §1 single-registration invariant).
  defp prelude_source?(ast),
    do: Map.has_key?(Cure.Stdlib.Preload.module_groups(), module_atom(ast))

  # The core-prelude subset auto-loaded into EVERY module (no `use` needed). Scope
  # is bounded by what the DEPENDENT elaborator can currently import: only modules
  # that fully dependent-elaborate qualify, because `import_source_env` dependent-
  # checks each imported module. Std.Bool and Std.Nat qualify today. Excluded, why:
  #   Std.Core       -- legacy bool_not/bool_and use `pickup` (:unsupported_expression)
  #   Std.Equivalent -- uses a :cure_refl symbol literal the elaborator rejects
  #   Equatable/Ord/Show/Functor protocols -- would couple instance resolution globally
  # Each can join once ported to dependent-clean syntax (ongoing parity work). The
  # listed modules are self-excluded (they stay self-contained on the seeded
  # builtins), which also breaks any bootstrap cycle. Each source is idempotent
  # under `merge_env`, so an explicit `use` is harmless and a local definition of
  # the same name shadows the import.
  #   Std.Sigma -- the dependent-pair projection globals `sigma_first`/`sigma_second`
  #   that `.1`/`.2` lower to must resolve in EVERY module (the surface sugar is
  #   usable without `use`, like %[..]); the Sigma family itself is seeded, and
  #   Std.Sigma dependent-elaborates cleanly (D1-proven pattern), so it qualifies.
  @auto_prelude ~w(Std.Bool Std.Nat Std.Sigma)

  # The canonical type each auto-prelude module provides. If a module locally
  # declares a same-named type (e.g. its own `type Nat = Zero | Suc`), that prelude
  # is NOT auto-imported — the local declaration is canonical and importing the
  # look-alike would collide (mirrors `declared_type_names`' builtin-seed skip).
  @auto_prelude_types %{"Std.Bool" => :Bool, "Std.Nat" => :Nat, "Std.Sigma" => :Sigma}

  defp auto_prelude_imports(ast) do
    self = find_module_name(ast)
    declared = declared_type_names(ast)

    Enum.reject(@auto_prelude, fn src ->
      src == self or MapSet.member?(declared, Map.get(@auto_prelude_types, src))
    end)
  end

  @doc """
  Elaborate a module and return the definitions declared directly by that
  module. Imported stdlib definitions remain in the env for type checking and
  conversion, but codegen should emit only `local_defs`.
  """
  @spec check_ast_with_locals(tuple() | list()) :: {:ok, Env.t(), [atom()]} | {:error, term()}
  def check_ast_with_locals(ast) do
    local_defs = local_def_names(ast)

    with {:ok, env} <- check_ast(ast) do
      # `implementation` declarations synthesise mangled method globals that are
      # not in the source AST; they are still this module's locals and must be
      # emitted alongside the source-declared defs.
      {:ok, env, local_defs ++ impl_def_names(env)}
    end
  end

  @doc """
  Names of the globals synthesised by `implementation` declarations (the mangled
  per-method impl bodies + any dictionary values). Codegen must emit these as
  module locals; `Cure.Elab.Resolve` references them by name.
  """
  @spec impl_def_names(Env.t()) :: [atom()]
  def impl_def_names(env) do
    case Env.coherence(env) do
      nil ->
        []

      %{anon: anon, named: named} ->
        refs = Map.values(anon) ++ Map.values(named)

        method_defs = Enum.flat_map(refs, &Map.values(&1.methods))
        dict_defs = Enum.flat_map(refs, fn ref -> List.wrap(Map.get(ref, :dict)) end)

        Enum.uniq(method_defs ++ dict_defs)
    end
  end

  @doc """
  Does a parsed program/AST use dependent constructs the kernel must check?

  This is intentionally a surface-feature router, not a semantic checker. Forms
  that already have a trusted Core elaboration must take the dependent compiler
  path even when a module does not declare an indexed family. Legacy proof
  containers are not routed here until proof containers elaborate into Core.
  """
  @spec dependent?(term()) :: boolean()
  def dependent?({:indexed_type, _meta, _body}), do: true
  def dependent?({:sigma_type, _meta, _body}), do: true
  def dependent?({:rewrite_expr, _meta, _body}), do: true

  def dependent?({:function_call, meta, children}) when is_list(meta) do
    Keyword.get(meta, :name) in ["Equivalent", "reflexive"] or Enum.any?(children, &dependent?/1)
  end

  def dependent?({:container, meta, body}) when is_list(meta) do
    case Keyword.get(meta, :container_type) do
      :proof -> false
      _other -> dependent?(body)
    end
  end

  def dependent?({:attribute_access, meta, children}) when is_list(meta) do
    Keyword.get(meta, :attribute) in ["1", "2"] or Enum.any?(children, &dependent?/1)
  end

  def dependent?({:function_def, meta, body}) when is_list(meta) do
    dependent_params?(Keyword.get(meta, :params, [])) or
      dependent?(Keyword.get(meta, :return_type)) or
      dependent?(body)
  end

  def dependent?({:param, meta, _name}) when is_list(meta) do
    Keyword.get(meta, :implicit) == true or dependent?(Keyword.get(meta, :type))
  end

  def dependent?({_tag, _meta, children}) when is_list(children),
    do: Enum.any?(children, &dependent?/1)

  def dependent?(list) when is_list(list), do: Enum.any?(list, &dependent?/1)
  def dependent?(_other), do: false

  defp dependent_params?(params) when is_list(params), do: Enum.any?(params, &dependent?/1)
  defp dependent_params?(_other), do: false

  @doc """
  Extract the `Cure.<Name>` module atom from a parsed `mod … end` program,
  defaulting to `Cure.Main` when no module container is present.
  """
  @spec module_atom(term()) :: module()
  def module_atom(ast), do: String.to_atom("Cure." <> (find_module_name(ast) || "Main"))

  defp find_module_name({:container, meta, _body}) when is_list(meta) do
    if Keyword.get(meta, :container_type) == :module, do: Keyword.get(meta, :name)
  end

  defp find_module_name({_tag, _meta, children}) when is_list(children),
    do: Enum.find_value(children, &find_module_name/1)

  defp find_module_name(list) when is_list(list), do: Enum.find_value(list, &find_module_name/1)
  defp find_module_name(_other), do: nil

  @doc """
  Hole goal reports (design spec §10/§11): for every definition whose body still
  carries a hole, report the hole's **goal type** (the definition's return type)
  and its **local context** (the parameter types in scope). This is the
  `:hole_goal` diagnostic — a hole typechecks, reports what must fill it, and
  blocks codegen until filled.
  """
  @spec hole_goals(Env.t()) :: [%{function: atom(), goal: term(), context: [term()]}]
  def hole_goals(%Env{defs: defs}) do
    for {name, %{type: type, body: body}} <- defs, Erase.has_hole?(body) do
      {context, goal} = split_pi(type, [])
      %{function: name, goal: goal, context: context}
    end
  end

  defp split_pi({:pi, dom, cod}, acc), do: split_pi(cod, [dom | acc])
  defp split_pi(goal, acc), do: {Enum.reverse(acc), goal}

  @doc """
  Codegen gate (§6 negative #5): a program with an unfilled hole typechecks but
  must not be emitted. Returns `{:error, {:unfilled_hole, name}}` for the first
  definition that still carries a hole.
  """
  @spec check_codegen_ready(Env.t()) :: :ok | {:error, {:unfilled_hole, atom()}}
  def check_codegen_ready(%Env{defs: defs}) do
    # Route through the single Final-Core enforcement point (K3): the validator
    # descends into every node (prim args, rewrite proof/motive, eq/refl args)
    # where the hand-rolled `has_hole?` walker had gaps.
    finding =
      Enum.find_value(defs, fn {name, %{body: body}} ->
        case Validator.validate(body, Validator.release_config()) do
          {:ok, _warnings} -> nil
          {:error, rejections} ->
            if Enum.any?(rejections, &(&1.clause == :no_hole)), do: {name, rejections}
        end
      end)

    case finding do
      nil -> :ok
      {name, _rejections} -> {:error, {:unfilled_hole, name}}
    end
  end

  # Flatten a parsed program into a flat list of top-level declarations,
  # unwrapping `{:block, …}` groupings and `mod … end` module containers while
  # leaving ADT/GADT/function declarations intact. Stray sibling nodes the parser
  # can place next to a module container (e.g. a bare `{:variable, …}`) are
  # dropped, mirroring how codegen locates the container and ignores siblings.
  defp declarations({:block, _meta, items}) when is_list(items),
    do: Enum.flat_map(items, &declarations/1)

  defp declarations({:container, meta, body}) when is_list(meta) do
    if Keyword.get(meta, :container_type) == :module do
      body |> List.wrap() |> Enum.flat_map(&declarations/1)
    else
      [{:container, meta, body}]
    end
  end

  defp declarations({:function_def, meta, body}) when is_list(meta),
    do: [{:function_def, meta, body}]

  defp declarations({tag, _meta, _body} = node) when tag in [:container, :indexed_type], do: [node]

  # Compile-time typeclass declarations (Task 21). Both are top-level
  # declarations the elaborator dispatches (`interface` → descriptor,
  # `implementation` → dictionary + coherence registration).
  defp declarations({tag, meta, _body} = node) when tag in [:interface, :implementation] and is_list(meta),
    do: [node]

  # A top-level type alias `type Name = RHS` (named, non-refinement). Inline
  # refinement/annotation `:type_annotation` nodes are not declarations.
  defp declarations({:type_annotation, meta, _} = node) when is_list(meta) do
    if Keyword.has_key?(meta, :name) and not Keyword.get(meta, :refinement, false),
      do: [node],
      else: []
  end

  defp declarations(_other), do: []

  defp imports({:block, _meta, items}) when is_list(items),
    do: Enum.flat_map(items, &imports/1)

  defp imports({:container, meta, body}) when is_list(meta) do
    if Keyword.get(meta, :container_type) == :module do
      body |> List.wrap() |> Enum.flat_map(&imports/1)
    else
      []
    end
  end

  defp imports({:import, meta, _}) when is_list(meta), do: [Keyword.fetch!(meta, :source)]

  defp imports({_tag, _meta, children}) when is_list(children),
    do: Enum.flat_map(children, &imports/1)

  defp imports(list) when is_list(list), do: Enum.flat_map(list, &imports/1)
  defp imports(_other), do: []

  defp import_env([], _seen), do: {:ok, Env.empty()}

  defp import_env(imports, seen) do
    Enum.reduce_while(imports, {:ok, Env.empty()}, fn source, {:ok, acc} ->
      case source |> import_source_path() |> import_source_env(seen) do
        {:ok, imported} -> {:cont, {:ok, merge_env(acc, imported)}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # Distinct {module_id, path} for every DIRECT import source, deduped by
  # module_id. Used for the merged-slice list (§3.2 re-keying/merging operates
  # only at this granularity — nested imports are pulled in automatically by
  # each direct module's own recursive `module_slice_env`).
  defp distinct_import_modules(sources) do
    sources
    |> Enum.map(&import_source_path/1)
    |> Enum.flat_map(fn
      {:ok, module_name, path} -> [{to_string(module_name), path}]
      _ -> []
    end)
    |> Enum.uniq_by(fn {mod_id, _path} -> mod_id end)
  end

  # Every module reachable via the import graph (direct AND transitive),
  # deduped by module_id, cycle-safe (BFS with a `seen` set). Collision
  # DETECTION (family_owners, below) must scan this closure, not just the
  # direct list: a family declared in a module reached only transitively
  # (e.g. Std.Nat, pulled in solely because `priv/std/vector.cure` itself
  # does `use Std.Nat`) still needs to be attributed to its owning module, or
  # a local declaration of the same name is never classified as a collision
  # and the disowning never happens for that family.
  defp transitive_import_modules(sources), do: bfs_import_modules(sources, MapSet.new(), [])

  defp bfs_import_modules([], _seen, acc), do: Enum.reverse(acc)

  defp bfs_import_modules([source | rest], seen, acc) do
    case import_source_path(source) do
      {:ok, module_name, path} ->
        mod_id = to_string(module_name)

        if MapSet.member?(seen, mod_id) do
          bfs_import_modules(rest, seen, acc)
        else
          nested =
            with {:ok, src} <- File.read(path),
                 {:ok, tokens} <- Lexer.tokenize(src, emit_events: false),
                 {:ok, nested_ast} <- Parser.parse(tokens, emit_events: false) do
              imports(nested_ast)
            else
              _ -> []
            end

          bfs_import_modules(nested ++ rest, MapSet.put(seen, mod_id), [{mod_id, path} | acc])
        end

      _ ->
        bfs_import_modules(rest, seen, acc)
    end
  end

  # Family names DECLARED in a module's own source (transitive imports excluded).
  defp owned_family_names(path) do
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      declared_type_names(ast)
    else
      _ -> MapSet.new()
    end
  end

  # Function names DECLARED in a module's own source (transitive imports
  # excluded). Mirror of `owned_family_names/1`, reusing the public
  # `local_def_names/1` scanner in place of `declared_type_names/1`.
  defp owned_def_names(path) do
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      MapSet.new(local_def_names(ast))
    else
      _ -> MapSet.new()
    end
  end

  # Build ONE module's flat env slice (own decls + its own imports), as today.
  defp module_slice_env(path) do
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false),
         {:ok, imported} <- import_env(imports(ast), MapSet.new()),
         seeded = Cure.Core.Builtins.seed(Env.empty(), declared_type_names(ast)),
         env0 = merge_env(seeded, imported),
         {:ok, env} <- elaborate_declarations(declarations(ast), env0, prelude_source?(ast)),
         {:ok, certified} <- TotalityClosure.certify_type_level(env) do
      {:ok, mark_inline_hints(certified, find_module_name(ast))}
    end
  end

  # Delete residual bare keys for a colliding family name left by transitive copies.
  defp drop_bare_family(%Env{} = env, name) do
    ctors = for {c, f} <- env.ctor_to_family, f == name, into: [], do: c

    %Env{
      env
      | families: Map.delete(env.families, name),
        ctors: Map.drop(env.ctors, ctors),
        ctor_to_family: Map.drop(env.ctor_to_family, [name | ctors]),
        builtins:
          env.builtins
          |> Enum.reject(fn {_key, fid} -> fid == name end)
          |> Map.new()
    }
  end

  # The full shadow-aware imported-env builder.
  defp shadow_resolved_imports(ast) do
    sources = auto_prelude_imports(ast) ++ imports(ast)
    modules = distinct_import_modules(sources)

    # Ownership scans the FULL transitive closure (not `modules`, which is
    # direct-only) — see the Design note + `transitive_import_modules/1` doc.
    # Family AND def ownership in ONE transitive walk (avoid re-walking): both are
    # `%{name => MapSet.t(owner_mod)}` maps fed to the shape-generic `classify/2`.
    {family_owners, def_owners} =
      sources
      |> transitive_import_modules()
      |> Enum.reduce({%{}, %{}}, fn {mod_id, path}, {fam_acc, def_acc} ->
        fam_acc =
          Enum.reduce(owned_family_names(path), fam_acc, fn name, a ->
            Map.update(a, name, MapSet.new([mod_id]), &MapSet.put(&1, mod_id))
          end)

        def_acc =
          Enum.reduce(owned_def_names(path), def_acc, fn name, a ->
            Map.update(a, name, MapSet.new([mod_id]), &MapSet.put(&1, mod_id))
          end)

        {fam_acc, def_acc}
      end)

    local = declared_type_names(ast)
    local_ctors = declared_ctor_names(ast)
    local_defs = MapSet.new(local_def_names(ast))
    %{losers: losers, ambiguous: ambiguous} = Resolution.classify(family_owners, local)
    # Def ambiguity (no local winner) is enforced at resolution time (Task 3 via
    # `ambiguous_modules/2`); here we only need the losers to re-key their keys.
    %{losers: def_losers} = Resolution.classify(def_owners, local_defs)

    collisions =
      losers |> Map.values() |> Enum.reduce(MapSet.new(), &MapSet.union/2)

    with {:ok, merged} <-
           Enum.reduce_while(modules, {:ok, Env.empty()}, fn {mod_id, path}, {:ok, acc} ->
             case module_slice_env(path) do
               {:ok, slice} ->
                 reachable =
                   [mod_id]
                   |> transitive_import_modules()
                   |> Enum.map(fn {owner, _path} -> owner end)
                   |> MapSet.new()

                 owner_mods =
                   MapSet.union(MapSet.new(Map.keys(losers)), MapSet.new(Map.keys(def_losers)))

                 slice =
                   Enum.reduce(owner_mods, slice, fn owner_mod, s ->
                     if MapSet.member?(reachable, owner_mod) do
                       Resolution.rekey_module_env(
                         s,
                         owner_mod,
                         Map.get(losers, owner_mod, MapSet.new()),
                         local_ctors,
                         Map.get(def_losers, owner_mod, MapSet.new())
                       )
                     else
                       s
                     end
                   end)

                 {:cont, {:ok, merge_env(acc, slice)}}

               {:error, _} = err ->
                 {:halt, err}
             end
           end) do
      # Drop residual bare copies of every collision name (transitive leftovers)
      # plus local family names supplied only by imported slices as seeded helper
      # builtins. Real imported owners have already been re-keyed above, preserving
      # their non-shadowed constructors under their own family id.
      cleaned =
        collisions
        |> MapSet.union(local)
        |> Enum.reduce(merged, fn name, e -> drop_bare_family(e, name) end)

      {:ok, cleaned, ambiguous}
    end
  end

  defp import_source_env(:not_stdlib, _seen), do: {:ok, Env.empty()}

  defp import_source_env({:ok, module_name, path}, seen) do
    if MapSet.member?(seen, module_name) do
      {:ok, Env.empty()}
    else
      with {:ok, source} <- File.read(path),
           {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
           {:ok, ast} <- Parser.parse(tokens, emit_events: false),
           {:ok, env0} <- import_env(imports(ast), MapSet.put(seen, module_name)),
           {:ok, env} <- elaborate_declarations(declarations(ast), env0) do
        with {:ok, certified} <- TotalityClosure.certify_type_level(env) do
          {:ok, mark_inline_hints(certified, module_name)}
        end
      else
        {:error, reason} -> {:error, {:dependent_import_failed, module_name, reason}}
      end
    end
  end

  # Emit-inline markers for the prelude defs whose saturated applications lower
  # to native BEAM forms (connectives → boolean ops, Sigma projections →
  # element/2). Set HERE, on the import path keyed by source module identity —
  # never by bare global atom — so a local def shadowing `eq`/`sigma_first`/…
  # owns an unmarked record and is emitted as an ordinary call (R1 discipline;
  # see `Env.register_inline_hint/3`).
  @inline_hints %{
    "Std.Bool" => [and: :and, or: :or, not: :not, eq: :eq, ne: :ne],
    "Std.Sigma" => [sigma_first: :sigma_first, sigma_second: :sigma_second]
  }

  defp mark_inline_hints(env, module_name) do
    case Map.get(@inline_hints, module_name) do
      nil ->
        env

      hints ->
        # Skip a hinted name the module doesn't actually define (a user module
        # merely NAMED Std.Bool must not crash marking).
        Enum.reduce(hints, env, fn {name, key}, e ->
          if Env.get_def(e, name), do: Env.register_inline_hint(e, name, key), else: e
        end)
    end
  end

  defp import_source_path(source) do
    case String.split(source, ".") do
      ["Std", name] ->
        case Paths.source_dir() do
          nil ->
            {:error, {:missing_stdlib_source_dir, source}}

          dir ->
            path = Path.join(dir, String.downcase(name) <> ".cure")

            if File.exists?(path) do
              {:ok, source, path}
            else
              {:error, {:missing_stdlib_source, source, path}}
            end
        end

      _ ->
        :not_stdlib
    end
  end

  defp merge_env(%Env{} = left, %Env{} = right) do
    %Env{
      families: Map.merge(left.families, right.families),
      ctors: Map.merge(left.ctors, right.ctors),
      ctor_to_family: Map.merge(left.ctor_to_family, right.ctor_to_family),
      defs: Map.merge(left.defs, right.defs),
      certified: MapSet.union(left.certified || MapSet.new(), right.certified || MapSet.new()),
      builtins: Map.merge(left.builtins, right.builtins),
      primitives: Map.merge(left.primitives, right.primitives)
    }
  end

  # Two passes so that forward references and mutual recursion resolve: first
  # every type/record is elaborated and every function *signature* is registered;
  # then every function *body* is elaborated against the fully-populated
  # environment. Non-function declarations are elaborated in source order in pass
  # one (a function signature may reference any type declared before it).
  defp elaborate_declarations(items, env, prelude? \\ false) do
    with {:ok, env1, fn_decls} <- register_pass(items, env, prelude?) do
      body_pass(fn_decls, env1)
    end
  end

  defp register_pass(items, env, prelude?) do
    Enum.reduce_while(items, {:ok, env, []}, fn decl, {:ok, acc, fns} ->
      case decl do
        {:function_def, _meta, _body} ->
          case Declarations.register_signature(decl, acc) do
            {:ok, acc2} -> {:cont, {:ok, acc2, fns ++ [decl]}}
            {:error, _} = err -> {:halt, err}
          end

        # An implementation lowers each method to a mangled global; register its
        # signatures + the coherence entry now, and thread the mangled defs into
        # `fns` so their bodies elaborate in the second pass like any function.
        {:implementation, _meta, _body} ->
          case Cure.Elab.Implementation.register(decl, acc) do
            {:ok, acc2, mangled_fns} -> {:cont, {:ok, acc2, fns ++ mangled_fns}}
            {:error, _} = err -> {:halt, err}
          end

        # A `type … deriving Iface` container elaborates normally, then each named
        # interface is derived structurally: `Cure.Elab.Deriving` synthesises an
        # implementation whose mangled method bodies join `fns` for the second
        # pass, exactly like a hand-written instance.
        {:container, meta, _body} = decl when is_list(meta) ->
          with {:ok, acc2} <- Declarations.elaborate(decl, acc),
               {:ok, acc3} <- maybe_register_builtin(decl, acc2, prelude?),
               {:ok, acc4, derived_fns} <-
                 register_derived(Keyword.get(meta, :deriving, []), decl, acc3) do
            {:cont, {:ok, acc4, fns ++ derived_fns}}
          else
            {:error, _} = err -> {:halt, err}
          end

        _ ->
          case Declarations.elaborate(decl, acc) do
            {:ok, acc2} ->
              # `maybe_register_builtin` is total ({:ok, _} always), so there is no
              # error branch to thread here.
              case maybe_register_builtin(decl, acc2, prelude?) do
                {:ok, acc3} -> {:cont, {:ok, acc3, fns}}
              end

            {:error, _} = err ->
              {:halt, err}
          end
      end
    end)
    |> case do
      {:ok, _env, _fns} = ok -> ok
      {:error, _} = err -> err
    end
  end

  # In a designated prelude source, a `@builtin(:key) type Name = ...` container
  # registers the canonical builtin family (schema-validated). Non-prelude
  # sources (or non-`@builtin` decls) pass through unchanged.
  #
  # A `@builtin(:tag) primitive Name` container is NOT an inductive family: its
  # marker is consumed by Declarations.elaborate's :primitive path (which binds
  # the floor), so it must skip the inductive-family schema validation here.
  defp maybe_register_builtin({:container, meta, _body}, env, true) do
    if Keyword.get(meta, :container_type) == :primitive do
      {:ok, env}
    else
      register_builtin_from_meta(meta, env)
    end
  end

  # A `@builtin(:key) type Name indices (...)` GADT family (e.g. Bounded)
  # elaborates to an {:indexed_type} rather than a {:container}; register it
  # identically off its :decorator meta.
  defp maybe_register_builtin({:indexed_type, meta, _ctors}, env, true),
    do: register_builtin_from_meta(meta, env)

  defp maybe_register_builtin(_decl, env, _prelude?), do: {:ok, env}

  # Derive an instance of each named interface for a `deriving` container. Each
  # generated implementation is registered like a hand-written one; its mangled
  # method defs are threaded back so the second pass elaborates their bodies.
  defp register_derived([], _decl, env), do: {:ok, env, []}

  defp register_derived(names, decl, env) do
    Enum.reduce_while(names, {:ok, env, []}, fn name, {:ok, acc, fns} ->
      iface = String.to_atom(name)

      with {:ok, impl_ast} <- Cure.Elab.Deriving.generate(iface, decl, acc),
           {:ok, acc2, mangled_fns} <- Cure.Elab.Implementation.register(impl_ast, acc) do
        {:cont, {:ok, acc2, fns ++ mangled_fns}}
      else
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp register_builtin_from_meta(meta, env) do
    case Keyword.get(meta, :decorator) do
      {:builtin, args} ->
        key = builtin_key(args)
        fid = meta |> Keyword.fetch!(:name) |> String.to_atom()
        :ok = Cure.Core.Builtins.validate!(env, key, fid)
        {:ok, Cure.Core.Inductive.register_builtin(env, key, fid)}

      _ ->
        {:ok, env}
    end
  end

  defp builtin_key([{:literal, _meta, key}]) when is_atom(key), do: key
  defp builtin_key([key]) when is_atom(key), do: key

  defp body_pass(fn_decls, env) do
    Enum.reduce_while(fn_decls, {:ok, env}, fn decl, {:ok, acc} ->
      case Declarations.elaborate_function_body(decl, acc) do
        {:ok, acc2} -> {:cont, {:ok, acc2}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end
end
