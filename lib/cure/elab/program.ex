defmodule Cure.Elab.Program do
  @moduledoc """
  Whole-program elaboration (design spec §5, M9.2 wiring): lex + parse a source
  string, elaborate every declaration into the `Cure.Core` signature, then run
  the type-level totality closure so that any function reduced by the type
  checker is kernel-certified total (§7). Returns the fully-elaborated,
  totality-certified signature.
  """

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.{Env, Inductive, Validator}
  alias Cure.Elab.{Coherence, Declarations, Erase, Resolution, TotalityClosure}
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
    with :ok <- check_declarations(ast) do
      check_ast_elixir_core(ast)
    end
  end

  # The declaration-level guards, in one place. `check_ast/2` runs them for the entry module;
  # `module_slice_env/1` and `import_source_env/2` run them for every module reached through a
  # `use` import. Those two paths used to call `elaborate_declarations/3` straight from the
  # parsed AST with no guards at all, so a duplicate inside a `Std.*` source was silently kept
  # last-wins — the exact `Map.put`-overwrite hole these checks exist to close, reachable
  # through two doors they never covered.
  @spec check_declarations(tuple() | list()) :: :ok | {:error, term()}
  defp check_declarations(ast) do
    with :ok <- check_no_duplicate_defs(ast),
         :ok <- check_no_duplicate_types(ast),
         :ok <- check_no_duplicate_ctors(ast),
         :ok <- check_no_fn_ctor_collision(ast),
         :ok <- check_proof_shapes(ast) do
      check_no_sibling_collision(ast)
    end
  end

  # A top-level container the dependent pipeline elaborates as a module. Classic
  # codegen compiles a `proof` container "exactly like a regular module"; the
  # dependent pipeline now does the same, so both container types are unwrapped
  # and their declarations elaborated identically.
  defp module_like_container?(meta), do: Keyword.get(meta, :container_type) in [:module, :proof]

  # E026 proof-shape discipline: every binding inside a `proof` container must
  # inhabit a propositional-equality type (`Equivalent(T, a, b)`) — proof
  # containers are exclusively for propositions, not ordinary code. A non-proof
  # return type is rejected here, before elaboration.
  defp check_proof_shapes(ast) do
    ast
    |> proof_container_fns()
    |> Enum.find_value(:ok, fn {:function_def, meta, _body} ->
      if proof_shape_return?(Keyword.get(meta, :return_type)) do
        nil
      else
        name = Keyword.get(meta, :name)

        {:error,
         {:proof_shape_mismatch,
          "E026: binding '#{name}' in a proof container must inhabit a " <>
            "propositional-equality type Equivalent(T, a, b)", name}}
      end
    end)
  end

  defp proof_container_fns({:block, _meta, items}) when is_list(items),
    do: Enum.flat_map(items, &proof_container_fns/1)

  defp proof_container_fns({:container, meta, body}) when is_list(meta) do
    if Keyword.get(meta, :container_type) == :proof do
      body |> List.wrap() |> Enum.filter(&match?({:function_def, m, _} when is_list(m), &1))
    else
      []
    end
  end

  defp proof_container_fns(_other), do: []

  # A proof return type is an application of the propositional-equality family.
  defp proof_shape_return?({:function_call, meta, _args}) when is_list(meta),
    do: Keyword.get(meta, :name) in ["Equivalent", "Eq"]

  defp proof_shape_return?(_other), do: false

  # Two sibling `mod` blocks in ONE compilation unit may not bind the same name.
  #
  # A module is a namespace, and two modules in two FILES may share a name freely: the stdlib
  # has `map` in five modules. Those are reconciled by the import rekey machinery
  # (`Resolution.rekey_module_env`, LOCKED type-shadowing Approach B), which this check does
  # not touch. But `declarations/1` flattens all SIBLING modules of one AST into a single list
  # before `elaborate_declarations/3` ever runs, and nothing rekeys them — they share one flat
  # `env.defs` / `env.families` / `env.ctor_to_family`, each a plain `Map.put`. So the later
  # sibling silently wins the bare key:
  #
  #     mod A  fn foo() -> Int = 1  end
  #     mod B  fn foo() -> Int = 2  end   # A's `foo` is GONE; A's callers δ-unfold B's body
  #
  # For types it is worse than lost — it is incoherent. `type Foo = MkA` / `type Foo = MkB`
  # leaves `MkA` registered as a constructor whose `ctor_to_family` entry names a family whose
  # constructor set contains only `MkB`. That is precisely the state `check_no_duplicate_ctors`
  # rejects within one module.
  #
  # Rejecting is the sound reading. Rekeying siblings the way imports are rekeyed would require
  # elaborating each sibling into its own slice, which would break the bare cross-sibling
  # references that flat elaboration makes work today (`mod B  fn baz() = bar()  end`, calling
  # A's `bar`). Nothing in the tree declares sibling modules in one file, so nothing loses.
  @spec check_no_sibling_collision(tuple() | list()) :: :ok | {:error, term()}
  defp check_no_sibling_collision(ast) do
    case top_modules(ast) do
      mods when length(mods) < 2 ->
        :ok

      mods ->
        # `fn` names and constructor names share one bare-atom namespace, so they collide with
        # each other across siblings exactly as `check_no_fn_ctor_collision` says they do
        # within one. Type names live in `env.families`, their own namespace.
        with :ok <- first_sibling_collision(mods, &value_names/1),
             do: first_sibling_collision(mods, &type_names/1)
    end
  end

  defp first_sibling_collision(mods, extract) do
    mods
    |> Enum.flat_map(fn mod ->
      owner = module_name_atom(mod)
      for name <- mod |> declarations() |> Enum.flat_map(extract) |> Enum.uniq(), do: {name, owner}
    end)
    |> Enum.group_by(&elem(&1, 0), &elem(&1, 1))
    |> Enum.find(fn {_name, owners} -> length(owners) > 1 end)
    |> case do
      nil -> :ok
      {name, owners} -> {:error, {:sibling_module_collision, name, Enum.sort(owners)}}
    end
  end

  defp value_names(decl), do: fn_names(decl) ++ ctor_names(decl)

  defp fn_names({:function_def, meta, _body}) when is_list(meta) do
    case Keyword.get(meta, :name) do
      name when is_binary(name) -> [String.to_atom(name)]
      _ -> []
    end
  end

  defp fn_names(_decl), do: []

  defp module_name_atom({:container, meta, _body}) when is_list(meta) do
    case Keyword.get(meta, :name) do
      n when is_binary(n) -> String.to_atom(n)
      n when is_atom(n) -> n
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
    if module_like_container?(meta), do: [node], else: []
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
    first_dup_per_module(ast, &type_names/1, :duplicate_type, & &1)
  end

  # Type names a declaration binds. `:interface` belongs here: `Cure.Elab.Interface`
  # declares the interface's DICTIONARY as a record family of the same name, through the
  # same `Inductive.declare/3` (a bare `Map.put`) that `type`/`indexed type`/`rec` use.
  # Omitting it let `interface Equatable(a)` and a sibling `type Equatable = Foo | Bar`
  # both register a family named `:Equatable`: whichever elaborated second won the slot,
  # and `env.ctor_to_family` kept a dangling entry for the loser's constructor.
  defp type_names({tag, meta, _})
       when tag in [:container, :indexed_type, :type_annotation, :interface] and is_list(meta) do
    case Keyword.get(meta, :name) do
      n when is_binary(n) -> [String.to_atom(n)]
      n when is_atom(n) and not is_nil(n) -> [n]
      _ -> []
    end
  end

  defp type_names(_decl), do: []

  # A module must not bind the same constructor name twice — within one type
  # (`A | A`) or across two types in the same module (`env.ctor_to_family` maps each
  # ctor to ONE family, so a shared name silently loses one family, an unsound state
  # since Cure has no type-directed constructor disambiguation).
  @spec check_no_duplicate_ctors(tuple() | list()) :: :ok | {:error, term()}
  defp check_no_duplicate_ctors(ast) do
    first_dup_per_module(ast, &ctor_names/1, :duplicate_constructor, & &1)
  end

  # A module must not bind one name as BOTH a constructor and a top-level function.
  # `type Foo = C` and `fn C() -> Int` both bind `C` in the same namespace; whichever
  # `Resolution` favours, the other is silently unreachable by name. Cure has no
  # type-directed disambiguation, so this must be a compile error rather than a coin
  # flip. Scoped per module, like the other duplicate checks.
  @spec check_no_fn_ctor_collision(tuple() | list()) :: :ok | {:error, term()}
  defp check_no_fn_ctor_collision(ast) do
    ast
    |> module_decl_groups()
    |> Enum.reduce_while(:ok, fn decls, :ok ->
      ctors = decls |> Enum.flat_map(&ctor_names/1) |> MapSet.new()

      decls
      |> Enum.flat_map(fn
        {:function_def, meta, _body} ->
          case Keyword.get(meta, :name) do
            name when is_binary(name) -> [String.to_atom(name)]
            _ -> []
          end

        _ ->
          []
      end)
      |> Enum.find(&MapSet.member?(ctors, &1))
      |> case do
        nil -> {:cont, :ok}
        clash -> {:halt, {:error, {:constructor_function_collision, clash}}}
      end
    end)
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
         {:ok, prelude} <- prelude_slice_env(ast),
         seeded = seed_with_telescope_support(ast),
         {:ok, base} <- merge_env(seeded, prelude),
         {:ok, env0} <- merge_env(base, imported),
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

  # The seeded base env plus telescope support. `Unit` (the empty telescope `%[]`
  # / `Tuple()`, the terminator of the unit-terminated Σ chain a flat `Tuple(…)`
  # unfolds to — spec 2026-07-09-unified-tuple §3.4) is declared here in the
  # E-LAYER via the ordinary `Inductive.declare/3` that `type`/`rec` use, NOT in
  # the trusted `Core.Builtins` seed: it needs no `@builtin` schema and carries no
  # kernel-judgement change, so it stays out of the TCB. A module declaring its own
  # `Unit` shadows this (the local declaration overwrites the same key), same as any
  # seeded builtin. `unit : Unit` is a plain nullary inductive.
  defp seed_with_telescope_support(ast) do
    seeded = Cure.Core.Builtins.seed(Env.empty(), declared_type_names(ast))

    if MapSet.member?(declared_type_names(ast), :Unit) do
      seeded
    else
      Inductive.declare(
        seeded,
        Inductive.family(:Unit, [], [], 0),
        [Inductive.ctor(:unit, [], [])]
      )
    end
  end

  # Family/type names the module declares itself. A builtin (Bool/Nat) is NOT
  # seeded into env0 when the module declares its own same-named type — the local
  # declaration is canonical, and seeding a look-alike would pollute its ctor set.
  defp declared_type_names(ast) do
    ast
    |> declarations()
    |> Enum.flat_map(&type_names/1)
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

  # `type X = Y` with a single bare RHS is either a one-constructor enum (`type Unit =
  # MkUnit`) or an alias (`type MyNat = Nat`), decided by whether `Y` names a type — a
  # question this AST-level scan cannot answer. The parser tags both `variant: true`.
  # Counting `Y` as a constructor over-approximates: it also names the alias's target.
  # That is the safe direction (the checks it feeds reject ambiguity), and it only bites
  # a module that aliases a type AND declares a function with that type's exact,
  # capitalized name.
  defp ctor_names({:type_annotation, _meta, [{_tag, rmeta, _} = rhs]}) when is_list(rmeta) do
    if Keyword.get(rmeta, :variant, false), do: variant_ctor_names(rhs), else: []
  end

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
  #   Std.Bounded -- `Char = Bounded(0x110000)`, so the `:bounded` family must
  #   resolve in EVERY module for a char/string LITERAL (`'a'`, "hi") to elaborate
  #   (`char_type_value` looks up `:bounded`); string literals are core surface
  #   sugar, exactly like %[..]. Std.Bounded is tiny + dependent-clean, so it
  #   qualifies. (Not seeded — auto-import avoids colliding with its own decl.)
  @auto_prelude ~w(Std.Bool Std.Nat Std.Sigma Std.Int Std.Float Std.Binary Std.Bounded)

  # The canonical type each auto-prelude module provides. If a module locally
  # declares a same-named type (e.g. its own `type Nat = Zero | Suc`), that prelude
  # is NOT auto-imported — the local declaration is canonical and importing the
  # look-alike would collide (mirrors `declared_type_names`' builtin-seed skip).
  @auto_prelude_types %{
    "Std.Bool" => :Bool,
    "Std.Nat" => :Nat,
    "Std.Sigma" => :Sigma,
    "Std.Int" => :Int,
    "Std.Float" => :Float,
    "Std.Binary" => :Binary,
    "Std.Bounded" => :Bounded
  }

  defp auto_prelude_imports(ast) do
    self = find_module_name(ast)
    declared = declared_type_names(ast)

    Enum.reject(@auto_prelude, fn src ->
      src == self or MapSet.member?(declared, Map.get(@auto_prelude_types, src))
    end)
  end

  # ── `@prelude` decorator ───────────────────────────────────────────────────
  #
  # A stdlib item marked `@prelude` (see `lib/std/string.cure`'s `String` alias)
  # joins the IMPLICIT prelude: its name resolves in every module with no `use`.
  # Unlike the hard-coded `@auto_prelude` whitelist (whole modules), `@prelude` is
  # declared at the DEFINITION site and is item-granular — preluding `type String`
  # brings the alias without dragging `Std.String`'s whole function surface (which
  # would shadow user `length`/`reverse`/…). Discovery scans the stdlib sources for
  # the marker; the resulting slice is merged UNDER the explicit imports (so a
  # `use` still wins) and under the module's own declarations.
  defp prelude_slice_env(ast) do
    self = find_module_name(ast)
    local = declared_names(ast)

    prelude_manifest()
    |> Enum.reject(fn entry -> entry.source == self end)
    |> Enum.reduce_while({:ok, Env.empty()}, fn entry, {:ok, acc} ->
      case prelude_entry_env(entry, local) do
        {:ok, slice} ->
          case merge_env(acc, slice) do
            {:ok, merged} -> {:cont, {:ok, merged}}
            {:error, _} = err -> {:halt, err}
          end

        {:error, _} = err ->
          {:halt, err}
      end
    end)
  end

  # Elaborate one prelude-contributing module and restrict its env to the
  # `@prelude`-marked names (minus any the importer declares locally — a local
  # decl shadows the prelude). A whole-module `@prelude` keeps everything.
  defp prelude_entry_env(%{source: source, path: path, names: names}, local) do
    with {:ok, full} <- import_source_env({:ok, source, path}, MapSet.new()) do
      keep =
        case names do
          :all -> :all
          set -> MapSet.difference(set, local)
        end

      {:ok, restrict_env_to(full, keep)}
    end
  end

  # Keep only the named defs/families/constructors from an elaborated env. List /
  # Char and the other seeded builtins stay ambient via the base seed, so a
  # type-alias slice (`String := List(Char)`) needs only its def entry; a
  # `@prelude type` also keeps its family and constructors. `certified` is kept
  # whole — it is a totality whitelist, so a superset is harmless.
  defp restrict_env_to(%Env{}, :all = _keep), do: raise("whole-module @prelude unimplemented")

  defp restrict_env_to(%Env{} = env, %MapSet{} = names) do
    name_list = MapSet.to_list(names)
    fam_names = Enum.filter(name_list, &Map.has_key?(env.families, &1))
    kept_ctors = for {c, f} <- env.ctor_to_family, f in fam_names, into: %{}, do: {c, f}

    %Env{
      Env.empty()
      | defs: Map.take(env.defs, name_list ++ Map.keys(kept_ctors)),
        families: Map.take(env.families, fam_names),
        ctors: Map.take(env.ctors, Map.keys(kept_ctors)),
        ctor_to_family: kept_ctors,
        primitives: Map.take(env.primitives, name_list),
        certified: env.certified
    }
  end

  # `@prelude`-marked items across the stdlib tree, as a list of
  # `%{source, path, names}` (names = a `MapSet` of item names, or `:all` for a
  # whole-module mark). Discovered by scanning the stdlib sources for the marker —
  # membership lives at the definition site, not in a hand-kept list. Cached in
  # `:persistent_term`: the stdlib is fixed for a compiler build, and this runs
  # only in the HOST compiler, never on AtomVM (where `persistent_term` is absent).
  defp prelude_manifest do
    case Paths.source_dir() do
      nil ->
        []

      dir ->
        key = {__MODULE__, :prelude_manifest, dir}

        case :persistent_term.get(key, :miss) do
          :miss ->
            manifest = scan_prelude_manifest(dir)
            :persistent_term.put(key, manifest)
            manifest

          cached ->
            cached
        end
    end
  end

  defp scan_prelude_manifest(dir) do
    dir
    |> Path.join("*.cure")
    |> Path.wildcard()
    |> Enum.flat_map(fn path ->
      with {:ok, src} <- File.read(path),
           {:ok, tokens} <- Lexer.tokenize(src, emit_events: false),
           {:ok, ast} <- Parser.parse(tokens, emit_events: false),
           source when is_binary(source) <- find_module_name(ast),
           names when names != [] <- prelude_marked_names(ast) do
        [%{source: source, path: path, names: MapSet.new(names)}]
      else
        _ -> []
      end
    end)
  end

  # The names of `@prelude`-marked declarations in a module's AST. A `typealias`
  # (`{:type_annotation}`), `fn` (`{:function_def}`), and enum/indexed `type`
  # container all carry the decorator in their meta once the parser attached it.
  defp prelude_marked_names(ast) do
    ast
    |> declarations()
    |> Enum.flat_map(fn decl ->
      if prelude_decorated?(decl), do: List.wrap(declaration_name(decl)), else: []
    end)
  end

  defp prelude_decorated?({_tag, meta, _}) when is_list(meta),
    do: match?({:prelude, _}, Keyword.get(meta, :decorator))

  defp prelude_decorated?(_), do: false

  defp declaration_name({:type_annotation, meta, _}) when is_list(meta),
    do: meta |> Keyword.get(:name) |> to_name_atom()

  defp declaration_name({:function_def, meta, _}) when is_list(meta),
    do: meta |> Keyword.get(:name) |> to_name_atom()

  defp declaration_name({:container, meta, _}) when is_list(meta),
    do: meta |> Keyword.get(:name) |> to_name_atom()

  defp declaration_name({:indexed_type, meta, _}) when is_list(meta),
    do: meta |> Keyword.get(:name) |> to_name_atom()

  defp declaration_name(_), do: nil

  defp to_name_atom(name) when is_binary(name), do: String.to_atom(name)
  defp to_name_atom(_), do: nil

  # Every function/type/constructor NAME a module declares locally, as a MapSet —
  # used so a `@prelude` item is not imported into a module that redefines the same
  # name (the local declaration is canonical). Reuses the existing scanners.
  defp declared_names(ast) do
    MapSet.new(local_def_names(ast))
    |> MapSet.union(declared_type_names(ast))
    |> MapSet.union(declared_ctor_names(ast))
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
  Map each `use`-imported function name to the BEAM module atom that DEFINES it,
  so dependent codegen can emit a REMOTE call for a cross-module reference rather
  than an (undefined) local one. Built from the module's transitive import
  closure (direct `use` + the auto-prelude), keyed by bare function name to the
  `Cure.<Module>` atom that owns it; the first owner in import-BFS order wins.
  This module's OWN local definitions are dropped from the map — a local
  definition shadows an imported one, so a call to a locally-defined name stays
  local. `Cure.Elab.Emit` consults this to route `{:global, name}` references
  (the #18 dependent-only codegen enabler). A self-contained module (no
  cross-module calls) yields an empty map and the old all-local behaviour.
  """
  @spec import_origins(tuple() | list()) :: %{atom() => module()}
  def import_origins(ast) do
    local = MapSet.new(local_def_names(ast))
    sources = imports(ast) ++ auto_prelude_imports(ast)

    transitive_import_modules(sources)
    |> Enum.reduce(%{}, fn {mod_id, path}, acc ->
      module = String.to_atom("Cure." <> mod_id)
      Enum.reduce(owned_def_names(path), acc, &Map.put_new(&2, &1, module))
    end)
    |> Map.drop(MapSet.to_list(local))
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
  The transitive closure of local defs reachable from `roots` via `{:global, _}`
  references in def bodies+types.

  Emit lowers a `{:global, name}` to a *local* call within the emitted module, so
  a self-contained module must co-emit every reachable callee — a cross-module
  polymorphic call (e.g. an imported instance body delegating to `Std.List#map`)
  pulls the callee in transitively. Builtin-op defs (body-less; saturated uses
  inline to BEAM operators) are excluded — they never need a function form.
  """
  @spec reachable_def_names(Env.t(), [atom()]) :: [atom()]
  def reachable_def_names(%Env{defs: defs} = env, roots) do
    Enum.reduce(roots, MapSet.new(), fn root, seen ->
      collect_reachable(env, defs, root, seen)
    end)
    |> MapSet.to_list()
  end

  defp collect_reachable(env, defs, name, seen) do
    cond do
      MapSet.member?(seen, name) ->
        seen

      match?(%{builtin_op: op} when not is_nil(op), Map.get(defs, name)) ->
        # Body-less builtin op: reachable but never emitted as a function form.
        seen

      match?(%{type: {:type, _}}, Map.get(defs, name)) ->
        # A TYPE-LEVEL def (a type alias like `Char = Bounded(…)`, whose type is
        # `Type`) is referenced from a value body only in a type position (a
        # lambda domain) and is never emitted as a runtime function — skip it and
        # its type-level references entirely.
        seen

      true ->
        case Map.get(defs, name) do
          nil ->
            seen

          d ->
            seen = MapSet.put(seen, name)

            [d.type, d.body]
            |> Enum.flat_map(&global_refs/1)
            |> Enum.reduce(seen, &collect_reachable(env, defs, &1, &2))
        end
    end
  end

  # Every `{:global, name}` atom referenced anywhere in a Core term.
  defp global_refs({:global, name}), do: [name]
  defp global_refs({:data, _n, ps, is}), do: Enum.flat_map(ps ++ is, &global_refs/1)
  defp global_refs({:ctor, _n, args}), do: Enum.flat_map(args, &global_refs/1)

  defp global_refs({:case, s, mo, brs}),
    do: global_refs(s) ++ global_refs(mo) ++ Enum.flat_map(brs, fn {_c, _a, b} -> global_refs(b) end)

  defp global_refs({:pi, _g, dom, cod}), do: global_refs(dom) ++ global_refs(cod)
  defp global_refs({:lam, _g, dom, body}), do: global_refs(dom) ++ global_refs(body)
  defp global_refs({:app, f, a}), do: global_refs(f) ++ global_refs(a)

  # The `:let` binder is the seventh Core former. Without this clause it fell
  # through to the catch-all below, and every global referenced only inside a
  # `let` vanished from `reachable_def_names/2` — co-emitting such a closure
  # produced a module that called a function it never defined.
  defp global_refs({:let, _g, ty, val, body}),
    do: global_refs(ty) ++ global_refs(val) ++ global_refs(body)

  defp global_refs(_leaf), do: []

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

  # An anonymous union (`Int | String`) and its elimination form (`n: Int -> …`) are
  # DEPENDENT-pipeline constructs: they elaborate to a generated inductive family whose
  # constructors carry the member tag.
  #
  # Without these two clauses a module using only unions is judged non-dependent and
  # compiled by the CLASSIC pipeline, where `Type.resolve/1` maps the union to `:any`
  # and the value is emitted UNTAGGED — silently giving the erasure the design
  # explicitly rejected as unsound (`String` is `List(Char)`, so members are not
  # runtime-distinguishable). The feature would type-check correctly and then never be
  # used at codegen.
  def dependent?({:union_type, _meta, _members}), do: true
  def dependent?({:typed_pattern, _meta, _children}), do: true

  # The generic fallback below only recurses into a node's CHILDREN, never its
  # META — which is why `:param`'s type needed its own dedicated clause further
  # down. A union can ALSO appear in two other meta-only positions:
  #
  #   * a `let`'s type ascription (`type_annotation:` in `:assignment`'s meta —
  #     parser.ex `let_ascribed`), and
  #   * a match arm's OWN PATTERN (`pattern:` in `:match_arm`'s meta — parser.ex
  #     `parse_match_arm/1`, `{:match_arm, [pattern: p], [body]}`).
  #
  # Left unhandled, a module using a union ONLY in one of these two positions
  # (no function param/return type ever names the union) is silently routed to
  # the classic pipeline, which has no union machinery — not a clean
  # `:unsupported_container`-style rejection but a confusing, unrelated error
  # out of classic's ordinary (non-union-aware) pattern handling.
  # A union can hide in META, which the generic fallback (children-only) never visits: a
  # `let`'s `:type_annotation`, and a match arm's `:pattern` (typed patterns live there).
  #
  # These scan the meta for UNION SYNTAX ONLY — deliberately NOT the full `dependent?/1`
  # walk. `dependent?/1` decides which COMPILER PIPELINE builds a module, and the two erase
  # constructors differently. Running the full predicate over a match arm's pattern exposes
  # ordinary constructor patterns to the pre-existing name-based `"Equivalent"`/`"reflexive"`
  # heuristic below — so a program with an ADT constructor merely NAMED `Equivalent`, and no
  # `|` anywhere, was silently rerouted to the dependent pipeline.
  def dependent?({:assignment, meta, children}) when is_list(meta) do
    union_syntax?(Keyword.get(meta, :type_annotation)) or dependent?(children)
  end

  def dependent?({:match_arm, meta, children}) when is_list(meta) do
    union_syntax?(Keyword.get(meta, :pattern)) or dependent?(children)
  end

  def dependent?({:function_call, meta, children}) when is_list(meta) do
    Keyword.get(meta, :name) in ["Equivalent", "reflexive"] or Enum.any?(children, &dependent?/1)
  end

  def dependent?({:container, meta, body}) when is_list(meta) do
    case Keyword.get(meta, :container_type) do
      # A proof container inhabits propositional-equality types — inherently
      # dependent, and now elaborated into Core (routed like a module below).
      :proof ->
        true

      container_type when container_type in [:enum, :struct, :opaque] ->
        # A user-declared family whose name COLLIDES with the generated-union
        # namespace (`Cure.Elab.Union.union_family?/1` — reachable only via a
        # backtick-quoted identifier, e.g. `` `Union<Bool|Int>` ``) must be
        # routed to the DEPENDENT pipeline even when nothing else in the module
        # is dependent, so `Cure.Elab.Declarations`'s reserved-name rejection
        # actually runs. The classic pipeline never calls into
        # `Cure.Elab.Union` at all, so left classic-routed, such a name would
        # sail through unrejected and remain indistinguishable from a real
        # generated family to any OTHER dependent-routed module compiled into
        # the same program.
        reserved_family_name?(meta) or dependent?(body)

      _other ->
        dependent?(body)
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

  # Union syntax, and nothing else. Kept deliberately narrow — see the meta clauses above.
  defp union_syntax?({:union_type, _meta, _members}), do: true
  defp union_syntax?({:typed_pattern, _meta, _children}), do: true

  defp union_syntax?(node) when is_tuple(node),
    do: node |> Tuple.to_list() |> Enum.any?(&union_syntax?/1)

  defp union_syntax?(list) when is_list(list), do: Enum.any?(list, &union_syntax?/1)
  defp union_syntax?(_other), do: false

  defp dependent_params?(params) when is_list(params), do: Enum.any?(params, &dependent?/1)
  defp dependent_params?(_other), do: false

  defp reserved_family_name?(meta) do
    case Keyword.get(meta, :name) do
      name when is_binary(name) -> name |> String.to_atom() |> Cure.Elab.Union.union_family?()
      _ -> false
    end
  end

  @doc """
  Extract the `Cure.<Name>` module atom from a parsed `mod … end` program,
  defaulting to `Cure.Main` when no module container is present.
  """
  @spec module_atom(term()) :: module()
  def module_atom(ast), do: String.to_atom("Cure." <> (find_module_name(ast) || "Main"))

  defp find_module_name({:container, meta, _body}) when is_list(meta) do
    if module_like_container?(meta), do: Keyword.get(meta, :name)
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

  defp split_pi({:pi, _g, dom, cod}, acc), do: split_pi(cod, [dom | acc])
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
    if module_like_container?(meta) do
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
    if module_like_container?(meta) do
      body |> List.wrap() |> Enum.flat_map(&imports/1)
    else
      []
    end
  end

  # `use Std.{List, Core}` is grouping sugar: the brace `:items` name a set of
  # sibling modules under the `:source` namespace, each expanded to its own full
  # `source.item` import. A plain `use Std.List` (no `:items`) yields just the source.
  # (`:exposing` — the selective-name form `use M exposing (a, b)` — is a filter on
  # WHICH of the module's names come in unqualified, not a different module list, so
  # it does not affect the source expansion here.)
  defp imports({:import, meta, _}) when is_list(meta) do
    source = Keyword.fetch!(meta, :source)

    case Keyword.get(meta, :items, []) do
      [] -> [source]
      items -> Enum.map(items, &(source <> "." <> to_string(&1)))
    end
  end

  defp imports({_tag, _meta, children}) when is_list(children),
    do: Enum.flat_map(children, &imports/1)

  defp imports(list) when is_list(list), do: Enum.flat_map(list, &imports/1)
  defp imports(_other), do: []

  defp import_env([], _seen), do: {:ok, Env.empty()}

  defp import_env(imports, seen) do
    Enum.reduce_while(imports, {:ok, Env.empty()}, fn source, {:ok, acc} ->
      case source |> import_source_path() |> import_source_env(seen) do
        {:ok, imported} ->
          case merge_env(acc, imported) do
            {:ok, merged} -> {:cont, {:ok, merged}}
            {:error, _} = err -> {:halt, err}
          end
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

  # Constructor names DECLARED in a module's own source (transitive imports excluded). Mirror of
  # `owned_family_names/1`. Constructor names are their OWN namespace: a bare `Ok` may collide
  # with an imported `Ok` while the families (`Res` vs `Result`) never do.
  defp owned_ctor_names(path) do
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      declared_ctor_names(ast)
    else
      _ -> MapSet.new()
    end
  end

  # Build ONE module's flat env slice (own decls + its own imports), as today.
  defp module_slice_env(path) do
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false),
         :ok <- check_declarations(ast),
         {:ok, imported} <- import_env(imports(ast), MapSet.new()),
         seeded = seed_with_telescope_support(ast),
         {:ok, env0} <- merge_env(seeded, imported),
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
    # Dedup by module identity: a module that is BOTH auto-preluded and named in an
    # explicit `use` (e.g. `char.cure` says `use Std.Bounded`, which is also in the
    # auto-prelude) must be a SINGLE provider. Otherwise the shadow resolver sees the
    # same family supplied "twice" and re-keys it to `Mod#Type` as if two distinct
    # modules collided — dragging a builtin-owning prelude's key (`:bounded`) onto
    # `Std.Bounded#Bounded`, which then clashes with the prelude source's own
    # canonical `@builtin` self-registration. Auto-prelude entries come first so an
    # explicit duplicate is the one dropped.
    sources = Enum.uniq(auto_prelude_imports(ast) ++ imports(ast))
    modules = distinct_import_modules(sources)

    # Ownership scans the FULL transitive closure (not `modules`, which is
    # direct-only) — see the Design note + `transitive_import_modules/1` doc.
    # Family AND def ownership in ONE transitive walk (avoid re-walking): both are
    # `%{name => MapSet.t(owner_mod)}` maps fed to the shape-generic `classify/2`.
    #
    # The module being elaborated is dropped from the owner walk: the auto-prelude
    # chain can transitively re-enter THIS module (e.g. Std.Bounded is reached via
    # Std.Binary → Std.Char → Std.Bounded), and that self-import is not a foreign
    # provider — it is the same module as the local declaration. Counting it would
    # make `classify` see a family both locally declared AND "imported" (n_sources
    # ≥ 2) and re-key the module's own family against itself, so `@builtin(:bounded)`
    # would clash with the leaked `:"Std.Bounded#Bounded"`. Self contributes only
    # through `local` below.
    #
    # Family, def AND constructor ownership in ONE transitive walk. Constructor names are their
    # own namespace: a bare `Ok` collides with an imported `Ok` even when the families never do.
    self_mod = find_module_name(ast)

    {family_owners, def_owners, ctor_owners} =
      sources
      |> transitive_import_modules()
      |> Enum.reject(fn {mod_id, _path} -> mod_id == self_mod end)
      |> Enum.reduce({%{}, %{}, %{}}, fn {mod_id, path}, {fam_acc, def_acc, ctor_acc} ->
        add = fn names, acc ->
          Enum.reduce(names, acc, fn name, a ->
            Map.update(a, name, MapSet.new([mod_id]), &MapSet.put(&1, mod_id))
          end)
        end

        {add.(owned_family_names(path), fam_acc), add.(owned_def_names(path), def_acc),
         add.(owned_ctor_names(path), ctor_acc)}
      end)

    local = declared_type_names(ast)
    local_ctors = declared_ctor_names(ast)
    local_defs = MapSet.new(local_def_names(ast))
    %{losers: losers, ambiguous: ambiguous} = Resolution.classify(family_owners, local)
    # Def ambiguity (no local winner) is enforced at resolution time (Task 3 via
    # `ambiguous_modules/2`); here we only need the losers to re-key their keys.
    %{losers: def_losers} = Resolution.classify(def_owners, local_defs)
    %{losers: ctor_losers} = Resolution.classify(ctor_owners, local_ctors)

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
                   [losers, def_losers, ctor_losers]
                   |> Enum.map(&MapSet.new(Map.keys(&1)))
                   |> Enum.reduce(&MapSet.union/2)

                 slice =
                   Enum.reduce(owner_mods, slice, fn owner_mod, s ->
                     if MapSet.member?(reachable, owner_mod) do
                       Resolution.rekey_module_env(
                         s,
                         owner_mod,
                         Map.get(losers, owner_mod, MapSet.new()),
                         local_ctors,
                         Map.get(def_losers, owner_mod, MapSet.new()),
                         Map.get(ctor_losers, owner_mod, MapSet.new())
                       )
                     else
                       s
                     end
                   end)

                 case merge_env(acc, slice) do
                   {:ok, merged} -> {:cont, {:ok, merged}}
                   {:error, _} = err -> {:halt, err}
                 end

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

      # Record the DIRECT import set so bare-name resolution can prefer a direct
      # owner over a name reachable only through a module's transitive re-export
      # (`use Std.List` + `use Std.Core`: `map` resolves to Std.List's own `map`,
      # not the Std.Option `map` that Core merely re-exports). `modules` is the
      # direct list (explicit `use` + auto-prelude); transitive-only modules are
      # deliberately excluded.
      direct_ids = MapSet.new(modules, fn {mod_id, _path} -> mod_id end)
      {:ok, %{cleaned | import_modules: direct_ids}, ambiguous}
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
           :ok <- check_declarations(ast),
           {:ok, imported} <- import_env(imports(ast), MapSet.put(seen, module_name)),
           seeded = seed_with_telescope_support(ast),
           {:ok, env0} <- merge_env(seeded, imported),
           {:ok, env} <- elaborate_declarations(declarations(ast), env0, prelude_source?(ast)) do
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
    "Std.Sigma" => [
      sigma_first: :sigma_first,
      sigma_second: :sigma_second,
      tproj2: :tproj2,
      tproj3: :tproj3,
      tproj4: :tproj4,
      tproj5: :tproj5,
      tproj6: :tproj6,
      tproj7: :tproj7,
      tproj8: :tproj8
    ]
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

  # Every `Env` field this function knows how to combine. `merge_env/2` builds a
  # FRESH `%Env{}`, so any field omitted here silently reverts to the struct default
  # — that is how `interfaces`/`coherence`/`constrained` were lost across module
  # boundaries, making an imported interface's instances invisible to the importer
  # and quietly breaking global coherence. The assertion below turns the next such
  # omission into a compile error rather than a runtime mystery.
  @merged_env_keys ~w(families ctors ctor_to_family defs certified builtins
                      primitives interfaces coherence constrained import_modules)a

  @env_keys Map.keys(Map.from_struct(%Env{}))
  missing = @env_keys -- @merged_env_keys

  if missing != [] do
    raise CompileError,
      description:
        "Cure.Elab.Program.merge_env/2 does not merge Env field(s) #{inspect(missing)}. " <>
          "Add them to the merge (and to @merged_env_keys) or they will be dropped " <>
          "when an imported module's env is combined with the importing module's."
  end

  defp merge_env(%Env{} = left, %Env{} = right) do
    with {:ok, coherence} <- merge_coherence(left.coherence, right.coherence) do
      {:ok,
       %Env{
         families: Map.merge(left.families, right.families),
         ctors: Map.merge(left.ctors, right.ctors),
         ctor_to_family: Map.merge(left.ctor_to_family, right.ctor_to_family),
         defs: Map.merge(left.defs, right.defs),
         certified: MapSet.union(left.certified || MapSet.new(), right.certified || MapSet.new()),
         builtins: Map.merge(left.builtins, right.builtins),
         primitives: Map.merge(left.primitives, right.primitives),
         interfaces: Map.merge(left.interfaces, right.interfaces),
         coherence: coherence,
         constrained: Map.merge(left.constrained, right.constrained),
         import_modules: MapSet.union(left.import_modules, right.import_modules)
       }}
    end
  end

  defp merge_coherence(nil, right), do: {:ok, right}
  defp merge_coherence(left, nil), do: {:ok, left}

  defp merge_coherence(%Coherence{} = left, %Coherence{} = right) do
    # Global coherence must survive the merge: two modules may not each supply an
    # anonymous instance for the same `(interface, head)`. Identical entries are
    # fine — a diamond import re-delivers the same instance descriptor by two paths,
    # and `import_env/2` accumulates left-to-right — so only a genuine DISAGREEMENT
    # is an overlap. Named instances are exempt from uniqueness by design but their
    # names must still not collide with a different instance.
    with {:ok, anon} <- merge_instances(left.anon, right.anon, :overlapping_instance),
         {:ok, named} <- merge_instances(left.named, right.named, :overlapping_named_instance) do
      {:ok, %Coherence{anon: anon, named: named}}
    end
  end

  defp merge_instances(left, right, error_tag) do
    Enum.reduce_while(right, {:ok, left}, fn {key, ref}, {:ok, acc} ->
      case Map.fetch(acc, key) do
        {:ok, ^ref} -> {:cont, {:ok, acc}}
        {:ok, _other} -> {:halt, {:error, overlap_error(error_tag, key)}}
        :error -> {:cont, {:ok, Map.put(acc, key, ref)}}
      end
    end)
  end

  defp overlap_error(:overlapping_instance, {iface, head}), do: {:overlapping_instance, iface, head}
  defp overlap_error(:overlapping_named_instance, name), do: {:overlapping_named_instance, name}

  # Two passes so that forward references and mutual recursion resolve: first
  # every type/record is elaborated and every function *signature* is registered;
  # then every function *body* is elaborated against the fully-populated
  # environment. Non-function declarations are elaborated in source order in pass
  # one (a function signature may reference any type declared before it).
  defp elaborate_declarations(items, env, prelude?) do
    with {:ok, env1, fn_decls} <- register_pass(items, env, prelude?) do
      body_pass(fn_decls, env1)
    end
  end

  defp register_pass(items, env, prelude?) do
    with {:ok, env_h} <- declare_type_headers(items, env) do
      body_register_pass(items, env_h, prelude?)
    end
  end

  # Header pre-pass: register every ctor-bearing type family's HEADER (name +
  # telescopes, empty ctors) before any constructor body is elaborated, so a
  # field type may forward-reference a sibling declared later or a
  # mutually-recursive partner (standard `data`-block scoping). `declare_header`
  # is a no-op for non-type decls and for `@builtin` containers.
  defp declare_type_headers(items, env) do
    Enum.reduce_while(items, {:ok, env}, fn decl, {:ok, acc} ->
      case Declarations.declare_header(decl, acc) do
        {:ok, acc2} -> {:cont, {:ok, acc2}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp body_register_pass(items, env, prelude?) do
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
