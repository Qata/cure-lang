defmodule Cure.Migrate do
  @moduledoc """
  The migration facility's rule engine (spec §4). Holds the ordered registry of
  migration rules and runs them over a whole-file AST as a fold, threading each
  rule's rewrite into the next and collecting one warning per rewrite.

  Two consumers share this one engine:

    * `cure build` reports the warnings but keeps the original source.
    * `cure migrate` applies the rewrites and reprints the file.

  See `Cure.Migrate.Rule` for the shape of a single rule.
  """

  alias Cure.Migrate.Rule

  defmodule Warning do
    @moduledoc """
    A migration warning emitted when a rule rewrites (or, in `cure build`,
    *would* rewrite) a file. `:rule` is the rule's stable id atom; `:file` and
    `:line` locate it for the user.
    """
    @enforce_keys [:rule, :message, :file]
    defstruct [:rule, :message, :file, :line]

    @type t :: %__MODULE__{
            rule: atom(),
            message: String.t(),
            file: String.t(),
            line: pos_integer() | nil
          }
  end

  @doc """
  The built-in rule registry, in declaration (application) order. Seeded by the
  day-one rules (Tasks 8/9/9b); empty until then. `run/2` uses this unless the
  caller passes an explicit `:rules` list (tests do).
  """
  @spec rules() :: [Rule.t()]
  def rules,
    do: [
      Cure.Migrate.Rules.IfElifToPickup.rule(),
      Cure.Migrate.Rules.UppercaseTypeVar.rule(),
      Cure.Migrate.Rules.GroupHoist.rule()
    ]

  @doc """
  Run `rules` over `ast` as an ordered fold. Each rule sees the AST as left by
  the previous rule; a `{:rewrite, new_ast}` result is threaded forward and
  records one `Warning`, a `:no_change` result is transparent. Returns
  `{final_ast, warnings}` with warnings in rule-application order.

  Options:

    * `:file` — the source path, recorded on each warning (default `"nofile"`).
    * `:rules` — override the registry (default `rules/0`).
    * `:apply` — which rewrites to fold into the returned AST:
        * `:all` (default) — every rule's rewrite; used by `cure migrate`.
        * `:safe_only` — only the rewrites of rules flagged `tolerate_safe?`;
          used by `cure build`, so an unsafe rule *warns* but leaves the legacy
          form as-is in the compiled AST (spec's "normalize in-memory where
          safe"). Warnings are emitted for every fired rule in both modes.
  """
  @spec run(Rule.ast(), keyword()) :: {Rule.ast(), [Warning.t()]}
  def run(ast, opts \\ []) do
    file = Keyword.get(opts, :file, "nofile")
    rule_set = Keyword.get(opts, :rules, rules())
    apply_mode = Keyword.get(opts, :apply, :all)
    ctx = build_ctx(ast, file)

    Enum.reduce(rule_set, {ast, []}, fn %Rule{} = rule, {acc_ast, warns} ->
      case rule.detect_and_rewrite.(acc_ast, ctx) do
        {:rewrite, new_ast} ->
          {commit(rule, apply_mode, acc_ast, new_ast), warns ++ warnings_for(rule, file, [nil])}

        {:rewrite, new_ast, lines} ->
          {commit(rule, apply_mode, acc_ast, new_ast), warns ++ warnings_for(rule, file, lines)}

        {:warn, lines} ->
          {acc_ast, warns ++ warnings_for(rule, file, lines)}

        :no_change ->
          {acc_ast, warns}
      end
    end)
  end

  # Fold the rewrite (`:all` mode, or a `tolerate_safe?` rule) or keep the legacy
  # AST while still having warned (`:safe_only` mode, unsafe rule).
  defp commit(_rule, :all, _old_ast, new_ast), do: new_ast
  defp commit(%Rule{tolerate_safe?: true}, :safe_only, _old_ast, new_ast), do: new_ast
  defp commit(%Rule{tolerate_safe?: false}, :safe_only, old_ast, _new_ast), do: old_ast

  defp warnings_for(%Rule{} = rule, file, lines) do
    Enum.map(lines, fn line ->
      %Warning{rule: rule.id, message: rule.warning_template, file: file, line: line}
    end)
  end

  @typedoc "Why a path failed the git preflight."
  @type git_reason :: :dirty | :untracked | :not_a_repo

  @doc """
  Preflight git-safety guard for `cure migrate` (spec §5.7): every path must be
  tracked and porcelain-clean before any file is rewritten, so a migration can
  always be reviewed and reverted as a diff. Classifies **each** path
  independently (no short-circuit) and returns one reason per failing path — a
  batch can legitimately mix untracked scratch files with merely-dirty tracked
  ones, and a single reason-for-the-whole-batch could not represent that without
  misreporting some paths.

  Returns `:ok` when every path is clean, else `{:error, [{path, reason}]}` in
  the order `paths` was given, where `reason` is `:untracked`, `:dirty`, or
  `:not_a_repo`.

  Each `git` invocation pins `cd: Path.dirname(path)` (git discovers the repo
  root upward from there): `git status`/`git ls-files` resolve relative to the
  caller's cwd, not the repo containing `path`, so without this a path in a
  different repo than the caller's cwd fails with "outside repository".
  """
  @spec git_guard([Path.t()]) :: :ok | {:error, [{Path.t(), git_reason()}]}
  def git_guard(paths) do
    failures =
      paths
      |> Enum.map(fn path -> {path, classify_path(path)} end)
      |> Enum.reject(fn {_path, reason} -> reason == :clean end)

    if failures == [], do: :ok, else: {:error, failures}
  end

  defp classify_path(path) do
    dir = Path.dirname(path)
    # Pin the git call to the file's own directory and address the file by its
    # basename there: this resolves correctly whether `path` was given absolute
    # or relative to a different cwd (a relative `lib/a.cure` addressed from
    # `cd lib` would otherwise become `lib/lib/a.cure` and misclassify).
    name = Path.basename(path)

    case System.cmd("git", ["ls-files", "--error-unmatch", name], cd: dir, stderr_to_stdout: true) do
      {_out, 0} -> porcelain_status(name, dir)
      {out, _nonzero} -> if not_a_repo?(out), do: :not_a_repo, else: :untracked
    end
  end

  defp porcelain_status(name, dir) do
    case System.cmd("git", ["status", "--porcelain", "--", name], cd: dir) do
      {"", 0} -> :clean
      {_nonempty, 0} -> :dirty
      {_out, _nonzero} -> :dirty
    end
  end

  defp not_a_repo?(output), do: output =~ "not a git repository"

  @doc """
  Build the per-file context consulted by `:needs_resolution` rules: the set of
  type names (as strings) in scope for `ast`. Seeded with Cure's built-in
  primitive type names (`@builtin_type_names`, owned by the lint) — and
  unioned with the type names this file declares (structs, enums, type aliases,
  and indexed families) and those it imports.

  `file` is the consuming source's path; it is needed to resolve USER-module
  imports (a `use MyApp.Foo` has no path convention — see `imported_names/2` —
  so the only handle is a sibling `.cure` file next to `file`). Callers with no
  path may use the arity-1 form, which resolves only `Std.*` + auto-prelude
  imports (a user import then contributes nothing rather than crashing).
  """
  @spec build_ctx(Rule.ast(), Path.t()) :: MapSet.t()
  def build_ctx(ast, file \\ "nofile") do
    builtin_type_names()
    |> MapSet.union(declared_type_names(ast))
    |> MapSet.union(declared_ctor_names(ast))
    |> MapSet.union(imported_names(ast, file))
  end

  # The built-in type names in scope for every module — real Cure types (never
  # free type variables) that must NOT be lowercased. The lint owns this surface
  # vocabulary directly (the classic type-checker Env, which formerly supplied
  # the first group, was deleted in the #18 rip-out). Group 1 = the surface
  # primitive types (`Int`/`Float`/`String`/`Bool`/`Atom`/`Unit`/`Any`/`Never`/
  # `Char`). Group 2: `Type` is the universe kind (`fn F(a: Type) -> Type`);
  # `Pid`/`Ref`/`Binary`/`Bitstring` are BEAM primitive types; `Map`/`Tuple` are
  # built-in containers; `Nat` is the Int-tier foundational numeric (dedicated
  # kernel literal forms). Without these, container/kind signatures warn
  # spuriously and `cure migrate --all` would corrupt them (`Pid` -> `pid`). Data
  # *constructors* of imported inductives (e.g. `Std.Nat`'s `Z`/`S`) are a
  # different category — resolved per-import (`imported_names/2`), not here.
  @builtin_type_names ~w(Int Float String Bool Atom Unit Any Never Char
                         Type Pid Ref Binary Bitstring Map Tuple Nat)

  defp builtin_type_names, do: MapSet.new(@builtin_type_names)

  # Every type name this file introduces, gathered by a full pre-order walk:
  #   * `{:container, [container_type: :struct | :enum | :opaque, name: n], _}` —
  #     records, enums, and bodyless opaque handles (`opaque type GCounter`)
  #   * `{:type_annotation, [name: n], _}` — `typealias N = …`
  #   * `{:indexed_type, [name: n], _}` — indexed families (defensive; carries :name)
  defp declared_type_names(ast) do
    ast |> collect_type_names([]) |> MapSet.new()
  end

  defp collect_type_names({:container, meta, ch}, acc) when is_list(ch) do
    acc =
      case Keyword.get(meta, :container_type) do
        t when t in [:struct, :enum, :opaque] -> maybe_name(meta, acc)
        _ -> acc
      end

    Enum.reduce(ch, acc, &collect_type_names/2)
  end

  defp collect_type_names({:type_annotation, meta, ch}, acc) when is_list(ch) do
    Enum.reduce(ch, maybe_name(meta, acc), &collect_type_names/2)
  end

  defp collect_type_names({:indexed_type, meta, ch}, acc) when is_list(ch) do
    Enum.reduce(ch, maybe_name(meta, acc), &collect_type_names/2)
  end

  defp collect_type_names({_k, _meta, ch}, acc) when is_list(ch) do
    Enum.reduce(ch, acc, &collect_type_names/2)
  end

  defp collect_type_names({_k, _meta, _name, inner}, acc), do: collect_type_names(inner, acc)
  defp collect_type_names(l, acc) when is_list(l), do: Enum.reduce(l, acc, &collect_type_names/2)
  defp collect_type_names(_other, acc), do: acc

  defp maybe_name(meta, acc) do
    case Keyword.get(meta, :name) do
      n when is_binary(n) -> [n | acc]
      _ -> acc
    end
  end

  # Every data-constructor name this file introduces. A constructor spelled in an
  # index/argument position (`Optic(s, a, LensKind)`) parses as a bare
  # `{:variable}` node indistinguishable from a free type var, so its name must
  # be in `ctx` too — otherwise the rule lowercases it (`LensKind` -> `lenskind`),
  # corrupting the family index. Three surface spellings carry constructors:
  #   * `{:variable, [variant: true], name}` — nullary enum variant (`LensKind`)
  #   * `{:function_def, [variant: true, name: n], _}` — field-carrying variant
  #     (`MkLensRep(a, (a) -> s)`), a constructor decl reusing the fn-def node
  #   * `{:gadt_ctor, [name: n], _}` — an `indices`-form GADT constructor
  defp declared_ctor_names(ast) do
    ast |> collect_ctor_names([]) |> MapSet.new()
  end

  defp collect_ctor_names({:variable, meta, name}, acc) when is_binary(name) do
    if Keyword.get(meta, :variant) == true, do: [name | acc], else: acc
  end

  defp collect_ctor_names({:function_def, meta, ch}, acc) when is_list(ch) do
    acc = if Keyword.get(meta, :variant) == true, do: maybe_name(meta, acc), else: acc
    Enum.reduce(ch, acc, &collect_ctor_names/2)
  end

  defp collect_ctor_names({:gadt_ctor, meta, ch}, acc) when is_list(ch) do
    Enum.reduce(ch, maybe_name(meta, acc), &collect_ctor_names/2)
  end

  defp collect_ctor_names({_k, _meta, ch}, acc) when is_list(ch) do
    Enum.reduce(ch, acc, &collect_ctor_names/2)
  end

  defp collect_ctor_names({_k, _meta, _name, inner}, acc), do: collect_ctor_names(inner, acc)
  defp collect_ctor_names(l, acc) when is_list(l), do: Enum.reduce(l, acc, &collect_ctor_names/2)
  defp collect_ctor_names(_other, acc), do: acc

  # The type + constructor names each `use`d module exports, resolved by reading
  # the imported module's source and collecting its declarations (the same walk
  # used for this file). An imported type or constructor spelled in a signature
  # (`Vector(a, Z)` — `Z` from `Std.Nat`) is a real name, not a free type
  # variable, but only the imported module knows it. DIRECT imports only (no
  # transitive walk): a name used in this file's signatures is either declared
  # here, a builtin, or directly imported. Best-effort and FAIL-OPEN — an
  # unresolvable import (non-stdlib module, missing source dir, read/parse
  # failure) contributes nothing rather than crashing the warn-only lint.
  # The stdlib modules the elaborator auto-imports into EVERY module with no
  # `use` statement (`Cure.Elab.Program.@auto_prelude`). A file like `proof.cure`
  # references `Nat`/`Z`/`S` with no import node at all — it gets them from this
  # implicit prelude — so their exported names must seed the ctx exactly as a
  # direct `use` would, or the auto-imported `Z` is misread as a free type var.
  # Duplicated (not imported) to keep the warn-only lint decoupled from the
  # elaborator's private attr; keep in sync with program.ex if the prelude grows.
  @auto_prelude ~w(Std.Bool Std.Nat Std.Sigma Std.Int Std.Float Std.Binary Std.Bounded)

  defp imported_names(ast, file) do
    sources = Enum.uniq(collect_import_sources(ast, []) ++ @auto_prelude)
    # User (non-`Std.*`) imports have no path convention — Cure resolves them by
    # co-compilation, not by name→path — so they cannot be read the way a stdlib
    # source is. The only handle a single-file lint has is the sibling `.cure`
    # files next to `file`; build a mod-name→exports map from them once, up front.
    sibling_exports = sibling_module_exports(file, sources)

    Enum.reduce(sources, MapSet.new(), fn source, acc ->
      names =
        case stdlib_source_path(source) do
          {:ok, path} -> exported_names_of_file(path)
          :error -> {:ok, Map.get(sibling_exports, source, MapSet.new())}
        end

      case names do
        {:ok, ns} -> MapSet.union(acc, ns)
        :error -> acc
      end
    end)
  end

  defp collect_import_sources({:import, meta, _}, acc) do
    case Keyword.get(meta, :source) do
      s when is_binary(s) -> [s | acc]
      _ -> acc
    end
  end

  defp collect_import_sources({_k, _meta, ch}, acc) when is_list(ch),
    do: Enum.reduce(ch, acc, &collect_import_sources/2)

  defp collect_import_sources({_k, _meta, _name, inner}, acc),
    do: collect_import_sources(inner, acc)

  defp collect_import_sources(l, acc) when is_list(l),
    do: Enum.reduce(l, acc, &collect_import_sources/2)

  defp collect_import_sources(_other, acc), do: acc

  # The type + constructor names a `.cure` source at `path` exports. Fail-open:
  # any read/lex/parse failure yields `:error` and contributes nothing.
  defp exported_names_of_file(path) do
    with {:ok, src} <- File.read(path),
         {:ok, tokens} <- Cure.Compiler.Lexer.tokenize(src, emit_events: false),
         {:ok, ast} <- Cure.Compiler.Parser.parse(tokens, emit_events: false) do
      {:ok, MapSet.union(declared_type_names(ast), declared_ctor_names(ast))}
    else
      _ -> :error
    end
  end

  # Resolve USER-module imports (`use MyApp.Foo`, i.e. any non-`Std.*` source)
  # by scanning the consuming file's directory. Cure has no name→path convention
  # for user modules — the real compiler resolves them by co-compiling all input
  # files together, a registry this per-file lint does not have — so the only
  # sound handle is the sibling `.cure` sources next to `file`. Each sibling is
  # matched to an import by its declared `mod` NAME (robust to arbitrary
  # filenames), and only the requested sources are kept. Returns a
  # `mod-name-string => exported-names` map. Scans nothing (returns `%{}`) when
  # there is no file path or no user import — so the pure-`Std` case pays zero
  # directory I/O. Fail-open throughout.
  defp sibling_module_exports(file, sources) do
    user_sources =
      sources
      |> Enum.reject(&match?({:ok, _}, stdlib_source_path(&1)))
      |> MapSet.new()

    if file in [nil, "", "nofile"] or MapSet.size(user_sources) == 0 do
      %{}
    else
      Path.dirname(file)
      |> Path.join("*.cure")
      |> Path.wildcard()
      |> Enum.reduce(%{}, fn path, acc ->
        with {:ok, name} <- module_name_of_file(path),
             true <- MapSet.member?(user_sources, name),
             {:ok, names} <- exported_names_of_file(path) do
          Map.put(acc, name, names)
        else
          _ -> acc
        end
      end)
    end
  end

  # The declared `mod`/`proof`-container name of the source at `path`, as a
  # string, mirroring `Cure.Elab.Program.find_module_name/1`. Fail-open.
  defp module_name_of_file(path) do
    with {:ok, src} <- File.read(path),
         {:ok, tokens} <- Cure.Compiler.Lexer.tokenize(src, emit_events: false),
         {:ok, ast} <- Cure.Compiler.Parser.parse(tokens, emit_events: false),
         name when is_binary(name) <- module_name(ast) do
      {:ok, name}
    else
      _ -> :error
    end
  end

  defp module_name({:container, meta, _body}) when is_list(meta) do
    if Keyword.get(meta, :container_type) in [:module, :proof],
      do: Keyword.get(meta, :name)
  end

  defp module_name({_tag, _meta, children}) when is_list(children),
    do: Enum.find_value(children, &module_name/1)

  defp module_name(list) when is_list(list),
    do: Enum.find_value(list, &module_name/1)

  defp module_name(_other), do: nil

  # Resolve a `Std.<Name>` import source to its `.cure` file, searching the same
  # stdlib source directories the elaborator uses (`import_source_path/1`). Only
  # `Std.*` is handled — a bare/user module resolves to `:error` and is skipped.
  defp stdlib_source_path(source) do
    case String.split(source, ".") do
      ["Std", name] ->
        Cure.Stdlib.Paths.source_dirs()
        |> Enum.map(&Path.join(&1, String.downcase(name) <> ".cure"))
        |> Enum.find(&File.exists?/1)
        |> case do
          nil -> :error
          path -> {:ok, path}
        end

      _ ->
        :error
    end
  end
end
