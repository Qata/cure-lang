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
      Cure.Migrate.Rules.GroupHoist.rule(),
      Cure.Migrate.Rules.ModuleRename.rule(),
      Cure.Migrate.Rules.RemovedModule.rule(),
      Cure.Migrate.Rules.ProtoToInterface.rule()
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
        * `:safe_only` — only the rewrites of `:machine`-tier rules; used by
          `cure build`, so a `:review`/`:manual` rule *warns* but leaves the
          legacy form as-is in the compiled AST (spec's "normalize in-memory
          where safe"). Warnings are emitted for every fired rule in both modes.
  """
  @spec run(Rule.ast(), keyword()) :: {Rule.ast(), [Warning.t()]}
  def run(ast, opts \\ []) do
    {new_ast, warns, _rewrote?} = fold_rules(ast, opts)
    {new_ast, warns}
  end

  # Shared fold behind `run/2` and `run_to_fixpoint/2`. Threads the AST through
  # the rule set as `run/2` documents, and additionally reports `rewrote?` —
  # whether any rule's committed rewrite actually changed the AST during this
  # pass. `run_to_fixpoint/2` needs that: a pass whose rewrites net to identity
  # (e.g. a non-monotone `x->y`/`y->x` pair) leaves the AST equal yet is still
  # actively rewriting, so AST-equality alone cannot tell "done" from "thrashing"
  # — while a pure `:warn` rule must NOT count as a rewrite (it never converges
  # away, so counting it would loop forever).
  @spec fold_rules(Rule.ast(), keyword()) :: {Rule.ast(), [Warning.t()], boolean()}
  defp fold_rules(ast, opts) do
    file = Keyword.get(opts, :file, "nofile")
    rule_set = Keyword.get(opts, :rules, rules())
    apply_mode = Keyword.get(opts, :apply, :all)
    ctx = build_ctx(ast)

    Enum.reduce(rule_set, {ast, [], false}, fn %Rule{} = rule, {acc_ast, warns, rewrote?} ->
      case rule.detect_and_rewrite.(acc_ast, ctx) do
        {:rewrite, new_ast} ->
          committed = commit(rule, apply_mode, acc_ast, new_ast)
          {committed, warns ++ warnings_for(rule, file, [nil]), rewrote? or committed != acc_ast}

        {:rewrite, new_ast, lines} ->
          committed = commit(rule, apply_mode, acc_ast, new_ast)
          {committed, warns ++ warnings_for(rule, file, lines), rewrote? or committed != acc_ast}

        {:warn, lines} ->
          {acc_ast, warns ++ warnings_for(rule, file, lines), rewrote?}

        :no_change ->
          {acc_ast, warns, rewrote?}
      end
    end)
  end

  # Fold the rewrite (`:all` mode, or a `:machine`-tier rule) or keep the legacy
  # AST while still having warned (`:safe_only` mode, `:review`/`:manual` rule).
  defp commit(_rule, :all, _old_ast, new_ast), do: new_ast
  defp commit(%Rule{tier: :machine}, :safe_only, _old_ast, new_ast), do: new_ast
  defp commit(%Rule{}, :safe_only, old_ast, _new_ast), do: old_ast

  defp warnings_for(%Rule{} = rule, file, lines) do
    Enum.map(lines, fn line ->
      %Warning{rule: rule.id, message: rule.warning_template, file: file, line: line}
    end)
  end

  @max_passes 8

  @doc """
  Run the registry to a fixpoint (spec §6.1): repeatedly apply `run/2` until a
  full pass changes nothing. After each changing pass, verify the reprinted
  output reparses and preserves every comment; a verify failure aborts. If the
  AST is still changing at `:max_passes`, return `{:error, {:no_convergence,
  culprit_rule_ids}}` (a rule-set bug, not a user error).
  """
  @spec run_to_fixpoint(Rule.ast(), keyword()) ::
          {:ok, Rule.ast(), [Warning.t()]}
          | {:error, {:no_convergence, [atom()]}}
          | {:error, {:verify_failed, atom()}}
  def run_to_fixpoint(ast, opts \\ []) do
    max = Keyword.get(opts, :max_passes, @max_passes)
    baseline_comments = comment_texts(Cure.Compiler.Printer.quoted_to_string(ast))
    do_fixpoint(ast, opts, max, [], baseline_comments)
  end

  defp do_fixpoint(ast, opts, passes_left, warns, baseline) do
    {new_ast, pass_warns, rewrote?} = fold_rules(ast, opts)

    cond do
      # Fixpoint reached: nothing rewrote the AST this pass. Pure `:warn` rules
      # may still have fired (they warn every pass and never converge away) —
      # that is expected and does NOT block convergence.
      new_ast == ast and not rewrote? ->
        {:ok, ast, warns ++ pass_warns}

      # Still rewriting at the pass budget → the rule set does not converge
      # (a rule-set bug, not a user error). Report the rules that fired last.
      passes_left <= 1 ->
        {:error, {:no_convergence, pass_warns |> Enum.map(& &1.rule) |> Enum.uniq()}}

      true ->
        case verify(new_ast, baseline) do
          :ok ->
            do_fixpoint(new_ast, opts, passes_left - 1, warns ++ pass_warns, baseline)

          {:error, _reason} ->
            culprit = pass_warns |> List.last() |> then(&(&1 && &1.rule))
            {:error, {:verify_failed, culprit}}
        end
    end
  end

  # Reprint → reparse (fail if the output no longer parses) AND diff comments
  # against `baseline` — the ORIGINAL input's comment texts, captured once by
  # `run_to_fixpoint/2` before the first pass, not the previous pass's output.
  # Checking against the true original (not pass-to-pass) is what makes this
  # catch a comment a rule drops on pass 3 even though passes 1-2 preserved
  # everything — re-basing to each intermediate pass would let that slip
  # through as "no *new* loss this pass".
  defp verify(ast, baseline_comments) do
    src = Cure.Compiler.Printer.quoted_to_string(ast)

    with {:ok, toks} <- Cure.Compiler.Lexer.tokenize(src, emit_events: false),
         {:ok, _} <- Cure.Compiler.Parser.parse(toks, emit_events: false) do
      if baseline_comments -- comment_texts(src) == [] do
        :ok
      else
        {:error, :comment_dropped}
      end
    else
      _ -> {:error, :reparse}
    end
  end

  # Mirrors Cure.CLI's migrate_comments/1 (lib/cure/cli.ex:1319): every `#`-led
  # comment body, trimmed, sorted — the same coarse-but-adequate lossless check
  # the file-mode `cure migrate` pipeline already uses.
  defp comment_texts(src) do
    src
    |> String.split("\n")
    |> Enum.flat_map(fn line ->
      case Regex.run(~r/#+\s?(.*)$/, line) do
        [_, txt] -> [String.trim(txt)]
        _ -> []
      end
    end)
    |> Enum.reject(&(&1 == ""))
    |> Enum.sort()
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
  primitive type names — derived from `Cure.Types.Env`, never hardcoded — and
  unioned with the type names this file declares (structs, enums, type aliases,
  and indexed families).
  """
  @spec build_ctx(Rule.ast()) :: MapSet.t()
  def build_ctx(ast) do
    MapSet.union(builtin_type_names(), declared_type_names(ast))
  end

  defp builtin_type_names do
    Cure.Types.Env.new().types |> Map.keys() |> MapSet.new()
  end

  # Every type name this file introduces, gathered by a full pre-order walk:
  #   * `{:container, [container_type: :struct | :enum, name: n], _}` — records/enums
  #   * `{:type_annotation, [name: n], _}` — `typealias N = …`
  #   * `{:indexed_type, [name: n], _}` — indexed families (defensive; carries :name)
  defp declared_type_names(ast) do
    ast |> collect_type_names([]) |> MapSet.new()
  end

  defp collect_type_names({:container, meta, ch}, acc) when is_list(ch) do
    acc =
      case Keyword.get(meta, :container_type) do
        t when t in [:struct, :enum] -> maybe_name(meta, acc)
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
end
