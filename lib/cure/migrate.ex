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

  @doc "Rules to apply when crossing to `target` (spec §7.2)."
  @spec rules_for_crossing(Cure.Edition.t(), [Rule.t()]) :: [Rule.t()]
  def rules_for_crossing(target, rules \\ rules()) do
    Enum.filter(rules, fn r ->
      mandatory = r.enforced_in != nil and Cure.Edition.compare(r.enforced_in, target) in [:lt, :eq]
      proactive = r.tier in [:machine, :review] and Cure.Edition.compare(r.since, target) in [:lt, :eq]
      mandatory or proactive
    end)
  end

  @doc "The :manual rules whose old form is illegal at `target` (block the bump)."
  @spec blocking_manual(Cure.Edition.t(), [Rule.t()]) :: [Rule.t()]
  def blocking_manual(target, rules \\ rules()) do
    Enum.filter(rules, fn r ->
      r.tier == :manual and r.enforced_in != nil and
        Cure.Edition.compare(r.enforced_in, target) in [:lt, :eq]
    end)
  end

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
    {new_ast, warns, _rewriters} = fold_rules(ast, opts)
    {new_ast, warns}
  end

  # Shared fold behind `run/2` and `run_to_fixpoint/2`. Threads the AST through
  # the rule set as `run/2` documents, and additionally reports `rewriters` — the
  # ordered ids of rules whose committed rewrite actually changed the AST this
  # pass. `run_to_fixpoint/2` needs that: a pass whose rewrites net to identity
  # (e.g. a non-monotone `x->y`/`y->x` pair) leaves the AST equal yet is still
  # actively rewriting, so AST-equality alone cannot tell "done" from "thrashing"
  # — while a pure `:warn` rule must NOT count as a rewrite (it never converges
  # away, so counting it would loop forever). The list (not just a boolean) also
  # lets a verify failure be attributed to a *rewriter* rather than a warner.
  @spec fold_rules(Rule.ast(), keyword()) :: {Rule.ast(), [Warning.t()], [atom()]}
  defp fold_rules(ast, opts) do
    file = Keyword.get(opts, :file, "nofile")
    rule_set = Keyword.get(opts, :rules, rules())
    apply_mode = Keyword.get(opts, :apply, :all)
    ctx = build_ctx(ast)

    {ast, warns, rev_rewriters} =
      Enum.reduce(rule_set, {ast, [], []}, fn %Rule{} = rule, {acc_ast, warns, rewriters} ->
        case rule.detect_and_rewrite.(acc_ast, ctx) do
          {:rewrite, new_ast} ->
            committed = commit(rule, apply_mode, acc_ast, new_ast)
            {committed, warns ++ warnings_for(rule, file, [nil]), maybe_rewriter(rewriters, rule, committed, acc_ast)}

          {:rewrite, new_ast, lines} ->
            committed = commit(rule, apply_mode, acc_ast, new_ast)
            {committed, warns ++ warnings_for(rule, file, lines), maybe_rewriter(rewriters, rule, committed, acc_ast)}

          {:warn, lines} ->
            {acc_ast, warns ++ warnings_for(rule, file, lines), rewriters}

          :no_change ->
            {acc_ast, warns, rewriters}
        end
      end)

    {ast, warns, Enum.reverse(rev_rewriters)}
  end

  # Prepend the rule's id to the (reversed) rewriter list iff its commit actually
  # changed the AST — a `:safe_only`-suppressed rewrite is not a rewriter.
  defp maybe_rewriter(rewriters, %Rule{id: id}, committed, old_ast) do
    if committed != old_ast, do: [id | rewriters], else: rewriters
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
          | {:error, {:verify_failed, atom() | nil}}
  def run_to_fixpoint(ast, opts \\ []) do
    max = Keyword.get(opts, :max_passes, @max_passes)
    # The target edition governs the verify reparse (F12): output valid only under
    # the crossing target must parse under it, not the compiler default.
    edition = Keyword.get(opts, :edition) || Cure.Edition.current()

    case safe_print(ast) do
      {:ok, src} -> do_fixpoint(ast, opts, max, [], comment_texts(src), edition)
      # An input the Printer can't render can't be migrated cleanly — report it as
      # a verify failure (no culprit rule) rather than crashing the caller.
      {:error, _} -> {:error, {:verify_failed, nil}}
    end
  end

  defp do_fixpoint(ast, opts, passes_left, warns, baseline, edition) do
    {new_ast, pass_warns, rewriters} = fold_rules(ast, opts)

    cond do
      # Fixpoint reached: nothing rewrote the AST this pass. Pure `:warn` rules
      # may still have fired (they warn every pass and never converge away) —
      # that is expected and does NOT block convergence. Deduplicate the
      # accumulated warnings (F2): a rule that fires on N passes must surface its
      # warning once, not once per pass.
      new_ast == ast and rewriters == [] ->
        {:ok, ast, Enum.uniq(warns ++ pass_warns)}

      # Still rewriting at the pass budget → the rule set does not converge
      # (a rule-set bug, not a user error). Report the rules that fired last.
      passes_left <= 1 ->
        {:error, {:no_convergence, pass_warns |> Enum.map(& &1.rule) |> Enum.uniq()}}

      true ->
        case verify(new_ast, baseline, edition) do
          :ok ->
            do_fixpoint(new_ast, opts, passes_left - 1, warns ++ pass_warns, baseline, edition)

          {:error, _reason} ->
            # Attribute to a rule that actually REWROTE this pass (F-culprit): a
            # verify break is caused by a rewrite, never by a pure-warn rule.
            {:error, {:verify_failed, List.last(rewriters)}}
        end
    end
  end

  # Reprint → reparse (fail if the output no longer parses) AND diff comments
  # against `baseline` — the ORIGINAL input's comment texts, captured once by
  # `run_to_fixpoint/2` before the first pass, not the previous pass's output.
  # Checking against the true original (not pass-to-pass) is what makes this
  # catch a comment a rule drops on pass 3 even though passes 1-2 preserved
  # everything — re-basing to each intermediate pass would let that slip
  # through as "no *new* loss this pass". Reparse uses the target `edition` so
  # output valid only under it is not spuriously rejected (F12). The whole body
  # is guarded (F3b): a rule that yields unrenderable/unparseable output must
  # surface a clean {:error, …}, never crash the migration.
  defp verify(ast, baseline_comments, edition) do
    with {:ok, src} <- safe_print(ast),
         {:ok, toks} <- Cure.Compiler.Lexer.tokenize(src, emit_events: false, edition: edition),
         {:ok, _} <- Cure.Compiler.Parser.parse(toks, emit_events: false, edition: edition) do
      if baseline_comments -- comment_texts(src) == [] do
        :ok
      else
        {:error, :comment_dropped}
      end
    else
      _ -> {:error, :reparse}
    end
  rescue
    _ -> {:error, :verify_crashed}
  end

  # Render an AST to source, converting a Printer exception (e.g. an unrenderable
  # node a buggy rule produced) into a value rather than a propagating crash.
  defp safe_print(ast) do
    {:ok, Cure.Compiler.Printer.quoted_to_string(ast)}
  rescue
    _ -> {:error, :unprintable}
  end

  # The lossless-comment check for `verify/3`: every `#`-led comment body, trimmed,
  # sorted. Coarse-but-adequate — KNOWN latent limitation: the scan is not
  # quote-aware, so a `#` inside a string literal is misread as a comment. Harmless
  # today (no migrate rule rewrites string-literal contents, so the bogus entry is
  # stable across baseline/output and never trips `:comment_dropped`); make this
  # quote-aware before adding any rule that edits inside string literals.
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

  # `Type` — the kind universe / sort — is a built-in name that lives in every
  # scope but is not an entry in `Cure.Types.Env`'s `types` map (it classifies
  # types rather than being one). It appears pervasively in dependent signatures
  # (`{a: Type}`, `(a) -> Type`), and there is no reading of it as a user type
  # variable, so it is seeded here explicitly to keep the uppercase-type-var rule
  # from downgrading it to a free `type`.
  @builtin_sorts ["Type"]

  defp builtin_type_names do
    (Cure.Types.Env.new().types |> Map.keys()) |> Enum.concat(@builtin_sorts) |> MapSet.new()
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
