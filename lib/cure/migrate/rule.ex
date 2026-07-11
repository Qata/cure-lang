defmodule Cure.Migrate.Rule do
  @moduledoc """
  A single migration rule (spec §4). One rule detects one deprecated shape and
  rewrites it to the new edition's spelling. Rules are pure `AST × ctx -> result`
  functions collected into an ordered registry (`Cure.Migrate.rules/0`) and run
  as a fold by `Cure.Migrate.run/2`.

  The same rule set drives both consumers:

    * `cure build` — runs each rule to detect deprecated shapes and emits its
      warning, but keeps the *original* source (warn-and-tolerate).
    * `cure migrate` — applies each rule's rewrite and writes the result back
      (rewrite-and-write).

  ## Fields

    * `:id` — a stable warning id atom (e.g. `:W_uppercase_type_var`). Used as
      the warning code in both consumers and as the key tests assert on.
    * `:description` — a one-line human description of what the rule migrates.
    * `:phase` — `:syntactic` for rules that fire on shape alone, or
      `:needs_resolution` for rules that must consult the per-file `ctx` (the
      set of in-scope type names) before deciding — e.g. an uppercase type
      variable that is actually a declared type must NOT be renamed.
    * `:detect_and_rewrite` — `(ast, ctx) -> result`. Given the current AST and
      the file context, one of:
        * `{:rewrite, new_ast}` — rewrote; `run/2` records ONE warning from
          `warning_template` (with no line).
        * `{:rewrite, new_ast, lines}` — rewrote and knows the exact source
          line(s) it fired on; `run/2` records one warning per line.
        * `{:warn, lines}` — detected legacy shape(s) it could NOT rewrite (e.g.
          the paren-context skip in spec §5.5), so warn but leave the AST as-is.
        * `:no_change` — nothing found; transparent.
    * `:warning_template` — the message body emitted when the rule fires.
    * `:tier` — the single warn/rewrite/normalize authority (spec §5.3),
      replacing the old binary `tolerate_safe?`:
        * `:machine` — the rewrite is certified semantics-preserving; `cure build`
          may normalize it in-memory (`:safe_only` mode folds it).
        * `:review` — warn only; `cure build` must NOT normalize it (e.g.
          lowercasing a dependently-typed signature is not always safe).
        * `:manual` — no auto-migration; the reference must be ported by hand.
      `cure migrate` always applies every rule's rewrite regardless of `tier`.
    * `:since` — the edition this rule was introduced in.
    * `:enforced_in` — the edition at which the legacy form stops being a keyword
      / stops compiling (drives the lexer's edition-derived keyword set); `nil`
      when the legacy form is still accepted.
    * `:retires_keywords` — the keywords this rule retires at `enforced_in`
      (single source of truth for the lexer); `[]` when it retires none.
  """

  @enforce_keys [:id, :description, :phase, :detect_and_rewrite, :warning_template, :tier, :since]
  defstruct [
    :id,
    :description,
    :phase,
    :detect_and_rewrite,
    :warning_template,
    :tier,
    :since,
    enforced_in: nil,
    retires_keywords: []
  ]

  @type tier :: :machine | :review | :manual

  @typedoc "The whole-file AST a rule receives and returns (a `{:block, …}` node)."
  @type ast :: term()

  @typedoc "Per-file context: the set of type names in scope (spec §4)."
  @type ctx :: MapSet.t()

  @typedoc "A source line a warning points at (`nil` when the rule has none)."
  @type warning_loc :: pos_integer() | nil

  @typedoc "A rule's decision for one file."
  @type result ::
          {:rewrite, ast()}
          | {:rewrite, ast(), [warning_loc()]}
          | {:warn, [warning_loc()]}
          | :no_change

  @type t :: %__MODULE__{
          id: atom(),
          description: String.t(),
          phase: :syntactic | :needs_resolution,
          detect_and_rewrite: (ast(), ctx() -> result()),
          warning_template: String.t(),
          tier: tier(),
          since: Cure.Edition.t(),
          enforced_in: Cure.Edition.t() | nil,
          retires_keywords: [String.t()]
        }
end
