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
    * `:detect_and_rewrite` — `(ast, ctx) -> {:rewrite, new_ast} | :no_change`.
      Given the current AST and the file context, either return the rewritten
      AST (which the fold threads into the next rule) or `:no_change`.
    * `:warning_template` — the message body emitted when the rule fires.
  """

  @enforce_keys [:id, :description, :phase, :detect_and_rewrite, :warning_template]
  defstruct [:id, :description, :phase, :detect_and_rewrite, :warning_template]

  @typedoc "The whole-file AST a rule receives and returns (a `{:block, …}` node)."
  @type ast :: term()

  @typedoc "Per-file context: the set of type names in scope (spec §4)."
  @type ctx :: MapSet.t()

  @typedoc "A rule's decision for one file."
  @type result :: {:rewrite, ast()} | :no_change

  @type t :: %__MODULE__{
          id: atom(),
          description: String.t(),
          phase: :syntactic | :needs_resolution,
          detect_and_rewrite: (ast(), ctx() -> result()),
          warning_template: String.t()
        }
end
