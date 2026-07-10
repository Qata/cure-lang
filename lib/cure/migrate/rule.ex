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
    * `:tolerate_safe?` — the spec's "where safe" knob for the `cure build`
      consumer. `false` (default): the rule *warns* during build but its rewrite
      is NOT folded into the compiled AST — the legacy form compiles as-is. Only
      `true` when the rewrite is certified semantics-preserving-and-compilable,
      so that `cure build` may normalize it in-memory. `cure migrate` always
      applies every rule's rewrite regardless of this flag.

      All three day-one rules are `false`: each legacy form still compiles today,
      so folding the rewrite is unnecessary, and doing so is either unsafe
      (lowercasing a dependently-typed signature breaks metavar solving),
      redundant (`if/elif` still compiles), or cosmetic (decorator relocation).
      A rule opts in only once its rewrite is proven safe AND the legacy form has
      actually stopped compiling (the "warn-now → error-later" transition).
  """

  @enforce_keys [:id, :description, :phase, :detect_and_rewrite, :warning_template]
  defstruct [
    :id,
    :description,
    :phase,
    :detect_and_rewrite,
    :warning_template,
    tolerate_safe?: false
  ]

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
          tolerate_safe?: boolean()
        }
end
