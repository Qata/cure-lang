defmodule Cure.Diagnostic.SyntaxProblem do
  @moduledoc "Structured parser context retained before diagnostic conversion."

  @enforce_keys [:kind]
  defstruct [:kind, :expected, :observed, :at, :within, :opener, :previous, alternatives: [], context: %{}]

  @type t :: %__MODULE__{
          kind: atom(),
          expected: term(),
          observed: term(),
          at: Cure.Diagnostic.Span.t() | nil,
          within: Cure.Diagnostic.Span.t() | nil,
          opener: Cure.Diagnostic.Span.t() | nil,
          previous: Cure.Diagnostic.Span.t() | nil,
          alternatives: [term()],
          context: map()
        }
end

defmodule Cure.Diagnostic.ExpectationOrigin do
  @moduledoc "Why a type was expected at a particular authored expression."

  @enforce_keys [:kind]
  defstruct [:kind, :span, :owner, :index, details: %{}]

  @type kind ::
          :annotation
          | :local_fact
          | :call_argument
          | :call_result
          | :application
          | :overload
          | :operator_operand
          | :condition
          | :branch
          | :element
          | :collection
          | :record
          | :record_field
          | :record_update
          | :pattern
          | :constructor_argument
          | :implicit
          | :effects
          | :ffi
          | :actor
          | :fsm
          | :supervisor

  @type t :: %__MODULE__{
          kind: kind(),
          span: Cure.Diagnostic.Span.t() | nil,
          owner: term(),
          index: non_neg_integer() | nil,
          details: map()
        }
end

defmodule Cure.Diagnostic.ProofChainSyntaxProblem do
  @moduledoc "Structured syntax failure for an equational proof chain."
  @enforce_keys [:kind]
  defstruct [:kind, :construct, :step, :observed, :expected, :insertion]

  @type t :: %__MODULE__{
          kind: atom(),
          construct: Cure.Diagnostic.Span.t() | nil,
          step: Cure.Diagnostic.Span.t() | nil,
          observed: term(),
          expected: term(),
          insertion: Cure.Diagnostic.Span.t() | nil
        }
end

defmodule Cure.Diagnostic.ProofChainMismatchProblem do
  @moduledoc "Structured typing failure for an equational proof-chain step."
  @enforce_keys [:kind, :step_index]
  defstruct [
    :kind,
    :step_index,
    :previous_step,
    :current_step,
    :justification,
    :expected,
    :actual,
    :cause,
    :residual_goal
  ]

  @type t :: %__MODULE__{
          kind: atom(),
          step_index: non_neg_integer(),
          previous_step: Cure.Diagnostic.Span.t() | nil,
          current_step: Cure.Diagnostic.Span.t() | nil,
          justification: Cure.Diagnostic.Span.t() | nil,
          expected: term(),
          actual: term(),
          cause: term(),
          residual_goal: term()
        }
end

defmodule Cure.Diagnostic.RewriteProblem do
  @moduledoc "Structured failure for a directed proof rewrite command."
  @enforce_keys [:kind]
  defstruct [:kind, :command, :theorem, :goal, :occurrences, :target, :direction, :searched, :cause]

  @type t :: %__MODULE__{
          kind: atom(),
          command: Cure.Diagnostic.Span.t() | nil,
          theorem: Cure.Diagnostic.Span.t() | nil,
          goal: Cure.Diagnostic.Span.t() | nil,
          occurrences: [term()],
          target: term(),
          direction: :forward | :backwards,
          searched: term(),
          cause: term()
        }
end

defmodule Cure.Diagnostic.DefiningEquationProblem do
  @moduledoc "Structured failure to resolve a generated defining equation."
  @enforce_keys [:kind]
  defstruct [:kind, :equation_use, :function_definition, :candidate_equations, :owner, :member]
end

defmodule Cure.Diagnostic.TypeProblem do
  @moduledoc "A contextual type disagreement independent of presentation."

  @enforce_keys [:kind, :actual, :expected, :origin]
  defstruct [:kind, :actual, :expected, :origin, :expression, :span, :related, debug: %{}]

  @type t :: %__MODULE__{
          kind: atom(),
          actual: term(),
          expected: term(),
          origin: Cure.Diagnostic.ExpectationOrigin.t(),
          expression: term(),
          span: Cure.Diagnostic.Span.t() | nil,
          related: Cure.Diagnostic.Span.t() | nil,
          debug: map()
        }
end
