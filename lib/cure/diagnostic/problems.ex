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
          | :call_argument
          | :call_result
          | :operator_operand
          | :condition
          | :branch
          | :element
          | :record_field
          | :record_update
          | :pattern
          | :constructor_argument
          | :implicit
          | :ffi
          | :actor
          | :fsm

  @type t :: %__MODULE__{
          kind: kind(),
          span: Cure.Diagnostic.Span.t() | nil,
          owner: term(),
          index: non_neg_integer() | nil,
          details: map()
        }
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
