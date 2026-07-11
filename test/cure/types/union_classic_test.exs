defmodule Cure.Types.UnionClassicTest do
  @moduledoc """
  Pins the classic checker's coexistence with anonymous unions: it must not CRASH on a
  `{:union_type, …}` node.

  `Type.resolve/1` has no clause for the node, so it falls through to the pre-existing
  unconditional catch-all `def resolve(_), do: :any`. That catch-all is the entire
  reason "must not crash" holds — which means it is load-bearing by accident, and a
  future tightening of it would silently break the dependent pipeline's parser
  sharing. Hence this pin.

  Note what is NOT claimed: classic resolves an anonymous union to `:any` (its top
  type), NOT to its own structural `{:union, [...]}` type. That is deliberate — the
  dependent pipeline does the real checking here, and classic's only job is to not
  fall over. Zero classic production code was written for this feature.
  """
  use ExUnit.Case, async: true

  alias Cure.Types.Type

  @union {:union_type, [],
          [
            {:variable, [scope: :local], "Int"},
            {:variable, [scope: :local], "String"}
          ]}

  test "Type.resolve/1 maps a union_type node to :any rather than raising" do
    assert Type.resolve(@union) == :any
  end

  test "a union nested inside a type argument also resolves without raising" do
    nested = {:function_call, [name: "List"], [@union]}

    assert Type.resolve(nested) != :error
  end
end
