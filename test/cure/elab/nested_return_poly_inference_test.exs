defmodule Cure.Elab.NestedReturnPolyInferenceTest do
  @moduledoc """
  A return-ONLY lowercase type variable NESTED under a constructor (`List(k)`)
  must be solvable from the caller's expected type, exactly as a BARE return-only
  var already is (`Std.Map.get(...) -> v`). The expected type `List(t)` should pin
  `k := t` by descending structurally into `List(?k) ~ List(t)`.

  Regression repro: `Std.Map.keys(map: Map) -> List(k)` — `k` appears only nested
  in the return type. Calling it where `List(t)` is expected previously failed with
  `{:error, {:unsolved_metavariables, :keys}}`.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @repro """
  mod P
    use Std.Map
    fn to_list(set: Map) -> List(t) = Std.Map.keys(set)
  end
  """

  test "nested return-only type var is solved from the expected type" do
    assert {:ok, _env} = Program.elaborate(@repro)
  end
end
