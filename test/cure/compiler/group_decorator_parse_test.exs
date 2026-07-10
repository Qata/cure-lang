defmodule Cure.Compiler.GroupDecoratorParseTest do
  @moduledoc """
  `@group` inside the mod body is a hard parse error (spec
  2026-07-10-group-decorator-placement). The canonical placement — above
  `mod`, attached to the module container — is covered by
  `Cure.Compiler.GroupDecoratorTest`.
  """
  use ExUnit.Case, async: true

  test "@group in the mod body is rejected at parse time" do
    src = "mod X\n  @group(:core)\n  fn f() -> Int = 1\n"

    assert {:error, {:parse_error, errors}} = Cure.Compiler.parse_source(src)

    assert Enum.any?(errors, &match?({:group_not_above_module, _line, _col}, &1)),
           "expected a :group_not_above_module error, got: #{inspect(errors)}"
  end
end
