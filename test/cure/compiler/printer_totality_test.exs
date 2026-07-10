defmodule Cure.Compiler.PrinterTotalityTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Printer
  alias Cure.Compiler.Printer.UnprintableNodeError

  test "an unhandled node kind raises loudly, never silently inspects" do
    # A synthetic node kind the Printer has no clause for.
    bogus = {:definitely_not_a_real_node_kind, [line: 1, col: 1], []}

    assert_raise UnprintableNodeError, fn ->
      Printer.quoted_to_string(bogus)
    end
  end
end
