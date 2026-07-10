defmodule Cure.Migrate.MonotonePropertyTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser, Trivia, Printer}
  alias Cure.Migrate

  defp fixpoint_string(src) do
    {:ok, toks, trivia} = Lexer.tokenize(src, trivia: true)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    {:ok, out, _} = Migrate.run_to_fixpoint(Trivia.attach(ast, trivia))
    Printer.quoted_to_string(out)
  end

  test "migrating a fixpoint output again is byte-identical (monotone law) across the stdlib" do
    for path <- Path.wildcard("lib/std/*.cure") do
      once = fixpoint_string(File.read!(path))
      twice = fixpoint_string(once)
      assert once == twice, "non-monotone on #{path}"
    end
  end
end
