defmodule Cure.Migrate.MonotonePropertyTest do
  use ExUnit.Case, async: true
  # Stdlib-scale: parses, migrates-to-fixpoint, and reprints every lib/std/*.cure
  # file twice (117 files). Genuinely whole-stdlib work, so per test_helper.exs it
  # is excluded from the default run (where async contention pushes its ~5s of CPU
  # past the 60s per-test wall) and runs in CI via `mix test --include slow`.
  @moduletag :slow
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
