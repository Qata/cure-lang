defmodule Cure.Stdlib.DependentEmitParityTest do
  @moduledoc """
  #18-readiness firewall, EMIT tier. The companion
  `dependent_elaboration_parity_test.exs` proves every `@green` stdlib module
  *elaborates* on the dependent pipeline. This one proves the strictly stronger
  property that actually gates the classic rip-out: each module completes the
  full DEPENDENT CODEGEN path and produces real BEAM function forms.

  Today the committed stdlib modules are syntactically non-dependent, so
  `Cure.Compiler.codegen/5` routes them through the CLASSIC codegen
  (`Cure.Elab.Program.dependent?/1` is false). Deleting the classic pipeline
  (#18) makes `codegen` route EVERY module through `Cure.Elab.Emit`
  unconditionally. So the question that decides whether the rip-out is a clean
  delete is not "does it elaborate" but "does the dependent emitter lower it to
  loadable forms." This test runs exactly the private `dependent_codegen/1`
  sequence (`check_ast_with_locals` → `Emit.compile_forms`) against each module
  and locks the answer in as an immutable regression: a future change that breaks
  dependent emission of a stdlib module is caught HERE, before rip-out, rather
  than discovered mid-teardown.

  The `@green` list mirrors the elaboration firewall's and only ever grows. The
  same seven modules are held out for the same reasons (show/io/access/set are
  classic-coexistence-blocked; http/regex are AtomVM dead-ends; pair is slated
  for retirement) — see `dependent_elaboration_parity_test.exs`. They emit
  through the dependent pipeline only after their rip-out rewrites land.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Program, Emit}

  @green ~w(
    actor app atom binary bool bounded char comparable core crdt decision equatable
    equivalent float fsm functor gen int iter json list map match math nat
    non_empty option process proof result semigroup sigma string supervisor
    system telescope test time tuple unit vector
  )

  # Rich modules that must emit a substantial function surface — guards against a
  # silent regression where emission "succeeds" but degrades to empty/hollow forms.
  @min_forms %{"list" => 20, "map" => 10, "string" => 15, "math" => 12, "result" => 8}

  defp dependent_codegen(name) do
    src = File.read!(Path.join("lib/std", name <> ".cure"))

    with {:ok, tokens} <- Lexer.tokenize(src, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false),
         {:ok, env, locals} <- Program.check_ast_with_locals(ast),
         {:ok, forms} <- Emit.compile_forms(env, Program.module_atom(ast), locals) do
      {:ok, forms}
    end
  end

  test "every dependent-green stdlib module lowers to BEAM forms via the dependent emitter" do
    failures =
      Enum.reduce(@green, [], fn name, acc ->
        result =
          try do
            dependent_codegen(name)
          rescue
            e -> {:raise, Exception.message(e)}
          catch
            kind, value -> {:raise, "#{inspect(kind)}: #{inspect(value)}"}
          end

        case result do
          {:ok, forms} when is_list(forms) -> acc
          other -> [{name, inspect(other, limit: 5)} | acc]
        end
      end)

    assert failures == [],
           "stdlib modules failed dependent emission (rip-out would break on these):\n" <>
             Enum.map_join(Enum.reverse(failures), "\n", fn {n, e} -> "  Std.#{n}: #{e}" end)
  end

  test "rich stdlib modules emit their full function surface (no hollow-emit regression)" do
    shortfalls =
      Enum.reduce(@min_forms, [], fn {name, floor}, acc ->
        {:ok, forms} = dependent_codegen(name)
        fun_count = Enum.count(forms, &match?({:function, _, _, _, _}, &1))
        if fun_count >= floor, do: acc, else: [{name, fun_count, floor} | acc]
      end)

    assert shortfalls == [],
           "stdlib modules emitted fewer function forms than expected:\n" <>
             Enum.map_join(shortfalls, "\n", fn {n, got, floor} ->
               "  Std.#{n}: emitted #{got} functions, expected >= #{floor}"
             end)
  end
end
