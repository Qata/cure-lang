defmodule Cure.Elab.CanonicalDefinitionIdentityTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Emit, Name, Program}

  test "local helper identities and Core calls are canonical in either declaration order" do
    bodies = [
      "local fn same() -> Int = 1\n  local fn matches() -> Int = same()",
      "local fn matches() -> Int = same()\n  local fn same() -> Int = 1"
    ]

    for body <- bodies do
      source = "mod RegexFixture\n  #{body}\n  fn run() -> Int = matches()\nend\n"
      {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
      {:ok, ast} = Parser.parse(tokens, emit_events: false)
      assert {:ok, env, locals} = Program.check_ast_with_locals(ast)

      assert MapSet.new(locals) ==
               MapSet.new([
                 :"RegexFixture#same",
                 :"RegexFixture#matches",
                 :"RegexFixture#run"
               ])

      assert %{body: matches_body} = Map.fetch!(env.defs, :"RegexFixture#matches")
      assert contains_term?(matches_body, {:global, :"RegexFixture#same"})
      refute contains_term?(matches_body, {:global, :same})

      reachable = Program.reachable_def_names(env, [:run])

      assert reachable == [
               :"RegexFixture#matches",
               :"RegexFixture#run",
               :"RegexFixture#same"
             ]

      assert Enum.all?(reachable, &Map.has_key?(env.defs, &1))
      assert Enum.all?(reachable, &Name.qualified?/1)

      module = :"Cure.Test.RegexFixture#{System.unique_integer([:positive])}"
      assert {:ok, ^module} = Emit.compile_and_load(env, module: module, functions: reachable)
      assert apply(module, :run, []) == 1
    end
  end

  # `run` is also the bare spelling of a kernel builtin op (`:effect_run`, seeded
  # by `Cure.Core.Builtins.seed_run/1` alongside the 32 arithmetic ops). Builtin
  # ops are body-less and are never emitted as function forms, so if an authored
  # root spelling resolves to the ambient bare key instead of to this module's own
  # canonical one, the function silently drops out of the emission set — the
  # module compiles to a BEAM form that does not contain it.
  #
  # A local definition shadows an ambient one everywhere else in the language;
  # selecting an emission root by authored spelling has to obey the same rule.
  test "a local definition whose name matches a builtin op still emits" do
    source = """
    mod BuiltinNameShadow
      fn run() -> Int = 41
      fn start() -> Int = run() + 1
    end
    """

    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    assert {:ok, env, _locals} = Program.check_ast_with_locals(ast)

    # Selected by the colliding spelling itself, which is where the ambient key
    # wins: a builtin-op def is body-less, so `collect_reachable/4` returns
    # without recording anything and the root vanishes.
    assert Program.reachable_def_names(env, [:run]) == [:"BuiltinNameShadow#run"]

    reachable = Program.reachable_def_names(env, [:run, :start])

    assert reachable == [
             :"BuiltinNameShadow#run",
             :"BuiltinNameShadow#start"
           ]

    module = :"Cure.Test.BuiltinNameShadow#{System.unique_integer([:positive])}"

    assert {:ok, ^module} = Emit.compile_and_load(env, module: module, functions: reachable)

    assert apply(module, :start, []) == 42
    assert apply(module, :run, []) == 41
  end

  test "reachability never guesses a bare Core edge from a matching suffix" do
    env =
      Cure.Core.Env.empty()
      |> Cure.Core.Env.with_owner("Fixture")
      |> Cure.Core.Env.add_def(:same, {:int_type}, {:int_lit, 1})
      |> Cure.Core.Env.add_def(:run, {:int_type}, {:global, :same})

    assert Program.reachable_def_names(env, [:run]) == [:"Fixture#run"]

    assert {:error, {:emission_closure_missing, %{definition: :same, referenced_by: :"Fixture#run", module: "Fixture"}}} =
             Emit.compile_forms(env, :Fixture, [:"Fixture#run"])
  end

  defp contains_term?(term, wanted) when term == wanted, do: true

  defp contains_term?(term, wanted) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.any?(&contains_term?(&1, wanted))

  defp contains_term?(term, wanted) when is_list(term),
    do: Enum.any?(term, &contains_term?(&1, wanted))

  defp contains_term?(_term, _wanted), do: false
end
