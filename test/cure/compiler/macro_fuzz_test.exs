defmodule Cure.Compiler.MacroFuzzTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.MacroFuzz
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program
  alias Cure.Core.{Context, Eval, Kernel}

  test "samples well-typed Core fillers for supported grammar categories" do
    for category <- ["Nat", "Bd", "Vec"] do
      assert {:ok, %{ctx: ctx, goal: goal}, terms} = MacroFuzz.sample_holes(category, 12, 19)
      goal_value = Eval.eval(goal, Context.env(ctx))

      assert length(terms) == 12
      assert Enum.all?(terms, &(Kernel.check(ctx, &1, goal_value) == :ok))
    end
  end

  test "unsupported grammar categories are reported as coverage gaps" do
    assert {:error, {:unsupported_hole_type, "UnknownCategory"}} =
             MacroFuzz.hole_generator("UnknownCategory")
  end

  test "surface categories use native literal and syntax-domain generators" do
    assert {:ok, %{domain: :number}, numbers} = MacroFuzz.sample_holes("Number", 12, 19)
    assert Enum.all?(numbers, fn term -> match?({:int_lit, _}, term) or match?({:float_lit, _}, term) end)

    assert {:ok, %{domain: :duration}, durations} = MacroFuzz.sample_holes("Duration", 12, 19)
    assert Enum.all?(durations, &match?({:int_lit, _}, &1))

    assert {:ok, %{domain: :code}, code} = MacroFuzz.sample_holes("Code", 12, 19)
    assert Enum.all?(code, &is_tuple/1)

    assert {:ok, %{domain: :expression}, expressions} =
             MacroFuzz.sample_holes("Expression", 12, 19)

    assert Enum.all?(expressions, &match?({:raw_text, _}, &1))

    assert {:ok, %{goal: {:type, 0}}, kinds} = MacroFuzz.sample_holes("Kind", 12, 19)
    assert Enum.all?(kinds, &match?({:data, _, _, _}, &1))
  end

  test "Expression fillers preserve complete ordinary expressions at use sites" do
    source = """
    macro Identity
      syntax identity <value: Expression> becomes value
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:macro_def, _, [rule]}} = Parser.parse(tokens, emit_events: false)

    assert {:ok, use_site} =
             MacroFuzz.assemble_use_site(rule, %{"value" => {:raw_text, "1 + 2 * 3"}})

    assert {:binary_op, outer_meta, [_, {:binary_op, inner_meta, _}]} =
             Parser.expand_example([rule], use_site)

    assert outer_meta[:operator] == :+
    assert inner_meta[:operator] == :*
  end

  test "module-aware generation resolves closed user enum categories" do
    assert {:ok, env} = Program.elaborate("mod M\n  type Flag = Off | On\n")
    assert {:ok, %{goal: {:data, :"M#Flag", [], []}}, terms} = MacroFuzz.sample_holes("Flag", 10, 23, env)
    goal_value = Eval.eval({:data, :"M#Flag", [], []}, Context.env(Context.empty(env)))

    assert Enum.all?(terms, &(Kernel.check(Context.empty(env), &1, goal_value) == :ok))
    assert Enum.all?(terms, &match?({:ctor, name, []} when name in [:"M#Off", :"M#On"], &1))
  end

  test "module-aware generation resolves nullary parameterized and indexed families" do
    assert {:ok, env} =
             Program.elaborate("""
             mod M
               type Dec = D | C
               type Ix(a: Type) indices (d: Dec)
                 empty : Ix(a, D)
             """)

    assert {:ok, %{goal: {:data, :"M#Ix", [{:data, :"Std.Nat#Nat", [], []}], [{:ctor, :"M#D", []}]}}, terms} =
             MacroFuzz.sample_holes("Ix", 4, 29, env)

    goal = {:data, :"M#Ix", [{:data, :"Std.Nat#Nat", [], []}], [{:ctor, :"M#D", []}]}

    assert Enum.all?(
             terms,
             &(Kernel.check(Context.empty(env), &1, Eval.eval(goal, Context.env(Context.empty(env)))) == :ok)
           )

    assert Enum.all?(terms, &match?({:ctor, :"M#empty", []}, &1))
  end

  test "category coverage reports module domains and open extensions" do
    assert {:ok, env} = Program.elaborate("mod M\n  type Flag = Off | On\n")

    source = """
    macro Extension
      open Flag
      syntax flag <value: Flag> is Flag becomes value
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:macro_def, _, _} = macro_def} = Parser.parse(tokens, emit_events: false)
    assert {:ok, report} = MacroFuzz.category_coverage(macro_def, env)

    assert report.complete?
    assert report.open_categories == ["Flag"]
    assert [%{category: "Flag", domain: :core, open: true, status: :supported}] = report.categories
  end

  test "category coverage names unsupported domains without hiding them" do
    source = "macro M\n  syntax m <value: Missing> becomes value\n"
    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:macro_def, _, _} = macro_def} = Parser.parse(tokens, emit_events: false)
    assert {:ok, report} = MacroFuzz.category_coverage(macro_def, Cure.Core.Env.empty())

    refute report.complete?
    assert [%{category: "Missing", status: :unsupported}] = report.unsupported
  end

  test "generated scalar fillers assemble into fully consumed macro uses" do
    source = """
    macro Inc
      syntax inc <n: Nat> becomes n + 1
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:macro_def, _, rules}} = Parser.parse(tokens, emit_events: false)
    rule = Enum.find(rules, &(&1[:kind] == :syntax))
    assert {:ok, _info, terms} = MacroFuzz.sample_holes("Nat", 8, 29)

    for term <- terms do
      assert {:ok, use_site} = MacroFuzz.assemble_use_site(rule, %{"n" => term})
      expansion = Parser.expand_example(rules, use_site)
      refute match?({:example_use_site_not_fully_consumed, _, _}, expansion)
      assert {:binary_op, _, _} = expansion
    end
  end

  test "a filler with no supported surface encoding is reported" do
    source = "macro M\n  syntax m <x: Nat> becomes x\n"
    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:macro_def, _, [rule]}} = Parser.parse(tokens, emit_events: false)

    assert {:error, {:unsupported_surface_filler, _}} =
             MacroFuzz.assemble_use_site(rule, %{"x" => {:global, :missing_surface}})
  end

  test "a well-typed expansion passes the generated proof batch" do
    source = """
    mod M
      macro Inc
        syntax inc <n: Nat> becomes n + 1
          example inc 0 expands 0 + 1
        explain
          Nat =>
            "expects a Nat"
          keyword "inc" =>
            "starts with inc"
    """

    assert {:ok, env} = Program.elaborate(source)
    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:container, _, children}} = Parser.parse(tokens, emit_events: false)
    {:macro_def, _, _} = macro_def = Enum.find(children, &match?({:macro_def, _, _}, &1))

    assert :ok = MacroFuzz.check_expansion_proof(macro_def, env, draws: 8, seed: 31)
  end

  test "generated proof assembles and checks multiple typed holes per rule" do
    source = """
    mod M
      macro Pair
        syntax pair <a: Nat> then <b: Nat> becomes a + b
          example pair 0 then 0 expands 0 + 0
        explain
          Nat =>
            "expects Nat operands"
          keyword "pair" =>
            "starts with pair"
          keyword "then" =>
            "separates the operands"
    """

    assert {:ok, env} = Program.elaborate(source)
    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:container, _, children}} = Parser.parse(tokens, emit_events: false)
    macro_def = Enum.find(children, &match?({:macro_def, _, _}, &1))
    assert :ok = MacroFuzz.check_expansion_proof(macro_def, env, draws: 8, seed: 41)
  end

  test "an ill-typed generated expansion is reported by the proof batch" do
    source = """
    mod M
      macro Bad
        syntax bad <n: Nat> becomes n + true
          example bad 0 expands 0 + true
        explain
          Nat =>
            "expects a Nat"
          keyword "bad" =>
            "starts with bad"
    """

    env_source =
      source
      |> String.replace("n + true", "n + 1")
      |> String.replace("0 + true", "0 + 1")

    assert {:ok, env} = Program.elaborate(env_source)
    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:container, _, children}} = Parser.parse(tokens, emit_events: false)
    {:macro_def, _, _} = macro_def = Enum.find(children, &match?({:macro_def, _, _}, &1))

    assert {:error, {:expansion_ill_typed, %{keyword: "bad", generated_term: generated, shrunk_term: {:ctor, :Z, []}}}} =
             MacroFuzz.check_expansion_proof(macro_def, env, draws: 8, seed: 31)

    assert is_tuple(generated)
  end

  test "a nullary all-erased-implicit global expansion passes the proof parametrically" do
    # `Std.Otp.self : {m: Type} -> Effect(Pid(m))` has an erased result index `m`
    # that cannot be solved use-site-free, so standalone elaboration reports it as
    # an unsolved metavariable. Because `m` is erased (computationally
    # irrelevant), the expansion is well-typed at a schematic type for every
    # instantiation, so the generative proof accepts it without a `contextual`
    # exemption.
    source = """
    mod M
      use Std.Otp
      macro Here
        syntax here becomes Std.Otp.self()
          example here expands Std.Otp.self()
        explain
          keyword "here" =>
            "returns the current process"
    """

    assert {:ok, env} = Program.elaborate(source)
    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:container, _, children}} = Parser.parse(tokens, emit_events: false)
    macro_def = Enum.find(children, &match?({:macro_def, _, _}, &1))

    assert :ok = MacroFuzz.check_expansion_proof(macro_def, env, draws: 1, seed: 7)
  end

  test "the parametric-erased guard discriminates by shape, arity, and erasure" do
    # `Std.Otp.self : {m: Type} -> Effect(Pid(m))` is the sole otp qualifier: one
    # erased parameter, applied nullary. Everything else must be rejected.
    assert {:ok, otp_env} = Program.elaborate("mod M\n  use Std.Otp\n")

    self_call = {:function_call, [name: "Std.Otp.self"], []}
    assert MacroFuzz.parametric_erased_call?(self_call, otp_env, :"Std.Otp#self")

    # Non-call expansion — the shape guard rejects it.
    refute MacroFuzz.parametric_erased_call?({:identifier, [], :x}, otp_env, :"Std.Otp#self")

    # A call that supplies an explicit argument — the arity guard rejects it,
    # because an argument subterm could hide a relevant unsolved metavariable.
    refute MacroFuzz.parametric_erased_call?(
             {:function_call, [name: "Std.Otp.self"], [{:int_lit, 0}]},
             otp_env,
             :"Std.Otp#self"
           )

    # A nullary call of a global with a present (unrestricted) parameter — the
    # erasure guard rejects it; parametric acceptance is scoped to erased
    # parameters alone.
    assert {:ok, twice_env} =
             Program.elaborate("mod M\n  use Std.Nat\n  fn twice(x: Nat) -> Nat = x\n")

    refute MacroFuzz.parametric_erased_call?(
             {:function_call, [name: "twice"], []},
             twice_env,
             :"M#twice"
           )

    # An unknown callee has no signature to prove erasure from — rejected.
    refute MacroFuzz.parametric_erased_call?(
             {:function_call, [name: "nope"], []},
             otp_env,
             :"M#nope"
           )
  end

  test "proof manifests list every rule and cache identical proof work" do
    source = """
    mod M
      macro Pair
        syntax a becomes 1
          example a expands 1
        syntax b becomes 2
          example b expands 2
        explain
          keyword "a" =>
            "starts with a"
          keyword "b" =>
            "starts with b"
    """

    assert {:ok, env} = Program.elaborate(source)
    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:container, _, children}} = Parser.parse(tokens, emit_events: false)
    macro_def = Enum.find(children, &match?({:macro_def, _, _}, &1))

    assert {:ok, %{cached?: false, rules: rules}} =
             MacroFuzz.proof_manifest(macro_def, env, draws: 1, seed: 37)

    assert Enum.map(rules, & &1.keyword) == ["a", "b"]
    assert Enum.all?(rules, &(&1.status == :passed))

    assert {:ok, %{cached?: true, rules: ^rules}} =
             MacroFuzz.proof_manifest(macro_def, env, draws: 1, seed: 37)
  end
end
