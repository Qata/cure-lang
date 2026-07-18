defmodule Cure.Compiler.WithParseTest do
  @moduledoc """
  `with`-abstraction (capability A) surface parsing. `with` is a CONTEXTUAL
  keyword: it is a with-abstraction only in expression-prefix position; its
  existing FSM/actor payload-binder identifier use is unaffected.
  """
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  defp parse(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    Parser.parse(toks, emit_events: false)
  end

  # Collect every {tag, meta, children} 3-tuple in the AST.
  defp collect(node, acc) do
    acc = if is_tuple(node) and tuple_size(node) == 3, do: [node | acc], else: acc

    cond do
      is_tuple(node) -> Enum.reduce(Tuple.to_list(node), acc, &collect/2)
      is_list(node) -> Enum.reduce(node, acc, &collect/2)
      true -> acc
    end
  end

  test "block-form `with e <arms>` parses to a :with_abs node" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      fn foo(n: Nat) -> Nat =
        with n
          Z() -> Z()
          S(k) -> S(k)
    """

    assert {:ok, ast} = parse(src)

    node =
      collect(ast, [])
      |> Enum.find(fn t -> match?({:with_abs, _, [_ | _]}, t) end)

    assert {:with_abs, _meta, [scrut | arms]} = node
    assert {:variable, _, "n"} = scrut
    assert length(arms) == 2
    assert Enum.all?(arms, &match?({:match_arm, _, [_]}, &1))
  end

  test "`with e proof p <arms>` carries the proof name in meta (capability B)" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      fn foo(n: Nat) -> Nat =
        with n proof pf
          Z() -> Z()
          S(k) -> S(k)
    """

    assert {:ok, ast} = parse(src)

    node =
      collect(ast, [])
      |> Enum.find(fn t -> match?({:with_abs, _, [_ | _]}, t) end)

    assert {:with_abs, meta, [scrut | arms]} = node
    assert {:variable, _, "n"} = scrut
    assert Keyword.get(meta, :proof) == "pf"
    assert length(arms) == 2
  end

  test "`proof` after a call scrutinee is not consumed as another scrutinee" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      fn g(n: Nat) -> Nat = n
      fn foo(n: Nat) -> Nat =
        with g(n) proof pf
          Z() -> Z()
          S(k) -> S(k)
    """

    assert {:ok, ast} = parse(src)

    node =
      collect(ast, [])
      |> Enum.find(fn t -> match?({:with_abs, _, [_ | _]}, t) end)

    assert {:with_abs, meta, [{:function_call, call_meta, _args} | arms]} = node
    assert Keyword.get(call_meta, :name) == "g"
    assert Keyword.get(meta, :proof) == "pf"
    assert length(arms) == 2
  end

  test "no-proof `with` leaves :proof absent in meta (capability A unchanged)" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      fn foo(n: Nat) -> Nat =
        with n
          Z() -> Z()
          S(k) -> S(k)
    """

    assert {:ok, ast} = parse(src)

    node =
      collect(ast, [])
      |> Enum.find(fn t -> match?({:with_abs, _, [_ | _]}, t) end)

    assert {:with_abs, meta, _} = node
    assert Keyword.get(meta, :proof) == nil
  end

  # -- LHS re-matching (Idris-parity indexed views) --------------------------
  #
  # A with-clause may RESTATE the parent function's LHS patterns (refined) before
  # the with-pattern, separated by `|`:  `<parent-pat…> | <with-pat> -> body`.
  # Such an arm parses to a distinct `{:with_rematch_arm, meta, [body]}` node
  # carrying `:parent_patterns` and `:pattern` in meta. A clause WITHOUT the
  # `… |` prefix stays the ordinary no-rematch `{:match_arm}`.
  test "block-form `with` clause restating a single parent pattern parses to :with_rematch_arm" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      type NV = VZ | VS(Nat)
      fn foo(n: Nat) -> Nat =
        with view(n)
          S(m) | VS(m) -> S(m)
          Z() | VZ() -> Z()
    """

    assert {:ok, ast} = parse(src)

    node =
      collect(ast, [])
      |> Enum.find(fn t -> match?({:with_abs, _, [_ | _]}, t) end)

    assert {:with_abs, _meta, [scrut | arms]} = node
    assert {:function_call, _, _} = scrut
    assert length(arms) == 2
    assert Enum.all?(arms, &match?({:with_rematch_arm, _, [_]}, &1))

    [{:with_rematch_arm, m1, [_body1]} | _] = arms
    # First arm: parent pattern `S(m)`, with-pattern `VS(m)`.
    assert [{:function_call, pm, _}] = Keyword.fetch!(m1, :parent_patterns)
    assert Keyword.get(pm, :name) == "S"
    assert {:function_call, wm, _} = Keyword.fetch!(m1, :pattern)
    assert Keyword.get(wm, :name) == "VS"
  end

  test "block-form `with` clause restating multiple (comma-sep) parent patterns" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      type NV = VZ | VS(Nat)
      fn foo(n: Nat, w: Nat) -> Nat =
        with view(n)
          S(m), w | VS(m) -> S(m)
          Z(), w | VZ() -> w
    """

    assert {:ok, ast} = parse(src)

    node =
      collect(ast, [])
      |> Enum.find(fn t -> match?({:with_abs, _, [_ | _]}, t) end)

    assert {:with_abs, _meta, [_scrut | arms]} = node
    assert length(arms) == 2
    [{:with_rematch_arm, m1, _} | _] = arms
    pps = Keyword.fetch!(m1, :parent_patterns)
    assert length(pps) == 2
    assert [{:function_call, pm, _}, {:variable, _, "w"}] = pps
    assert Keyword.get(pm, :name) == "S"
  end

  test "no-rematch `with` clause (no `|` prefix) stays a :match_arm" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      fn foo(n: Nat) -> Nat =
        with n
          Z() -> Z()
          S(k) -> S(k)
    """

    assert {:ok, ast} = parse(src)

    node =
      collect(ast, [])
      |> Enum.find(fn t -> match?({:with_abs, _, [_ | _]}, t) end)

    assert {:with_abs, _meta, [_scrut | arms]} = node
    assert Enum.all?(arms, &match?({:match_arm, _, [_]}, &1))
    refute Enum.any?(arms, &match?({:with_rematch_arm, _, _}, &1))
  end

  # Regression: `with` remains the actor payload binder while the macro expands
  # to an ordinary lifted module.
  test "`actor Name with Payload` preserves the payload in transparent syntax" do
    src = """
    actor Counter with 0
      fn initial_state() -> Int = 0
    """

    assert {:ok, ast} = parse(src)

    node =
      collect(ast, [])
      |> Enum.find(fn t -> match?({:lift_module, _, _}, t) end)

    assert {:lift_module, meta, []} = node
    assert Keyword.get(meta, :module) == "Counter"

    assert Enum.any?(Keyword.get(meta, :declarations), fn
             {:function_def, fn_meta, _body} -> Keyword.get(fn_meta, :name) == "start_link"
             _ -> false
           end)
  end

  # The test above only checks the PARSE-level AST for `start_link` (always
  # present via the template itself); it never checks that the user's own
  # `body` declaration (`initial_state`) survives, nor that the actor actually
  # compiles and runs. The `Declarations until dedent` body-splice mechanism
  # (rule 212 in Std.Actor's `ActorContainers`) is what carries that body
  # through; pin its real, end-to-end claim here. Note: the raw
  # `becomes lift module name` template requires an already-qualified
  # `Cure.`-prefixed name (a pre-existing, unrelated convention — see
  # `qualify_module_name`/`macro_module_marker` in parser.ex), so this uses a
  # qualified name rather than the bare "Counter" above.
  test "`actor Name with Payload <body>` compiles and the spliced body fn is callable" do
    src = """
    actor Cure.Generated.WithBodySpliceProbe with 0
      fn initial_state() -> Int = 0
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(module, :initial_state, []) == 0
  end

  # An EMPTY body must splice nothing rather than crash the `{:declarations_block,
  # _, stmts}` -> `{:raw_splice, stmts}` mechanism (rule 212: `stmts == []`).
  test "`actor Name with Payload` with an empty body compiles (empty splice, no crash)" do
    src = """
    actor Cure.Generated.WithEmptyBodySpliceProbe with 0
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(src, emit_events: false)
  end

  # A body with MULTIPLE declarations must splice all of them flat into the
  # enclosing declarations list (rule 224, the bare/no-`with` form).
  test "bare `actor Name <body>` splices multiple body declarations flat and all are callable" do
    src = """
    actor Cure.Generated.BareMultiDeclSpliceProbe
      fn a() -> Int = 1
      fn b() -> Int = 2
      fn c() -> Int = 3
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert apply(module, :a, []) == 1
    assert apply(module, :b, []) == 2
    assert apply(module, :c, []) == 3
  end

  # ---- Multiple-with surface sugar -----------------------------------------

  # `with e1 e2 <arms>` (space-separated scrutinees, comma-separated arm
  # patterns) is SUGAR for nested single-scrutinee `:with_abs`. This test pins
  # the desugared AST shape so it is verified independently of elaboration.
  test "multi-scrutinee `with e1 e2` desugars to nested :with_abs" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      fn foo(a: Nat, b: Nat) -> Nat =
        with g(a) g(b)
          Z(), Z() -> Z()
          Z(), S(k) -> S(k)
          S(j), Z() -> S(j)
          S(j), S(k) -> S(k)
    """

    assert {:ok, ast} = parse(src)

    # Outermost with_abs: the one whose scrutinee is `g(a)`.
    outer =
      collect(ast, [])
      |> Enum.find(fn
        {:with_abs, _, [{:function_call, m, [{:variable, _, "a"}]} | _]} ->
          Keyword.get(m, :name) == "g"

        _ ->
          false
      end)

    assert {:with_abs, _meta, [outer_scrut | outer_arms]} = outer
    assert {:function_call, gm, [{:variable, _, "a"}]} = outer_scrut
    assert Keyword.get(gm, :name) == "g"

    # Two distinct first patterns Z() and S(j) → two grouped outer arms.
    assert length(outer_arms) == 2

    assert [{:match_arm, m0, [inner0]}, {:match_arm, m1, [inner1]}] = outer_arms
    assert {:function_call, p0m, []} = Keyword.get(m0, :pattern)
    assert Keyword.get(p0m, :name) == "Z"
    assert {:function_call, p1m, [{:variable, _, "j"}]} = Keyword.get(m1, :pattern)
    assert Keyword.get(p1m, :name) == "S"

    # Each outer arm body is an inner with_abs over `g(b)` with two arms.
    for inner <- [inner0, inner1] do
      assert {:with_abs, _, [{:function_call, bm, [{:variable, _, "b"}]} | inner_arms]} = inner
      assert Keyword.get(bm, :name) == "g"
      assert length(inner_arms) == 2
      assert Enum.all?(inner_arms, &match?({:match_arm, _, [_]}, &1))
    end
  end

  # Multiple-with combined with an LHS re-match (`| pat`) is out of scope in the
  # first slice and must be a clean parse error, not a silent mis-parse.
  test "multi-scrutinee with-arm + LHS rematch is rejected" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      fn foo(a: Nat, b: Nat) -> Nat =
        with g(a) g(b)
          Z(), Z() | Z() -> Z()
    """

    assert {:error, errors} = parse(src)
    assert Enum.any?(errors, &match?({:with_multi_rematch_unsupported, _, _}, &1))
  end

  # Two arms whose first pattern shares a constructor head but differs in
  # sub-structure (`S(j)` vs `S(m)`) would need variable renaming to share an
  # outer branch; the first slice rejects this rather than mis-bind.
  test "multi-scrutinee inconsistent shared-head first patterns are rejected" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      fn foo(a: Nat, b: Nat) -> Nat =
        with g(a) g(b)
          S(j), Z() -> S(j)
          S(m), S(k) -> S(k)
    """

    assert {:error, errors} = parse(src)
    assert Enum.any?(errors, &match?({:with_multi_inconsistent_pattern, _, _}, &1))
  end
end
