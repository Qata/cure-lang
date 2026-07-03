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

  # Regression: `with` is still the FSM/actor payload-binder identifier.
  test "`actor Name with Payload` still parses (with-abstraction is contextual)" do
    src = """
    actor Counter with 0
      on_message
        (:inc, n) -> n + 1
    """

    assert {:ok, ast} = parse(src)

    node =
      collect(ast, [])
      |> Enum.find(fn t -> match?({:container, _, _}, t) end)

    assert {:container, meta, _body} = node
    assert Keyword.get(meta, :container_type) == :actor
    # The payload came from the `with 0` clause.
    assert {:literal, lit_meta, 0} = Keyword.get(meta, :init)
    assert Keyword.get(lit_meta, :subtype) == :integer
  end
end
