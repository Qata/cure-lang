defmodule Cure.Stdlib.DependentEmitRuntimeTest do
  @moduledoc """
  #18-readiness firewall, RUNTIME tier — the strongest of the three. The
  elaboration firewall proves stdlib modules type-check on the dependent
  pipeline; the emit firewall proves they lower to BEAM forms. Neither proves the
  emitted code actually WORKS: well-typed, well-formed forms can still be
  runtime-wrong (a mis-erased constructor tag, a wrong arity, an off-by-one in a
  recursive lowering). This tier emits each module through the dependent pipeline,
  LOADS the BEAM, and RUNS its functions, asserting concrete results.

  It locks in the actual post-rip-out runtime behavior, including the canonical
  constructor representation: the OTP-conventional `Option`/`Result` constructors
  erase to lowercase BEAM tags (`some(42) == {:some, 42}`, `none() == :none`,
  `ok(7) == {:ok, 7}`, `error(:bad) == {:error, :bad}`) so a Cure value is a
  native OTP term that Erlang/Elixir and AtomVM FFI consume directly. Non-OTP
  constructors keep their declared (PascalCase) tag; records stay tagged tuples.

  The chosen modules are self-contained (no cross-module runtime dependency that
  would need separate loading): `option`/`result` exercise the ADT tag
  representation, `math` a pure-value `@extern` surface, `list` recursion + list
  externs, `bool` boolean logic. Together they show the dependent emitter yields
  correct runnable code across the shapes the stdlib is built from.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Program, Emit}

  # Emit `lib/std/<name>.cure` through the dependent pipeline and load the BEAM,
  # returning the loaded module atom.
  defp load_std(name) do
    src = File.read!(Path.join("lib/std", name <> ".cure"))
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    {:ok, env, locals} = Program.check_ast_with_locals(ast)
    {:ok, mod} = Emit.compile_and_load(env, module: Program.module_atom(ast), functions: locals)
    mod
  end

  test "Std.Option runs correctly with the dependent constructor representation" do
    m = load_std("option")
    some = apply(m, :some, [42])
    none = apply(m, :none, [])

    assert some == {:some, 42}
    assert none == :none
    assert apply(m, :is_some, [some]) == true
    assert apply(m, :is_none, [none]) == true
    assert apply(m, :unwrap, [some, 0]) == 42
    assert apply(m, :unwrap, [none, 99]) == 99
  end

  test "Std.Result runs correctly with the dependent constructor representation" do
    m = load_std("result")
    ok = apply(m, :ok, [7])
    err = apply(m, :error, [:bad])

    assert ok == {:ok, 7}
    assert err == {:error, :bad}
    assert apply(m, :is_ok, [ok]) == true
    assert apply(m, :is_error, [err]) == true
    assert apply(m, :unwrap, [ok, 0]) == 7
    assert apply(m, :unwrap, [err, 0]) == 0
  end

  test "Std.Math (pure @extern surface) runs correctly via the dependent emitter" do
    m = load_std("math")
    assert apply(m, :abs, [-5]) == 5
    assert apply(m, :max, [3, 7]) == 7
    assert apply(m, :min, [3, 7]) == 3
  end

  test "Std.List (recursion + list externs) runs correctly via the dependent emitter" do
    m = load_std("list")
    assert apply(m, :length, [[1, 2, 3]]) == 3
    assert apply(m, :reverse, [[1, 2, 3]]) == [3, 2, 1]
  end

  test "Std.Bool (boolean logic) runs correctly via the dependent emitter" do
    m = load_std("bool")
    assert apply(m, :and, [true, false]) == false
    assert apply(m, :and, [true, true]) == true
    assert apply(m, :not, [false]) == true
  end
end
