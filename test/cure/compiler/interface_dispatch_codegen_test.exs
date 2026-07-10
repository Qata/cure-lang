defmodule Cure.Compiler.InterfaceDispatchCodegenTest do
  @moduledoc """
  Classic codegen predates the `interface`/`implementation` surface (the
  successor to `proto`/`impl`). It had no handling for the new container
  tags and silently dropped them — so a top-level helper that dispatches
  an interface method (`compare(a, b)`) referenced a function classic never
  emitted, and the module failed `erl_lint` with `undefined_function`.

  Until the classic pipeline is removed (#18), the new surface normalizes
  onto classic's existing `:protocol`/`:trait` dispatcher machinery. This is
  an end-to-end check: an interface + implementation + a top-level derived
  helper must compile through to a loadable BEAM binary.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Codegen, Lexer, Parser}

  @src """
  mod IfaceDispatch
    interface Ordf(t)
      fn cmp(a: t, b: t) -> Bool

    implementation Ordf for Int
      fn cmp(a: Int, b: Int) -> Bool = a < b

    fn strictly_before(a: t, b: t) -> Bool where Ordf(t) = cmp(a, b)
  end
  """

  test "a top-level helper dispatching an interface method compiles to loadable BEAM" do
    {:ok, toks} = Lexer.tokenize(@src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    {:ok, forms, _warnings} = Codegen.compile_module(ast, emit_events: false)

    # `:compile.forms` runs erl_lint; a dropped interface leaves `cmp`
    # undefined and this returns `{:error, ...}`.
    assert {:ok, _mod, _bin} = :compile.forms(forms, [:return_errors])
  end
end
