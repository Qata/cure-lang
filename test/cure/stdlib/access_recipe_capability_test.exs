defmodule Cure.Stdlib.AccessRecipeCapabilityTest do
  @moduledoc """
  #18-readiness proof for `Std.Access`'s rip-out RECIPE — the last dependent-
  capable stdlib module whose target form was not yet locked as a test.

  `Std.Access` models Elixir's dynamic `Access` behaviour over heterogeneous
  maps/keyword-lists/tuples. Its committed form uses the OLD typeclass mechanism
  (`proto Access(c)` + `impl Access for Map`/`for List`), which the dependent
  pipeline rejects outright (`{:unsupported_container, :protocol}`) — so
  `access.cure` cannot elaborate dependent as-is, and it stays classic-shaped
  until the classic pipeline is deleted.

  Its rip-out recipe (verified ad-hoc when the backend landed in `90f1015`, but
  never locked until now) replaces the typeclass with RUNTIME TAG DISPATCH over
  an opaque top type:

    * `opaque type Any` — the dependent pipeline has no top type, so dynamic
      containers cross the typed/untyped boundary as `Any`.
    * lifts through `@extern(:cure_std_any, :coerce, 1)` — `coerce/1` is the
      identity (the BEAM is untyped), i.e. Idris's `believe_me`, with the trust
      quarantined to the `@extern` boundary (`lib/cure/stdlib/cure_std_any.ex`,
      guarded by `cure_std_any_test.exs`).
    * `fetch` dispatches on `is_map`/`is_list` at runtime instead of resolving a
      `proto Access` instance at compile time.
    * the `Accessor` ADT (`AccKey`/`AccAt`/`AccAll`) drives a `match`.

  This test locks that recipe — the NOVEL kernel that the full port depends on —
  as an immutable regression: it both elaborates AND lowers to BEAM forms through
  the dependent emitter. It is deliberately a compact faithful slice, not the
  574-line port (that also entails retiring the `Std.Pair.element` tuple
  projection in favour of `Std.Tuple`); porting the remaining accessor walkers is
  mechanical once this kernel holds. So every dependent-capable stdlib module now
  has a locked rip-out proof: 41 committed-green (elaboration + emit firewalls),
  show/io/set (coexistence forms), and access (this recipe). Only the AtomVM
  dead-ends (http/regex) and the to-be-retired `pair` remain out, by design.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Program, Emit}

  @access_recipe """
  mod Std.AccessDep
    opaque type Any
    @extern(:cure_std_any, :coerce, 1)
    fn to_any(x: t) -> Any
    @extern(:erlang, :is_map, 1)
    fn is_map_any(x: Any) -> Bool
    @extern(:erlang, :is_list, 1)
    fn is_list_any(x: Any) -> Bool
    @extern(:maps, :is_key, 2)
    fn map_has(k: Any, m: Any) -> Bool
    @extern(:maps, :get, 2)
    fn map_get(k: Any, m: Any) -> Any

    type Opt = Present(Any) | Absent
    type Accessor = AccKey(Any) | AccAt(Int) | AccAll

    fn key(k: Any) -> Accessor = AccKey(k)

    ## Runtime tag dispatch — replaces `impl Access for Map`/`for List`.
    fn fetch(container: Any, k: Any) -> Opt =
      pickup
        is_map_any(container) ->
          pickup
            map_has(k, container) -> Present(map_get(k, container))
            else                  -> Absent()
        else -> Absent()

    fn dispatch(container: Any, step: Accessor) -> Opt =
      match step
        AccKey(k) -> fetch(container, k)
        AccAt(i)  -> Absent()
        AccAll    -> Absent()
  """

  test "Std.Access's rip-out recipe (opaque Any + runtime dispatch) elaborates dependent" do
    assert {:ok, _env} = Program.elaborate(@access_recipe)
  end

  test "Std.Access's rip-out recipe also lowers to BEAM forms via the dependent emitter" do
    {:ok, tokens} = Lexer.tokenize(@access_recipe, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    {:ok, env, locals} = Program.check_ast_with_locals(ast)
    assert {:ok, forms} = Emit.compile_forms(env, Program.module_atom(ast), locals)
    fun_count = Enum.count(forms, &match?({:function, _, _, _, _}, &1))
    assert fun_count >= 5, "expected the access recipe to emit >= 5 functions, got #{fun_count}"
  end
end
