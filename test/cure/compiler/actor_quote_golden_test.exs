# test/cure/compiler/actor_quote_golden_test.exs
#
# SP5.1 Stage 5 — byte-identical-Core gate for the quasiquotation port.
#
# `derive_actor` and its helpers in lib/std/actor.cure are being rewritten from
# hand-built `Std.Syntax` builders to `quote`/`$( )`. The port is a pure
# refactor: the SAME generated GenServer module must come out. These goldens
# freeze the compiled BEAM of three representative generated modules, captured
# from the pre-port build (HEAD). Each module exercises a different slice of the
# expander:
#
#   * GDerived        — `derive` path: default_actor_init + actor_handler arms
#   * GStructuredCall — structured `on_call`: reply channel + handle_call
#   * GLifecycle      — optional terminate / code_change callback bodies
#   * GFsmDerived     — derive_fsm: callback_mode + init callback bodies
#   * GSup            — derive_supervisor: init %[:ok, %[strategy, children]]
#   * GApp            — derive_application: stop / start_phase :ok bodies
#
# If a hash here changes, the port altered the generated program — that is the
# failure this gate exists to catch. The ONLY legitimate reason to re-freeze is
# an intentional, separately-reviewed change to codegen or an OTP major bump
# that reshapes BEAM encoding; in that case recapture all three together and say
# so in the commit.
#
# Re-frozen for Task 2.6 (Equatable/Comparable as the sole route to `==`/`<`,
# with structural `Equatable` auto-derived for ADTs lacking a hand-written
# instance). GDerived, GStructuredCall, GFsmDerived and GLifecycle each declare
# their own message/event ADT (ActorMessage / ActorRequest / FsmEvent), so each
# now OWNS and emits exactly one auto-derived structural-equality method
# (`__impl_Equatable_<Module>#<Type>_==/2`) — an intentional codegen addition,
# verified as a single owned instance (not ambient bloat). The modules with no
# ADT of their own (Raw01/Raw15/Raw16, GSup, GApp) stay byte-identical: making
# Std.Equatable/Std.Comparable `@prelude` no longer duplicates their ~two dozen
# ambient instances into every consumer — owner-qualified instances now emit once
# in their owning module and are reached by remote call (see `check_ast_with_locals`).
defmodule Cure.Compiler.ActorQuoteGoldenTest do
  use ExUnit.Case, async: false

  @samples [
    {"GDerived",
     """
     mod M
       use Std.Actor
       use Std.Otp

       actor Cure.Generated.GDerived state Int derive
         match message
           Inc -> 1

     fn make_message() -> ActorMessage = Inc
     """,
     "1f4c7ab23e3d786a5d7cf3b2feebb7b7bd5e2431c69f5875b2dea54c92995bef"},
    {"GStructuredCall",
     """
     mod M
       use Std.Actor

       actor Cure.Generated.GStructuredCall
         state Int
         on_cast
           Inc -> state + 1
         on_call
           Read -> state

     fn make_request() -> ActorRequest = Read
     """,
     "186928fe2d506b59861830ca6355c1ded20654001245c52dd9436ff90a4b2fe7"},
    {"GFsmDerived",
     """
     mod M
       use Std.Fsm

       fsm Cure.Generated.GFsmDerived state Int derive
         match event
           Start -> :keep_state_and_data
           Stop -> :keep_state_and_data

     fn make_start() -> FsmEvent = Start
     """,
     "00ca03d11ed09b7c5fb68b7be8cab8128c90e3997a3001b942df9bfdb6bb3d74"},
    {"GSup",
     """
     mod M
       use Std.Supervisor

       sup Cure.Generated.GSup
         children []
     """,
     "c946d1c98c57efe5fc692ecad9c313ff11da59893f6cdad3cd2b06990d2c9818"},
    {"GApp",
     """
     mod M
       use Std.App

       app Cure.Generated.GApp
         root Cure.Generated.GSup
     """,
     "0fc99d391075931aa2c59ec052462675d4f45a754d10ebf45403601355699dfa"},
    {"GLifecycle",
     """
     mod M
       use Std.Actor

       actor Cure.Generated.GLifecycle
         state Int
         on_cast
           Inc -> state + 1
         terminate :shutdown
         code_change %[:ok, state + 1]
     """,
     "d9764518758cb4e3499b6bbdf95167b07c53909b2afd79eadd0441c68350df24"},
    # --- Raw Gen A characterization goldens (consolidation safety net) ---
    # Each freezes the compiled BEAM of one legacy `becomes lift module name`
    # raw-callback template (lib/std/actor.cure). They exist so the 1e
    # consolidation of the 16 positional templates into one unified-family raw
    # branch can be proven byte-identical. The L177 form (`initial` + `handle_cast`
    # with no `state`) is intentionally absent: it is dead code that fails to
    # compile on this tree (polymorphic state var never pinned) and is used by no
    # test or demo, so the consolidation drops it rather than reproducing it.
    {"Raw01_call_returns",
     """
     actor Cure.Generated.Raw01_call_returns state Int call Int returns Bool
       %[:reply, true, state]
     """,
     "81bd23b8b6f2b2c42a27df88fdabe29aa6fa859f6d667f917a8b67f0f5f609ee"},
    # Raw02_init (`actor N state T init <body>`) has been FOLDED into the shared
    # `emit_raw_state_init` → `derive_actor_family` emitter (§1e mechanism A) via
    # the `computed directly by` multi-arg input path. Per the corrected spec
    # (d1aec7b4) the raw fold is a behavioral-equivalence guarantee, NOT
    # byte-identical: the computed family branch legitimately reshapes the BEAM
    # (the folded `derive_actor_init(init: Some)` emits `init(args: Atom)` with a
    # 0-arg `start_link`, vs the template's `init(initial: State)` — the init/1
    # return value is identical regardless of the argument). Its byte-identical
    # golden therefore retires; behavioral equivalence (init/1 returns the spliced
    # result for any start argument) is pinned by "terse init template routes
    # through the shared family raw emitter" in actor_family_raw_test.exs.
    # Raw03_terminate (`actor N state T terminate <body>`) and Raw04_code_change
    # (`actor N state T code_change <body>`) have been FOLDED into the shared
    # `emit_raw_state_terminate` / `emit_raw_state_code_change` → derive_actor_family
    # emitters (§1e mechanism A) via the `computed directly by` multi-arg input
    # path. Per the corrected spec (d1aec7b4) the raw fold is a behavioral-
    # equivalence guarantee, NOT byte-identical: the computed family branch
    # legitimately reshapes the BEAM (callbacks split into meta the template folds
    # differently). Their byte-identical goldens therefore retire; behavioral
    # equivalence (terminate/2 and code_change/3 return the spliced result verbatim)
    # is pinned by "terse terminate/code_change template routes through the shared
    # family raw emitter" in actor_family_raw_test.exs.
    # Raw05_state_messages_cast (`actor N state T messages M handle_cast <body>`)
    # has been FOLDED into the shared `emit_raw_state_messages_cast` →
    # `derive_actor_family` emitter (§1e mechanism A) via the `computed directly
    # by` multi-arg input path. Per the corrected spec (d1aec7b4) the raw fold is a
    # behavioral-equivalence guarantee, NOT byte-identical: the computed family
    # branch legitimately reshapes the BEAM. Its byte-identical golden therefore
    # retires; behavioral equivalence (State/Message type-checking + pickup
    # dispatch) is pinned by the immutable container_macro_test:186/204 and by
    # "terse messages template routes through the shared family raw emitter" in
    # actor_family_raw_test.exs.
    # Raw06_state_cast (`actor N state T handle_cast <body>`) has been FOLDED into
    # the shared `emit_raw_state_cast` → `derive_actor_family_raw` emitter (§1e
    # mechanism A). Per the corrected spec (d1aec7b4) the raw fold is a
    # behavioral-equivalence guarantee, NOT byte-identical: the computed family
    # branch legitimately reshapes the BEAM, and the folded form now requires
    # `use Std.Actor` in scope (a computed rule resolves its elaborator, unlike a
    # bare Tier-2 template). Its byte-identical golden therefore retires; behavioral
    # equivalence is pinned by "terse template form routes through the shared family
    # raw emitter" in actor_family_raw_test.exs.
    # Raw07_state_initial_cast (`actor N state T initial <p> handle_cast <body>`) and
    # Raw08_state_initial_messages_cast (`... initial <p> messages <M> handle_cast
    # <body>`) have been FOLDED into the shared emit_raw_state_initial_cast /
    # emit_raw_state_initial_messages_cast → derive_actor_family emitters (§1e
    # mechanism A) via the `computed directly by` multi-arg input path. Per the
    # corrected spec (d1aec7b4) the raw fold is a behavioral-equivalence guarantee,
    # NOT byte-identical: the folded `initial: Some` path emits `init(args: Atom) =
    # %[:ok, payload]` with a nullary start_link passing `:unit`, vs the template's
    # `init(initial: State)` + `start_link() = beam_ops start_link name [payload]`
    # (both ignore the init arg and yield the seeded payload). Their byte-identical
    # goldens therefore retire; behavioral equivalence (init/1 returns the seeded
    # payload, handle_cast/pickup spliced verbatim) is pinned by "terse initial+
    # handle_cast / initial+messages+handle_cast template routes through the shared
    # family raw emitter" in actor_family_raw_test.exs.
    # Raw10_bare_cast (STATELESS `actor N handle_cast <body>`) has been FOLDED into
    # the shared emit_raw_cast_stateless → derive_actor_family_raw_stateless emitter
    # (§1e mechanism A, state-poly path) via the `computed directly by` multi-arg
    # input path. This is the first fold to route through the state-polymorphic
    # emitter (emit_actor_parts_poly_state + gen_server_module_raw): the stateless
    # form keeps the state a free type var `p` and emits NO `typealias State`, so a
    # uniform State alias cannot be used. Per the corrected spec (d1aec7b4) the raw
    # fold is a behavioral-equivalence guarantee, NOT byte-identical: the folded
    # family path emits Effect-wrapped default callbacks and DROPS the template's
    # default handle_call (matching every other folded raw form), legitimately
    # reshaping the BEAM. Its byte-identical golden therefore retires; behavioral
    # equivalence (init/1 seeds the state, start_link/1 starts, handle_cast body
    # spliced verbatim, :sys.get_state reflects the seed) is pinned by "bare
    # stateless handle_cast template routes through the poly-state family raw
    # emitter" in actor_family_raw_test.exs, and by container_macro_test:213
    # (Cure.PolymorphicCast).
    # Raw11_state_messages_info (`actor N state T messages <M> handle_info <body>`)
    # and Raw12_state_info (`... state T handle_info <body>`) have been FOLDED into
    # the shared emit_raw_state_messages_info / emit_raw_state_info →
    # derive_actor_family emitters (§1e mechanism A) via the `computed directly by`
    # multi-arg input path. Per the corrected spec (d1aec7b4) the raw fold is a
    # behavioral-equivalence guarantee, NOT byte-identical: the computed family
    # branch splices the handle_info body verbatim via raw_info_handler (wall-4
    # safe) and legitimately reshapes the BEAM. Their byte-identical goldens
    # therefore retire; behavioral equivalence (handle_info/2 returns the spliced
    # result verbatim, incl. a `match`-shaped body's arms not double-wrapped) is
    # pinned by "terse messages+handle_info / handle_info template routes through
    # the shared family raw emitter" in actor_family_raw_test.exs.
    # Raw13_state_with_body (`actor N state T with <payload> <body-declarations>`)
    # has been FOLDED into the shared emit_raw_state_initial_body ->
    # derive_actor_family emitter (§1e mechanism A) via the positional
    # `Declarations until dedent` hole + the `with` seed (initial: Some). Per the
    # corrected spec (d1aec7b4) the raw fold is a behavioral-equivalence
    # guarantee, NOT byte-identical: the folded initial-seed family path emits
    # init(args: Atom) = %[:ok, payload] with a nullary start_link (vs the
    # template's init(initial: State) + nullary start_link passing payload — both
    # seed the payload) and Effect-wrapped default callbacks. Its byte-identical
    # golden therefore retires; behavioral equivalence (init/1 returns the seeded
    # payload for any argument, default handle_cast, and the spliced extra
    # declaration callable) is pinned by "terse state+with+body template routes
    # through the shared family raw emitter" in actor_family_raw_test.exs.
    # Raw14_state_body (`actor N state T <body-declarations>`) has been FOLDED
    # into the shared emit_raw_state_body → derive_actor_family emitter (§1e
    # mechanism A). This is the first fold to route through the new positional
    # `Declarations until dedent` hole (parser raw-body branch, task #24 step 1):
    # the trailing definition block is captured as a `:declarations_block` node —
    # the same shape the structured family `body` section produces — and threaded
    # to emit_actor_parts via optional_declarations. Per the corrected spec
    # (d1aec7b4) the raw fold is a behavioral-equivalence guarantee, NOT
    # byte-identical: the folded default-init family path emits Effect-wrapped
    # callbacks vs the template's bare-Tuple return types (bodies identical,
    # return types erased). Its byte-identical golden therefore retires;
    # behavioral equivalence (default init/1 + start_link/1 + the spliced extra
    # declarations callable) is pinned by "terse state+body template routes
    # through the shared family raw emitter" in actor_family_raw_test.exs.
    {"Raw15_with_body",
     """
     actor Cure.Generated.Raw15_with_body with 0
       fn helper() -> Int = 0
     """,
     "21eae5f62c773db2e1452e985e786ccc5061eb939b580f5b71f2db7c3262db96"},
    {"Raw16_bare_body",
     """
     actor Cure.Generated.Raw16_bare_body
       fn helper() -> Int = 0
     """,
     "60b2a426b44df7a6b06214b9ba96f90f9df6d5be383ce5654927f129fd49c50d"}
  ]

  defp beam_sha256(name, src) do
    dir = Path.join(System.tmp_dir!(), "cure_actor_golden_#{name}_#{System.unique_integer([:positive])}")
    File.rm_rf!(dir)
    File.mkdir_p!(dir)

    try do
      assert {:ok, _module, _warnings} =
               Cure.Compiler.compile_string(src, output_dir: dir, emit_events: false)

      bin = File.read!(Path.join(dir, "Cure.Generated.#{name}.beam"))
      :crypto.hash(:sha256, bin) |> Base.encode16(case: :lower)
    after
      File.rm_rf!(dir)
    end
  end

  for {name, src, expected} <- @samples do
    test "generated #{name} module is byte-identical to the pre-port snapshot" do
      assert beam_sha256(unquote(name), unquote(src)) == unquote(expected)
    end
  end
end
