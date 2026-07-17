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
     "f819aab07c06793a1fe2f145bd3dd9865f5fc9bf034cee53cd5bb2cf01d0db7a"},
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
     "2756ad344630d8dbefa49f55b67224c0537bdd5bb1c6f09e112d1628c0982031"},
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
     "20fd156f84f75a598bab7ac2064f2cf3edecb75057a9884b565b1d514f4438ab"},
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
     "511485c8a39dcc47ff708cabdeec07cf4a6b9bd3dcc56c50e8e1343c088ed925"},
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
    {"Raw07_state_initial_cast",
     """
     actor Cure.Generated.Raw07_state_initial_cast state Int initial 0 handle_cast
       %[:noreply, state]
     """,
     "da4eb6bdb6a6ad5f4a332508ad33e5cb0a5a14629280cbe1c2f501214dbb017c"},
    {"Raw08_state_initial_messages_cast",
     """
     actor Cure.Generated.Raw08_state_initial_messages_cast state Int initial 0 messages Atom handle_cast
       %[:noreply, state]
     """,
     "4c1e8b80c5beaf2d7530e9532937211cf333f0750d399d752dfeea4a6f5a77a7"},
    {"Raw10_bare_cast",
     """
     actor Cure.Generated.Raw10_bare_cast handle_cast
       %[:noreply, state]
     """,
     "d960f4e0002773caf1bd8f8cdf855ee2cb1dafc16909bd8b06123d1a23fe11ff"},
    {"Raw11_state_messages_info",
     """
     actor Cure.Generated.Raw11_state_messages_info state Int messages Atom handle_info
       %[:noreply, state]
     """,
     "452c46b46cb7db8fea849d1c5c85209a3fd774b7a299d7a58cbe4a31bc201a90"},
    {"Raw12_state_info",
     """
     actor Cure.Generated.Raw12_state_info state Int handle_info
       %[:noreply, state + 1]
     """,
     "83c072435c8ad460084846bdd078b120310cae0d4819a752dd58b14fcee661b4"},
    {"Raw13_state_with_body",
     """
     actor Cure.Generated.Raw13_state_with_body state Int with 0
       fn helper() -> Int = 0
     """,
     "7035f79646a68bf95c0f7b10bfb95e422bbdb6037cfb2b15781ffac47a7289a3"},
    {"Raw14_state_body",
     """
     actor Cure.Generated.Raw14_state_body state Int
       fn helper() -> Int = 0
     """,
     "5a8f011c1a8a62cde887a045aba29553bb8e2cbaae0cad045a8b245fa779fbff"},
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
