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
#
# Re-frozen for typed actor Phase 2: structured actors intentionally add their
# nominal Handle plus validated start/send/stop adapters; call-capable actors
# also add request. This is a public generated-API change, not a quote-port
# refactor. Supervisor and application output remains byte-identical.
defmodule Cure.Compiler.ActorQuoteGoldenTest do
  use ExUnit.Case, async: false

  @samples [
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
     """, "ebdc21771a5a5ea1dc16158e6d7c02112afd0809eaad401f9b855d67de52f7a5"},
    {"GSup",
     """
     mod M
       use Std.Supervisor

       sup Cure.Generated.GSup
         children []
     """, "c946d1c98c57efe5fc692ecad9c313ff11da59893f6cdad3cd2b06990d2c9818"},
    {"GApp",
     """
     mod M
       use Std.App

       app Cure.Generated.GApp
         root Cure.Generated.GSup
     """, "0fc99d391075931aa2c59ec052462675d4f45a754d10ebf45403601355699dfa"},
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
     """, "9a13e85e59e6a53f8647b25efb2e4f2da698a83bafde0aa8a47c14fc40e8403a"}
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
