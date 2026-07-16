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
     "511485c8a39dcc47ff708cabdeec07cf4a6b9bd3dcc56c50e8e1343c088ed925"}
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
