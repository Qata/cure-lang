defmodule Cure.Stdlib.OtpTest do
  @moduledoc """
  `Std.Otp` — the typed BEAM process algebra. The payoff of the whole Effect stack:
  a `Pid(m)` accepts only messages of type `m`, and a `GenServer(q, r)` takes only
  requests `q` and replies `r`, so using a process at the WRONG message OR reply
  type is a COMPILE error (design 2026-07-10-checked-beam-concurrency §2) — the
  guarantee `Std.Otp.Raw`'s untyped `Pid` cannot give.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program
  alias Cure.Core.Env

  # A program in module `App` that `use`s Std.Otp and declares a request ADT.
  defp app(body) do
    Program.elaborate("mod App\n  use Std.Otp\n  type Cmd = Inc | Dec\n#{body}end\n")
  end

  defp effect_result?({:pi, _g, _d, cod}), do: effect_result?(cod)
  defp effect_result?({:effect_type, _}), do: true
  defp effect_result?(_), do: false

  test "the module elaborates on the dependent pipeline; ops are effect-typed" do
    src = File.read!("lib/std/otp.cure")
    {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
    assert {:ok, env, locals} = Program.check_ast_with_locals(ast)

    assert :self in locals and :spawn in locals and :spawn_link in locals and :start_link in locals and
             :start_statem in locals and
             :start_supervisor in locals and
             :tell in locals and :call in locals and :cast in locals

    for op <- [:spawn, :spawn_link, :start_link, :start_statem, :start_supervisor, :tell, :call, :cast],
        do: assert(effect_result?(Env.get_def(env, op).type))
  end

  test "the typed layer owns the public algebra; only Raw contains externs" do
    src = File.read!("lib/std/otp.cure")
    {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
    assert {:ok, env, locals} = Program.check_ast_with_locals(ast)

    for op <- [
          :self,
          :spawn,
          :spawn_link,
          :start_link,
          :start_supervisor,
          :tell,
          :call,
          :cast,
          :stop,
          :send_after,
          :cancel_timer,
          :monitor,
          :demonitor,
          :link,
          :unlink,
          :exit,
          :is_alive,
          :register,
          :unregister,
          :whereis
        ] do
      assert op in locals

      refute match?({:extern, _}, Env.get_def(env, op).body),
             "#{op} must be an ordinary checked wrapper"
    end
  end

  test "gen_server start_link preserves the raw OTP result tuple" do
    assert {:ok, _} =
             app("  fn start(module: Atom, args: List(Int)) -> Effect(Tuple) = Std.Otp.start_link(module, args)\n")
  end

  test "gen_statem start_link preserves the raw OTP result tuple" do
    assert {:ok, _} =
             app("  fn start(module: Atom, args: List(Int)) -> Effect(Tuple) = Std.Otp.start_statem(module, args)\n")
  end

  test "message codes are ordinary checked computations" do
    assert {:ok, _} =
             app("  fn accepts(code: MessageCode) -> Bool = handles(code, :ping, 0)\n")

    assert {:ok, _} =
             app("  fn combines(left: MessageCode, right: MessageCode) -> MessageCode = union(left, right)\n")
  end

  test "beam_ops self expands to ordinary Std.Otp syntax" do
    source = "mod App\n  beam_ops self\n"
    assert {:ok, ast} = Cure.Compiler.parse_source(source, emit_events: false)
    assert inspect(ast) =~ "Std.Otp.self"
    refute inspect(ast) =~ "__otp_container"
  end

  test "beam_ops expands every initial operation to ordinary algebra calls" do
    source = """
    mod App
      use Std.Otp
      type Cmd = Inc | Dec
      fn send_it(p: Pid(Cmd)) -> Effect(Unit) = beam_ops tell p Inc()
      fn call_it(s: GenServer(Cmd, Int)) -> Effect(Int) = beam_ops call s Dec()
      fn cast_it(s: GenServer(Cmd, Int)) -> Effect(Unit) = beam_ops cast s Inc()
      fn stop_it(p: Pid(Cmd)) -> Effect(Unit) = beam_ops stop p
    """

    assert {:ok, _} = Program.elaborate(source)
    refute inspect(Cure.Compiler.parse_source(source, emit_events: false)) =~ "__otp_container"
  end

  test "beam_ops expands behavior-specific startup operations" do
    source = """
    mod App
      use Std.Otp
      fn server(module: Atom) -> Effect(Tuple) = beam_ops start_link module [0]
      fn statem(module: Atom) -> Effect(Tuple) = beam_ops start_statem module [0]
      fn supervisor(module: Atom) -> Effect(Tuple) = beam_ops start_supervisor module [0]
    """

    assert {:ok, _} = Program.elaborate(source)
    expanded = Cure.Compiler.parse_source(source, emit_events: false)
    refute inspect(expanded) =~ "beam_ops"
    refute inspect(expanded) =~ "__otp_container"
  end

  test "beam_ops rejects a message with the wrong typed target" do
    source = """
    mod App
      use Std.Otp
      type Cmd = Inc | Dec
      fn send_it(p: Pid(Cmd)) -> Effect(Unit) = beam_ops tell p 5
    """

    assert {:error, _} = Program.elaborate(source)
  end

  describe "Pid(m) — typed one-way messaging" do
    test "a well-typed message is accepted" do
      assert {:ok, _} = app("  fn go(p: Pid(Cmd)) -> Effect(Unit) =\n    tell(p, Inc())\n")
    end

    test "the WRONG message type is a compile error" do
      assert {:error, _} = app("  fn go(p: Pid(Cmd)) -> Effect(Unit) =\n    tell(p, 5)\n")
    end
  end

  describe "GenServer(q, r) — typed synchronous call" do
    test "a well-typed request returns the server's reply type" do
      assert {:ok, _} =
               app("  fn go(s: GenServer(Cmd, Int)) -> Effect(Int) =\n    call(s, Dec())\n")
    end

    test "the WRONG request type is a compile error" do
      assert {:error, _} =
               app("  fn go(s: GenServer(Cmd, Int)) -> Effect(Int) =\n    call(s, 5)\n")
    end

    test "the WRONG reply type is a compile error (reply rides on the server type)" do
      assert {:error, _} =
               app("  fn go(s: GenServer(Cmd, Int)) -> Effect(Bool) =\n    call(s, Dec())\n")
    end

    test "cast takes a typed request; a wrong request is a compile error" do
      assert {:ok, _} =
               app("  fn go(s: GenServer(Cmd, Int)) -> Effect(Unit) =\n    cast(s, Inc())\n")

      assert {:error, _} =
               app("  fn go(s: GenServer(Cmd, Int)) -> Effect(Unit) =\n    cast(s, 5)\n")
    end
  end

  test "a sequenced typed conversation elaborates (tell then call, via effect bind)" do
    assert {:ok, _} =
             app("""
               fn talk(p: Pid(Cmd), s: GenServer(Cmd, Int)) -> Effect(Int) =
                 let u = tell(p, Inc())
                 call(s, Dec())
             """)
  end
end
