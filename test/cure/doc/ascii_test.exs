defmodule Cure.Doc.AsciiTest do
  use ExUnit.Case, async: true

  alias Cure.Doc.Ascii

  # The renderer is fed AST nodes directly so the tests stay decoupled
  # from the parser and from any specific example file.

  describe "render/2 -- FSM" do
    test "emits header, states, and a transition table" do
      transitions = [
        %{from: "Locked", event: "coin", to: "Unlocked", event_kind: :normal},
        %{from: "Unlocked", event: "push", to: "Locked", event_kind: :normal}
      ]

      ast = {:lift_module, [behaviour: :gen_statem, module: "Cure.Turnstile", transitions: transitions, line: 1], []}

      out = Ascii.render(ast)
      assert is_binary(out)
      assert out =~ "fsm Cure.Turnstile"
      assert out =~ "states:"
      assert out =~ "▢ Locked"
      assert out =~ "▢ Unlocked"
      assert out =~ "transitions:"
      assert out =~ "Locked ──[coin]──> Unlocked"
      assert out =~ "Unlocked ──[push]──> Locked"
    end

    test "preserves event suffixes ! and ?" do
      transitions = [
        %{from: "S0", event: "go", to: "S1", event_kind: :hard},
        %{from: "S1", event: "skip", to: "S0", event_kind: :soft}
      ]

      ast = {:lift_module, [behaviour: :gen_statem, module: "Cure.X", transitions: transitions, line: 1], []}
      out = Ascii.render(ast)

      assert out =~ "[go!]"
      assert out =~ "[skip?]"
    end

    test "marks terminal states with a filled glyph and a -->* line" do
      transitions = [
        %{from: "S0", event: "stop", to: "Done", event_kind: :normal}
      ]

      ast =
        {:lift_module,
         [behaviour: :gen_statem, module: "Cure.Y", terminal_states: ["Done"], transitions: transitions, line: 1], []}

      out = Ascii.render(ast)
      assert out =~ "▣ Done"
      assert out =~ "Done ──> *"
    end
  end

  describe "render/2 -- Supervisor" do
    test "vertical tree with restart policies" do
      ast =
        {:lift_module,
         [
           behaviour: :supervisor,
           module: "Cure.Colony",
           strategy: :one_for_one,
           children: [
             [id: "worker", module: "Cure.Actor.Worker", restart: :permanent],
             [id: "echo", module: "Cure.Actor.Echo", restart: :transient]
           ],
           line: 1
         ], []}

      out = Ascii.render(ast)
      assert out =~ "sup Cure.Colony (strategy: one_for_one)"
      assert out =~ "├── worker :: Cure.Actor.Worker (permanent)"
      assert out =~ "└── echo :: Cure.Actor.Echo (transient)"
    end
  end

  describe "render/2 -- Application" do
    test "panel includes vsn, root, applications" do
      ast =
        {:lift_module,
         [
           behaviour: :application,
           module: "Cure.Forge",
           vsn: "0.1.0",
           description: "demo",
           root: "Forge.Root",
           applications: [:logger, :stdlib],
           line: 1
         ], []}

      out = Ascii.render(ast)
      assert out =~ "app Cure.Forge (vsn 0.1.0)"
      assert out =~ "description: demo"
      assert out =~ "root: Forge.Root"
      assert out =~ "applications:"
      assert out =~ "├── logger"
      assert out =~ "├── stdlib"
    end

    test "renders a transparent lifted application module" do
      assert {:ok, ast} = Cure.Compiler.parse_source("app Cure.DocApp\n", emit_events: false)
      out = Ascii.render(ast)

      assert out =~ "app Cure.DocApp"
    end
  end

  describe "render/2 -- non-diagram containers" do
    test "returns nil for plain modules" do
      ast = {:lift_module, [behaviour: :custom, module: "Cure.Plain", line: 1], []}
      assert Ascii.render(ast) == nil
    end

    test "returns nil for non-container nodes" do
      assert Ascii.render({:literal, [], 0}) == nil
    end
  end

  describe "render_file/2" do
    test "round-trips a source file via the parser" do
      src = """
      mod Demo
        fn ok() -> Atom = :ok
      """

      path =
        Path.join(System.tmp_dir!(), "cure_ascii_test_#{System.unique_integer([:positive])}.cure")

      try do
        File.write!(path, src)
        assert {:ok, ""} = Ascii.render_file(path)
      after
        File.rm!(path)
      end
    end
  end
end
