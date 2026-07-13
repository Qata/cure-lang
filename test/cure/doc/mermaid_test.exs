defmodule Cure.Doc.MermaidTest do
  use ExUnit.Case, async: true

  alias Cure.Doc.Mermaid

  describe "FSM rendering" do
    test "emits stateDiagram-v2 with initial, edges, and event suffix" do
      transitions = [
        %{from: "Locked", event: "coin", to: "Unlocked", event_kind: :normal},
        %{from: "Unlocked", event: "push!", to: "Locked", event_kind: :hard}
      ]

      ast = {:lift_module, [behaviour: :gen_statem, module: "Cure.Turnstile", transitions: transitions, line: 1], []}
      out = Mermaid.render(ast)

      assert out =~ "stateDiagram-v2"
      assert out =~ "[*] --> Locked"
      assert out =~ "Locked --> Unlocked : coin"
      assert out =~ "Unlocked --> Locked : push!!"
    end

    test "renders terminal states into a sink edge" do
      transitions = [
        %{from: "Running", event: "stop", to: "Done", event_kind: :normal}
      ]

      ast =
        {:lift_module,
         [behaviour: :gen_statem, module: "Cure.Job", terminal_states: ["Done"], transitions: transitions, line: 1], []}

      out = Mermaid.render(ast)
      assert out =~ "Done --> [*]"
    end

    test "returns nil for non-container input" do
      assert Mermaid.render({:literal, [], 42}) == nil
    end
  end

  describe "supervisor rendering" do
    test "renders children as labelled nodes linked from the supervisor" do
      ast =
        {:lift_module,
         [
           behaviour: :supervisor,
           module: "Cure.Colony",
           strategy: :one_for_one,
           children: [
             [id: "worker", module: "WorkerActor", restart: :permanent],
             [id: "echo", module: "EchoActor", restart: :transient]
           ],
           line: 1
         ], []}

      out = Mermaid.render(ast)
      assert out =~ "graph TD"
      assert out =~ "Colony"
      assert out =~ "WorkerActor"
      assert out =~ "EchoActor"
      assert out =~ "Cure_Colony --> worker"
      assert out =~ "Cure_Colony --> echo"
    end
  end

  describe "application rendering" do
    test "labels the app node with vsn and draws the root edge" do
      ast =
        {:lift_module,
         [
           behaviour: :application,
           module: "Cure.CureAtelier",
           vsn: "0.27.0",
           root: "Atelier.Root",
           applications: ["logger", "cure"],
           line: 1
         ], []}

      out = Mermaid.render(ast)
      assert out =~ "graph LR"
      assert out =~ "CureAtelier"
      assert out =~ "vsn 0.27.0"
      assert out =~ "root: Atelier.Root"
      assert out =~ "logger"
      assert out =~ "cure"
    end

    test "renders a transparent lifted supervisor module" do
      assert {:ok, ast} = Cure.Compiler.parse_source("sup Cure.DocSup\n", emit_events: false)
      out = Mermaid.render(ast)

      assert out =~ "graph TD"
      assert out =~ "Cure.DocSup"
    end
  end
end
