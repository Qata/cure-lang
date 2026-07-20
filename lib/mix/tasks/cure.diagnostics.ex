defmodule Mix.Tasks.Cure.Diagnostics do
  use Mix.Task

  @shortdoc "Exercise compiler diagnostics and print them with coverage"

  @moduledoc """
  Runs the diagnostic exerciser under ExUnit coverage. Use:

      mix cure.diagnostics

  Every case is rendered to stderr in the same plain format used for users.
  """

  @impl true
  def run(_args) do
    Mix.Task.run("test", ["--cover", "test/cure/diagnostic_exerciser_test.exs"])
  end
end
