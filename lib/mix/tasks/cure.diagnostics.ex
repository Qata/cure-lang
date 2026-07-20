defmodule Mix.Tasks.Cure.Diagnostics do
  use Mix.Task

  @shortdoc "Exercise compiler diagnostics and print them with coverage"

  @moduledoc """
  Runs the diagnostic exerciser under ExUnit coverage. Use:

      mix cure.diagnostics

  Every case is rendered to stderr in the same plain format used for users.
  """

  @impl true
  def run(args) do
    validate_registry!()

    {opts, [], invalid} =
      OptionParser.parse(args,
        strict: [color: :string, width: :integer, coverage: :boolean],
        aliases: [w: :width]
      )

    if invalid != [], do: Mix.raise("invalid cure.diagnostics options: #{inspect(invalid)}")

    color =
      case Keyword.get(opts, :color, "auto") do
        value when value in ["auto", "always", "never"] -> String.to_atom(value)
        value -> Mix.raise("invalid --color=#{value}; expected auto, always, or never")
      end

    width = Keyword.get(opts, :width, 80)
    if not is_integer(width) or width < 1, do: Mix.raise("--width must be a positive integer")

    Application.put_env(:cure, :diagnostics_exerciser,
      color: color,
      width: width,
      coverage: Keyword.get(opts, :coverage, false)
    )

    test_args =
      if Keyword.get(opts, :coverage, false),
        do: ["--cover", "test/cure/diagnostic_exerciser_test.exs"],
        else: ["test/cure/diagnostic_exerciser_test.exs"]

    Mix.Task.run("test", test_args)
  end

  defp validate_registry! do
    with :ok <- Cure.Diagnostic.Registry.validate(),
         :ok <- Cure.Diagnostic.Registry.validate_reachability(),
         :ok <- Cure.Diagnostic.Registry.validate_sources(),
         :ok <- validate_inventory() do
      :ok
    else
      {:error, reason} -> Mix.raise("diagnostic registry validation failed: #{inspect(reason)}")
    end
  end

  defp validate_inventory do
    inventory = Cure.Diagnostic.Registry.Inventory.scan()

    if inventory.error_constructors == [] do
      {:error, :empty_producer_inventory}
    else
      :ok
    end
  end
end
