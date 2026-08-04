defmodule Cure.Compiler.ModulePipeline.Publication do
  @moduledoc """
  Atomic publication of a run's interfaces.

  A generation is assembled somewhere no reader looks, and only then moved into
  place with a single rename. Two runs writing the same output directory can
  therefore interleave freely: a reader either sees a generation entirely or
  does not see it at all, and never sees the half-built staging tree that
  produced it.

  The pointer is published the same way — written under a private name and
  renamed over the old one — so "which generation is current" also flips in one
  step rather than being briefly absent.
  """

  alias Cure.Compiler.ModuleInterface
  alias Cure.Compiler.ModulePipeline.Interface

  @staging ".staging"
  @pointer "current"
  @index "index.term"

  @doc """
  Assemble `interfaces` as `generation` under `root` and make it current.

  Returns `:ok` when publication is not requested, so callers do not have to
  know whether this run publishes anything.
  """
  @spec publish(Path.t() | nil, term(), %{term() => ModuleInterface.t()}) :: :ok | {:error, term()}
  def publish(nil, _generation, _interfaces), do: :ok

  def publish(root, generation, interfaces) when is_binary(root) do
    staging = Path.join([root, @staging, "gen-#{generation}-#{System.unique_integer([:positive])}"])
    final = generation_path(root, generation)

    with :ok <- File.mkdir_p(staging),
         :ok <- write_interfaces(interfaces, staging),
         :ok <- write_index(staging, root, generation, interfaces),
         :ok <- install(staging, final),
         :ok <- point_at(root, generation) do
      :ok
    else
      {:error, reason} ->
        File.rm_rf(staging)
        {:error, {:publication_failed, generation, reason}}
    end
  end

  @doc """
  The generation a reader of `root` currently sees.

  The pointer is followed exactly once: a reader that resolves it twice could
  straddle two generations, which is the very thing atomic publication exists
  to prevent.
  """
  @spec open(Path.t()) :: {:ok, map()} | {:error, term()}
  def open(root) when is_binary(root) do
    with {:ok, generation} <- File.read(Path.join(root, @pointer)),
         path = generation_path(root, generation),
         {:ok, payload} <- File.read(Path.join(path, @index)),
         {:ok, index} <- decode(payload) do
      {:ok, Map.put(index, :path, path)}
    else
      {:error, reason} -> {:error, {:no_published_generation, root, reason}}
    end
  end

  @doc """
  Whether every module the opened generation claims is actually there and reads
  back as a valid interface.

  A generation that is missing one of its own modules was observed mid-assembly,
  which a rename cannot produce and a copy can.
  """
  @spec complete?(map()) :: boolean()
  def complete?(%{path: path, modules: modules}) do
    Enum.all?(modules, fn module_name ->
      match?({:ok, %ModuleInterface{}}, Interface.read(Interface.path(path, module_name)))
    end)
  end

  def complete?(_published), do: false

  @doc """
  Whether anything the opened generation names still points into staging.

  Every path a reader can reach must live under the published generation. One
  that does not is a window onto a tree another run may still be writing, or may
  already have deleted.
  """
  @spec contains_staging_reference?(map()) :: boolean()
  def contains_staging_reference?(%{} = published) do
    published |> paths() |> Enum.any?(&staged?/1)
  end

  defp paths(%{path: path, root: root, modules: modules}) do
    [path, root | Enum.map(modules, &Interface.path(path, &1))]
  end

  defp staged?(path) when is_binary(path), do: @staging in Path.split(path)
  defp staged?(_path), do: false

  defp write_interfaces(interfaces, staging) do
    interfaces
    |> Map.values()
    |> Enum.uniq_by(& &1.module_name)
    |> Enum.reduce_while(:ok, fn interface, :ok ->
      case Interface.write(interface, staging) do
        :ok -> {:cont, :ok}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  # The index records the generation's *final* home, never the staging one it
  # was built in: a reader that opens it must not be handed a path that is about
  # to disappear.
  defp write_index(staging, root, generation, interfaces) do
    index = %{
      generation: generation,
      root: root,
      modules: interfaces |> Map.values() |> Enum.map(& &1.module_name) |> Enum.uniq() |> Enum.sort()
    }

    File.write(Path.join(staging, @index), :erlang.term_to_binary(index, [:deterministic]), [:binary])
  end

  # Losing the race is not a failure. Another run published the same generation
  # from the same sources, so its tree is as good as this one's; the only thing
  # that would be wrong is to overwrite a tree readers are already inside.
  defp install(staging, final) do
    with :ok <- File.mkdir_p(Path.dirname(final)),
         {:error, reason} <- File.rename(staging, final) do
      File.rm_rf(staging)
      if File.dir?(final), do: :ok, else: {:error, reason}
    end
  end

  defp point_at(root, generation) do
    pointer = Path.join(root, @pointer)
    scratch = "#{pointer}.#{System.unique_integer([:positive])}"

    with :ok <- File.write(scratch, to_string(generation), [:binary]),
         :ok <- File.rename(scratch, pointer) do
      :ok
    else
      {:error, _} = error ->
        File.rm(scratch)
        error
    end
  end

  defp generation_path(root, generation), do: Path.join(root, "generation-#{generation}")

  defp decode(payload) do
    {:ok, :erlang.binary_to_term(payload, [:safe])}
  rescue
    ArgumentError -> {:error, :generation_index_invalid}
  end
end
