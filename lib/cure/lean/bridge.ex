defmodule Cure.Lean.Bridge do
  @moduledoc """
  CLI bridge to the Lean/lean4lean checker.

  Stage 1 uses one process per request over stdin/stdout JSON. The executable is
  resolved from `:lean_bridge_executable`, `CURE_LEAN_BRIDGE`, the local
  `lean_bridge/.lake/build/bin/cure-lean-bridge` build, or finally
  `lean --run lean_bridge/CureLeanBridge.lean`. The lean4lean checkout defaults
  to the same checkout used by `lean_bridge/lakefile.lean` and can be
  overridden with `:lean4lean_path` or `CURE_LEAN4LEAN_PATH`.
  """

  @protocol_version 1

  @type response :: {:ok, map()} | {:error, term()}

  @spec health(keyword()) :: response()
  def health(opts \\ []) do
    request(%{"op" => "health", "protocol" => @protocol_version}, opts)
  end

  @spec check_module(map(), keyword()) :: response()
  def check_module(payload, opts \\ []) when is_map(payload) do
    request(
      %{"op" => "check_module", "protocol" => @protocol_version, "payload" => payload},
      opts
    )
  end

  @spec request(map(), keyword()) :: response()
  def request(request, opts \\ []) when is_map(request) do
    with {:ok, {executable, args}} <- bridge_command(opts),
         input = Cure.Project.Json.encode(request),
         {output, 0} <- run_bridge(executable, args, input, opts),
         {:ok, decoded} <- decode_response(output) do
      normalize_response(decoded)
    else
      {output, status} when is_binary(output) and is_integer(status) ->
        {:error, {:lean_bridge_exit, status, String.trim(output)}}

      {:error, _} = err ->
        err
    end
  end

  @spec executable_path(keyword()) :: String.t()
  def executable_path(opts \\ []) do
    Keyword.get(opts, :lean_bridge_executable) ||
      Application.get_env(:cure, :lean_bridge_executable) ||
      System.get_env("CURE_LEAN_BRIDGE") ||
      Path.join([project_root(), "lean_bridge", ".lake", "build", "bin", "cure-lean-bridge"])
  end

  @spec source_path() :: String.t()
  def source_path do
    Path.join([project_root(), "lean_bridge", "CureLeanBridge.lean"])
  end

  @spec lean4lean_path(keyword()) :: String.t()
  def lean4lean_path(opts \\ []) do
    Keyword.get(opts, :lean4lean_path) ||
      Application.get_env(:cure, :lean4lean_path) ||
      System.get_env("CURE_LEAN4LEAN_PATH") ||
      Path.expand("../lean4lean", project_root())
  end

  @spec protocol_version() :: pos_integer()
  def protocol_version, do: @protocol_version

  defp bridge_command(opts) do
    case explicit_executable(opts) do
      nil -> default_bridge_command()
      path -> with :ok <- ensure_executable(path), do: {:ok, {path, []}}
    end
  end

  defp explicit_executable(opts) do
    Keyword.get(opts, :lean_bridge_executable) ||
      Application.get_env(:cure, :lean_bridge_executable) ||
      System.get_env("CURE_LEAN_BRIDGE")
  end

  defp default_bridge_command do
    built = executable_path()

    cond do
      File.exists?(built) and not File.dir?(built) ->
        {:ok, {built, []}}

      lean = System.find_executable("lean") ->
        source = source_path()

        if File.exists?(source) do
          {:ok, {lean, ["--run", source]}}
        else
          {:error, {:lean_bridge_unavailable, %{executable: source, reason: :enoent}}}
        end

      true ->
        {:error, {:lean_bridge_unavailable, %{executable: built, reason: :enoent}}}
    end
  end

  defp ensure_executable(path) do
    cond do
      not File.exists?(path) ->
        {:error, {:lean_bridge_unavailable, %{executable: path, reason: :enoent}}}

      File.dir?(path) ->
        {:error, {:lean_bridge_unavailable, %{executable: path, reason: :eisdir}}}

      true ->
        :ok
    end
  end

  defp run_bridge(executable, args, input, opts) do
    env = [{"CURE_LEAN4LEAN_PATH", lean4lean_path(opts)}]
    System.cmd(executable, args, env: [{"CURE_LEAN_BRIDGE_REQUEST", input} | env], stderr_to_stdout: true)
  rescue
    e in ErlangError ->
      {:error, {:lean_bridge_exec_failed, executable, e.original}}
  end

  defp decode_response(output) do
    output
    |> String.trim()
    |> Cure.Project.Json.decode()
  end

  defp normalize_response(%{"status" => "ok"} = response), do: {:ok, response}

  defp normalize_response(%{"status" => "error", "diagnostics" => diagnostics}),
    do: {:error, {:lean_diagnostics, diagnostics}}

  defp normalize_response(%{"status" => "error", "error" => error}), do: {:error, {:lean_error, error}}
  defp normalize_response(other), do: {:error, {:invalid_lean_bridge_response, other}}

  defp project_root, do: Path.expand("../../..", __DIR__)
end
