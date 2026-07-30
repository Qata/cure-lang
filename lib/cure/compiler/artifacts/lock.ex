defmodule Cure.Compiler.Artifacts.Lock do
  @moduledoc false

  @lock_name ".cure_artifact.lock"
  @attempts 500
  @owner_key {__MODULE__, :owner}

  @spec with_lock(Path.t(), (-> result)) :: result | {:error, term()} when result: term()
  def with_lock(output_root, fun) when is_function(fun, 0) do
    File.mkdir_p!(output_root)
    path = Path.join(output_root, @lock_name)

    case acquire(path, @attempts) do
      {:ok, io} ->
        owner = lock_owner(path)
        write_owner(io, owner)
        Process.put(@owner_key, {io, owner})

        try do
          fun.()
        after
          Process.delete(@owner_key)
          File.close(io)
          File.rm(path)
        end

      {:error, reason} ->
        {:error, {:artifact_lock_failed, reason}}
    end
  end

  @doc false
  @spec set_intended_generation(binary()) :: :ok
  def set_intended_generation(generation) when is_binary(generation) do
    case Process.get(@owner_key) do
      {io, owner} ->
        owner = Map.put(owner, :intended_generation, generation)
        write_owner(io, owner)
        Process.put(@owner_key, {io, owner})
        :ok

      nil ->
        :ok
    end
  end

  defp acquire(_path, 0), do: {:error, :timeout}

  defp acquire(path, attempts) do
    case File.open(path, [:write, :exclusive]) do
      {:ok, io} ->
        {:ok, io}

      {:error, :eexist} ->
        if stale?(path), do: File.rm(path)
        Process.sleep(20)
        acquire(path, attempts - 1)

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp stale?(path) do
    with {:ok, encoded} <- File.read(path),
         owner when is_map(owner) <- safe_owner(encoded),
         true <- owner[:host] == hostname(),
         os_pid when is_binary(os_pid) <- owner[:os_pid] do
      not os_process_alive?(os_pid)
    else
      _ -> false
    end
  end

  defp lock_owner(path) do
    %{
      node: to_string(node()),
      pid: inspect(self()),
      os_pid: System.pid(),
      host: hostname(),
      acquired_at: System.os_time(:second),
      output_root: Path.dirname(path),
      intended_generation: :pending
    }
  end

  defp write_owner(io, owner) do
    {:ok, _position} = :file.position(io, 0)
    :ok = :file.truncate(io)
    :ok = IO.binwrite(io, :erlang.term_to_binary(owner, [:deterministic]))
    :ok = :file.sync(io)
  end

  defp safe_owner(encoded) do
    :erlang.binary_to_term(encoded, [:safe])
  rescue
    _ -> nil
  end

  defp hostname do
    case :inet.gethostname() do
      {:ok, host} -> List.to_string(host)
      {:error, _} -> "unknown"
    end
  end

  defp os_process_alive?(pid) do
    case :os.type() do
      {:unix, _} ->
        case System.cmd("kill", ["-0", pid], stderr_to_stdout: true) do
          {_output, 0} -> true
          {_output, _status} -> false
        end

      _ ->
        # On platforms where Cure cannot prove OS-process liveness, fail closed:
        # the lock is not reclaimable and the caller receives a timeout.
        true
    end
  rescue
    _ -> true
  end
end
