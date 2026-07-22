defmodule Cure.Compiler.BuildManifest do
  @moduledoc """
  Persisted fingerprint store for incremental Cure compilation.

  One manifest per output directory (`<output_dir>/.cure_manifest`), holding the
  compiler `toolchain` fingerprint, an optional external `stdlib_hash` (project
  builds only), and, per module, its content `source_hash`, `interface_hash`,
  direct `deps`, and the `beams` it produced. Any read or decode problem yields
  an empty manifest so the caller rebuilds everything — the failure mode is
  always "recompile", never "serve stale".
  """

  @manifest_version 1
  @filename ".cure_manifest"
  @toolchain_fingerprint_key {__MODULE__, :toolchain_fingerprint}

  @type entry :: %{
          source_path: String.t(),
          source_hash: binary(),
          interface_hash: binary() | nil,
          deps: [String.t()],
          beams: [String.t()]
        }
  @type t :: %{
          version: pos_integer(),
          toolchain: binary(),
          stdlib_hash: binary() | nil,
          modules: %{String.t() => entry()}
        }

  @spec empty(binary()) :: t()
  def empty(toolchain) when is_binary(toolchain),
    do: %{version: @manifest_version, toolchain: toolchain, stdlib_hash: nil, modules: %{}}

  @spec load(String.t()) :: t()
  def load(output_dir) do
    path = Path.join(output_dir, @filename)

    with {:ok, bin} <- File.read(path),
         {:ok, term} <- safe_decode(bin),
         %{version: @manifest_version, toolchain: tc, modules: mods}
         when is_binary(tc) and is_map(mods) <- term do
      %{
        version: @manifest_version,
        toolchain: tc,
        stdlib_hash: Map.get(term, :stdlib_hash),
        modules: mods
      }
    else
      _ -> empty("")
    end
  end

  @spec save(t(), String.t()) :: :ok
  def save(manifest, output_dir) do
    File.mkdir_p!(output_dir)
    final = Path.join(output_dir, @filename)
    tmp = final <> ".tmp"
    File.write!(tmp, :erlang.term_to_binary(manifest))
    File.rename!(tmp, final)
    :ok
  end

  @doc "SHA-256 over the :cure application's compiled .beam files, in sorted path order."
  @spec toolchain_fingerprint() :: binary()
  def toolchain_fingerprint do
    beams = toolchain_beams()
    signature = toolchain_signature(beams)

    case :persistent_term.get(@toolchain_fingerprint_key, :missing) do
      {^signature, fingerprint} ->
        fingerprint

      _missing_or_changed ->
        fingerprint = compute_toolchain_fingerprint(beams)
        :persistent_term.put(@toolchain_fingerprint_key, {signature, fingerprint})
        fingerprint
    end
  end

  defp toolchain_beams do
    # NOT `Application.app_dir(:cure, "ebin")`: in this project `:code.lib_dir(:cure)`
    # resolves to `_build/cure` (not the standard `_build/<env>/lib/cure`), so
    # `Application.app_dir/2` collides with the driver's own default `output_dir`
    # (`_build/cure/ebin`, see the incremental-compilation Global Constraints).
    # Hashing that directory is self-referential: every compile run writes fresh
    # `Cure.*.beam` files into the exact directory being fingerprinted as
    # "toolchain", so the very next run always sees a mismatch and forces a full
    # rebuild — and it never hashes the compiler's own `Elixir.*.beam` files at
    # all, so a real toolchain change goes undetected. `Mix.Project.compile_path()`
    # is the correct location: `_build/<env>/lib/cure/ebin`, where the `:cure`
    # app's own compiled bytecode actually lives.
    Mix.Project.compile_path()
    |> Path.join("*.beam")
    |> Path.wildcard()
    |> Enum.sort()
  end

  defp toolchain_signature(beams) do
    Enum.map(beams, fn beam ->
      stat = File.stat!(beam, time: :posix)
      {beam, stat.inode, stat.size, stat.mtime, stat.ctime}
    end)
  end

  defp compute_toolchain_fingerprint(beams) do
    ctx = :crypto.hash_init(:sha256)

    beams
    |> Enum.reduce(ctx, fn beam, acc ->
      :crypto.hash_update(acc, File.read!(beam))
    end)
    |> :crypto.hash_final()
  end

  defp safe_decode(bin) do
    {:ok, :erlang.binary_to_term(bin, [:safe])}
  rescue
    _ -> :error
  end
end
