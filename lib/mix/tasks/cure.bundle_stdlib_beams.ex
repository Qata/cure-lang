defmodule Mix.Tasks.Cure.BundleStdlibBeams do
  @moduledoc """
  Compile `lib/std/*.cure` into `priv/ebin/Cure.Std.*.beam`.

  Companion to `Mix.Tasks.Cure.BundleStdlib`, which stages stdlib
  *sources* into `priv/std/`. Host applications that embed Cure (most
  notably the browser REPL inside `:cure_site`) need not just the
  sources but also the compiled stdlib BEAMs reachable at runtime --
  `Std.List.map` lowers to `:'Cure.Std.List':map/...` in codegen, and
  that BEAM has to be loadable or every call raises `:undef`.

  Historically `mix cure.compile_stdlib` wrote the BEAMs to
  `_build/cure/ebin`, a build-time artefact that is not part of an OTP
  release. Staging the BEAMs under `priv/ebin/` instead gives us the
  same guarantees as `priv/std/`:

    * Mix propagates `priv/` into every dep build (`_build/<env>/lib/cure/priv/`).
    * `mix release` bundles `priv/` into the release tarball.
    * `:code.priv_dir(:cure)` resolves to the staged location at runtime.

  ## Idempotency

  Per-module source fingerprints: a `.cure` source triggers a recompile when
  the expected `.beam` is missing or its adjacent SHA-256 sidecar does not
  match the source. This remains correct across branch switches and merges,
  where filesystem mtimes are not reliable provenance. The module name baked
  into the BEAM filename is parsed from the source's `mod ...` declaration (the same regex
  `Cure.Stdlib.Preload` uses at Elixir compile time). Sources we
  cannot classify are compiled unconditionally, since `Cure.Compiler`
  itself produces the canonical filename.

  ## No-op paths

  Leaves the tree untouched when `lib/std/` is missing (hex-packaged
  consumers whose `:files` strips the sources, tests that stub the
  project layout, etc.) and when `Cure.Compiler` is not yet available
  at the moment the task runs (very first dep compile). The caller
  that wired this into a `compile` alias is responsible for ordering
  it **after** the regular `compile` step so `Cure.Compiler` has been
  built.

  Wired into Cure's own `compile` alias in `mix.exs`, so end users do
  not need to invoke it explicitly.
  """

  use Mix.Task

  @shortdoc "Compile Cure stdlib sources into priv/ebin/"

  @source_dir Path.join(["lib", "std"])
  @fingerprint_suffix ".cure-source-sha256"

  @impl Mix.Task
  def run(_args) do
    # `Cure.Compiler` emits pipeline events unconditionally (see
    # `Cure.Compiler.Lexer.maybe_emit_event/2`), so the
    # `Cure.Pipeline.Events.Registry` has to be running for any
    # compilation to succeed. Starting `:cure` as an OTP application
    # brings the registry up via `Cure.Application`. We call it even
    # when `compiler_available?/0` is false below; Mix handles the
    # "app not loaded yet" case gracefully.
    _ = ensure_cure_application_started()
    _ = bundle(@source_dir, default_destination())
    :ok
  end

  defp ensure_cure_application_started do
    if Code.ensure_loaded?(Mix.Task) and function_exported?(Mix.Task, :run, 2) do
      try do
        Mix.Task.run("app.start", [])
      rescue
        _ -> :ok
      catch
        _, _ -> :ok
      end
    else
      Application.ensure_all_started(:cure)
    end
  end

  @doc """
  Default output directory for compiled stdlib BEAMs.

  Resolves to `<priv>/ebin` relative to Cure's mix project root. Exposed
  as a function so tests can stub the path without pulling in Mix.
  """
  @spec default_destination() :: String.t()
  def default_destination, do: Path.join(["priv", "ebin"])

  @doc false
  @spec bundle(String.t(), String.t()) ::
          {:ok, %{compiled: non_neg_integer(), skipped: non_neg_integer(), errors: non_neg_integer()}}
  def bundle(source_dir, dest_dir) do
    cond do
      not File.dir?(source_dir) ->
        {:ok, %{compiled: 0, skipped: 0, errors: 0}}

      not compiler_available?() ->
        {:ok, %{compiled: 0, skipped: 0, errors: 0}}

      true ->
        Process.delete(:cure_bundle_compiler_fingerprint)
        File.mkdir_p!(dest_dir)

        files = source_dir |> Path.join("*.cure") |> Path.wildcard()

        case Cure.Compiler.prepare_files(files) do
          {:ok, plan} ->
            compile_opts = [
              source_roots: [source_dir],
              prelude_providers: plan.providers,
              module_index: plan.module_index
            ]

            Enum.reduce(plan.ordered, {:ok, %{compiled: 0, skipped: 0, errors: 0}}, fn src, {:ok, counts} ->
              compile_one(src, dest_dir, counts, compile_opts)
            end)

          {:error, reason} ->
            if Code.ensure_loaded?(Mix) and function_exported?(Mix, :shell, 0) do
              Mix.shell().error(render_host_diagnostic(reason, source_dir))
            end

            {:ok, %{compiled: 0, skipped: 0, errors: 1}}
        end
    end
  end

  @doc false
  @spec compiler_available?() :: boolean()
  # The task is wired into a `compile` alias that runs *after* the
  # primary `compile` step, so by the time we get here the Cure
  # compiler should already be loaded. On the very first dep compile
  # however the task module can still be stale; guarding with a
  # function-exported check lets us degrade to a silent no-op instead
  # of crashing the entire compile.
  def compiler_available? do
    Code.ensure_loaded?(Cure.Compiler) and
      function_exported?(Cure.Compiler, :compile_file, 2)
  end

  @doc false
  @spec compile_one(String.t(), String.t(), map()) :: {:ok, map()}
  def compile_one(src, dest_dir, counts), do: compile_one(src, dest_dir, counts, [])

  defp compile_one(src, dest_dir, counts, compile_opts) do
    case expected_beam_path(src, dest_dir) do
      {:ok, beam_path} ->
        if should_compile?(src, beam_path) do
          do_compile(src, dest_dir, counts, compile_opts)
        else
          # A fresh BEAM is also an input to later modules in this same bundle:
          # compiled macros and final module-resolution validation may need it
          # loaded even though its source does not need recompilation. Skipping
          # without loading made clean VMs report a transient E101 for providers
          # such as Std.Syntax, then succeed on a later stdlib pass.
          beam_path
          |> Path.basename(".beam")
          |> String.to_atom()
          |> refresh_loaded_beam(dest_dir)

          {:ok, %{counts | skipped: counts.skipped + 1}}
        end

      :unknown ->
        # Could not classify the module name from the source. Compile
        # unconditionally and let `Cure.Compiler` place the BEAM under
        # the canonical name.
        do_compile(src, dest_dir, counts, compile_opts)
    end
  end

  defp do_compile(src, dest_dir, counts, compile_opts) do
    opts =
      Keyword.merge(
        [
          output_dir: dest_dir,
          emit_events: false,
          source_roots: [Path.dirname(src)]
        ],
        compile_opts
      )

    case Cure.Compiler.compile_file(src, opts) do
      {:ok, module, _warnings} ->
        # Keep the freshly compiled runtime module available to later
        # definition-site macro execution. Ordinary name and type resolution
        # uses canonical source-hash-keyed module interfaces and does not
        # inspect loaded BEAM exports.
        refresh_loaded_beam(module, dest_dir)
        write_source_fingerprint(src, Path.join(dest_dir, "#{module}.beam"))
        {:ok, %{counts | compiled: counts.compiled + 1}}

      {:error, reason} ->
        # Surface the failure to the shell but keep processing the
        # remaining stdlib files so a single bad source does not
        # prevent the rest from being staged.
        if Code.ensure_loaded?(Mix) and function_exported?(Mix, :shell, 0) do
          Mix.shell().error(render_host_diagnostic(reason, src))
        end

        {:ok, %{counts | errors: counts.errors + 1}}
    end
  end

  defp render_host_diagnostic(reason, path) do
    {diagnostic, registry} = Cure.Diagnostic.Host.to_diagnostic(reason, path)

    Cure.Diagnostic.Sink.new(format: :plain, color: :auto, width: 80, registry: registry)
    |> Cure.Diagnostic.Sink.render(diagnostic)
  end

  # Purge any previously-loaded copy of `module` and load the beam just
  # written to `dest_dir`, so later modules in the same bundle run probe its
  # fresh export table. Best-effort: a beam we cannot load (e.g. a codegen
  # that wrote an unexpected filename) leaves the VM's current copy in place
  # rather than aborting the bundle.
  defp refresh_loaded_beam(module, dest_dir) do
    base = Path.join(dest_dir, Atom.to_string(module)) |> String.to_charlist()

    if File.exists?(to_string(base) <> ".beam") do
      :code.purge(module)
      :code.load_abs(base)
    end

    :ok
  end

  @doc false
  @spec expected_beam_path(String.t(), String.t()) :: {:ok, String.t()} | :unknown
  def expected_beam_path(src, dest_dir) do
    case module_name_from_source(src) do
      {:ok, declared} ->
        {:ok, Path.join(dest_dir, "Cure.#{declared}.beam")}

      :unknown ->
        :unknown
    end
  end

  @doc false
  @spec module_name_from_source(String.t()) :: {:ok, String.t()} | :unknown
  def module_name_from_source(path) do
    mod_regex = ~r/^\s*(?:mod|proof|actor|fsm|sup|app)\s+([A-Za-z_][\w\.]*)/m

    with {:ok, contents} <- File.read(path),
         [_, declared] <- Regex.run(mod_regex, contents) do
      {:ok, declared}
    else
      _ -> :unknown
    end
  end

  @doc false
  @spec should_compile?(String.t(), String.t()) :: boolean()
  # A source fingerprint is authoritative. Git checkouts and merges can leave
  # a source's mtime older than a beam produced by a different revision, so an
  # mtime-only check can silently retain incompatible generated code. Beams
  # without a fingerprint are conservatively stale and are rebuilt once.
  def should_compile?(src, beam_path) do
    cond do
      not File.regular?(src) ->
        false

      not File.regular?(beam_path) ->
        true

      true ->
        case File.read(fingerprint_path(beam_path)) do
          {:ok, stored_fingerprint} ->
            String.trim(stored_fingerprint) != fingerprint(src)

          {:error, _} ->
            true
        end
    end
  end

  @doc "Return the sidecar path storing a bundled BEAM's source fingerprint."
  @spec fingerprint_path(String.t()) :: String.t()
  def fingerprint_path(beam_path), do: beam_path <> @fingerprint_suffix

  @doc "Return the SHA-256 fingerprint of a Cure source file."
  @spec source_fingerprint(String.t()) :: String.t()
  def source_fingerprint(source_path) do
    :crypto.hash(:sha256, File.read!(source_path))
    |> Base.encode16(case: :lower)
  end

  @doc "Return the source and compiler fingerprint stored beside a BEAM."
  @spec fingerprint(String.t()) :: String.t()
  def fingerprint(source_path) do
    source_fingerprint(source_path) <> ":" <> compiler_fingerprint()
  end

  defp write_source_fingerprint(source_path, beam_path) do
    if File.regular?(beam_path) do
      File.write!(fingerprint_path(beam_path), fingerprint(source_path) <> "\n")
    end
  end

  defp compiler_fingerprint do
    case Process.get(:cure_bundle_compiler_fingerprint) do
      nil ->
        files = ["mix.exs" | Path.wildcard("lib/cure/**/*.ex")] |> Enum.sort()

        payload =
          Enum.map_join(files, <<0>>, fn path ->
            path <> <<0>> <> File.read!(path)
          end)

        value = :crypto.hash(:sha256, payload) |> Base.encode16(case: :lower)
        Process.put(:cure_bundle_compiler_fingerprint, value)
        value

      value ->
        value
    end
  end
end
