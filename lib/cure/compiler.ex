defmodule Cure.Compiler do
  @moduledoc """
  Compiler orchestrator for the Cure programming language.

  Chains together the full compilation pipeline:

      source -> Lexer -> Parser -> [Checker] -> Codegen -> BeamWriter -> .beam

  The type checker runs before codegen by default; set `check_types: false`
  (or pass `--no-type-check` to the CLI) to opt out.

  Emits pipeline events at each stage boundary.

  ## Usage

      # Compile a file
      {:ok, module, warnings} = Cure.Compiler.compile_file("hello.cure")

      # Compile a string
      {:ok, module, warnings} = Cure.Compiler.compile_string(source, file: "hello.cure")

      # Compile and load into VM (for testing / REPL)
      {:ok, module} = Cure.Compiler.compile_and_load(source)
  """

  alias Cure.Compiler.{Lexer, Parser, BeamWriter}

  @doc """
  Compile a `.cure` source file to BEAM bytecode.

  Reads the file, runs the full pipeline, and writes a `.beam` file
  to the output directory.

  ## Options

  - `:output_dir` -- directory for `.beam` output (default: `"_build/cure/ebin"`)
  - `:emit_events` -- whether to emit pipeline events (default: `true`)
  - `:check_types` -- whether to run the type checker (default: `true`).
    Set to `false` to skip type checking.
  - `:source_roots` -- directories containing sibling `.cure` modules that may
    be imported with `use` (default: the source file's directory)
  """
  @spec compile_file(String.t(), keyword()) ::
          {:ok, module(), list()} | {:error, term()}
  def compile_file(path, opts \\ []) do
    case File.read(path) do
      {:ok, source} ->
        opts = Keyword.put_new(opts, :file, path)
        compile_string(source, opts)

      {:error, reason} ->
        {:error, {:file_read_error, path, reason}}
    end
  end

  @doc """
  Load a just-emitted `<output_dir>/<module>.beam` into the VM via
  `:code.load_binary/3` — no code-path mutation. Used by multi-file
  builds so later files' codegen can resolve imports of earlier ones.
  """
  @spec load_emitted(module(), Path.t()) :: :ok | {:error, term()}
  def load_emitted(module, output_dir) when is_atom(module) and is_binary(output_dir) do
    module_name = module |> Atom.to_string() |> String.replace_prefix("Elixir.", "")
    path = Path.join(output_dir, "#{module_name}.beam")

    with {:ok, binary} <- File.read(path),
         {:module, ^module} <- :code.load_binary(module, String.to_charlist(path), binary) do
      :ok
    else
      {:error, reason} -> {:error, reason}
    end
  end

  @doc """
  Compile a Cure source string to BEAM bytecode and write to disk.

  ## Options

  - `:file` -- filename for error messages (default: `"nofile"`)
  - `:output_dir` -- directory for `.beam` output (default: `"_build/cure/ebin"`)
  - `:emit_events` -- whether to emit pipeline events (default: `true`)
  """
  @spec compile_string(String.t(), keyword()) ::
          {:ok, module(), list()} | {:error, term()}
  def compile_string(source, opts \\ []) do
    file = Keyword.get(opts, :file, "nofile")
    output_dir = Keyword.get(opts, :output_dir, "_build/cure/ebin")
    emit? = Keyword.get(opts, :emit_events, true)
    declared_phases = Keyword.get(opts, :declared_phases)

    with_source_roots(file, opts, fn ->
      with {:ok, edition} <- resolve_edition(source, opts),
           {:ok, tokens} <- lex(source, file, emit?, edition),
           {:ok, ast} <- parse(tokens, file, emit?, edition),
           {:ok, ast} <- migrate_warn(ast, file),
           {:ok, ast} <- Cure.Elab.Program.expand_declaration_uses(ast),
           {:ok, units, cg_warnings} <- codegen(ast, file, emit?, output_dir, declared_phases) do
        write_beam_units(units, output_dir, emit?, file, cg_warnings)
      end
    end)
  end

  # `BeamWriter.compile_forms/2` returns `{:error, errors, warnings}` (3-tuple)
  # on lint/compile failures, but the public `compile_string/2`,
  # `compile_file/2`, and `compile_and_load/2` contracts are `{:ok, ...}` or
  # `{:error, reason}` (2-tuple). Normalize the BEAM-writer failure here so
  # downstream consumers (CLI, `cure check`, `mix cure.check.examples`, test
  # suites) can rely on the 2-tuple shape without `CaseClauseError` crashes.
  defp write_beam_units([{main_module, _main_forms} | _] = units, output_dir, emit?, file, cg_warnings) do
    Enum.reduce_while(units, {:ok, main_module, cg_warnings}, fn {_module, forms}, {:ok, main, warnings} ->
      case BeamWriter.compile_forms(forms) do
        {:ok, module, binary, beam_warnings} ->
          case BeamWriter.write_beam(module, binary, output_dir, emit_events: emit?, file: file) do
            :ok -> {:cont, {:ok, main, warnings ++ beam_warnings}}
            {:error, _} = err -> {:halt, err}
          end

        {:error, errors, _beam_warnings} when warnings != [] ->
          {:halt, {:error, {:beam_lint_error, errors, warnings}}}

        {:error, errors, _beam_warnings} ->
          {:halt, {:error, {:beam_lint_error, errors}}}
      end
    end)
  end

  defp write_beam_units([], _output_dir, _emit?, _file, _warnings),
    do: {:error, {:codegen_error, :no_compilation_units}}

  defp compile_and_load_units([{main_module, _main_forms} | _] = units) do
    Enum.reduce_while(units, {:ok, main_module}, fn {_module, forms}, {:ok, main} ->
      case BeamWriter.compile_and_load(forms) do
        {:ok, _loaded} -> {:cont, {:ok, main}}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp compile_and_load_units([]), do: {:error, {:codegen_error, :no_compilation_units}}

  @doc """
  Lex and parse a Cure source string into its raw parser AST.

  Runs the front end only — no type checking, optimization, or codegen — and
  with pipeline event emission disabled, so it works **headless**: under
  `mix run --no-compile --no-start`, a bare `elixir` invocation, or any context
  where the `:cure` application (and its events registry) is not started. This
  is the supported entry point for debugging and tooling that needs to inspect
  how a construct parses. See `Cure.Pipeline.Events.emission_enabled?/0`.

  ## Options

  - `:file` -- filename for error messages (default: `"nofile"`)

  Returns `{:ok, ast}` or `{:error, {:lex_error | :parse_error | :edition_error, reason}}`.
  An `:edition_error` is returned when the resolved edition (file pragma or project
  `Cure.toml`) is unknown — surfaced rather than silently degraded to the default.

  ## Examples

      iex> {:ok, ast} = Cure.Compiler.parse_source("mod X\\n  type T = A | B\\n")
      iex> is_list(ast)
      true
  """
  @spec parse_source(String.t(), keyword()) :: {:ok, list()} | {:error, term()}
  def parse_source(source, opts \\ []) do
    file = Keyword.get(opts, :file, "nofile")

    # Tooling entry: resolve the file's edition so inspection sees the same keyword
    # set the compiler would — pragma > project Cure.toml > default, matching the
    # compile path (A3-F2). A real :file discovers its project root so a manifest-
    # pinned edition is honoured; a genuine no-file source stays headless (nil dir
    # → default). An unknown edition is surfaced, not swallowed (iteration 8, F1):
    # a manifest edition error can't be re-caught by the parser (the manifest isn't
    # in the source), so degrading to current() would hide a real §3.1 error.
    project_dir = if file in [nil, "nofile"], do: nil, else: Cure.Project.find_root(file)

    case Cure.Edition.resolve(%{source: source, project_dir: project_dir}) do
      {:ok, edition} ->
        with {:ok, tokens} <- lex(source, file, false, edition) do
          parse(tokens, file, false, edition)
        end

      {:error, reason} ->
        {:error, {:edition_error, reason}}
    end
  end

  @doc """
  Compile a Cure source string and load the resulting module into the VM.

  Does not write a `.beam` file to disk. Useful for testing and REPL.
  """
  @spec compile_and_load(String.t(), keyword()) ::
          {:ok, module()} | {:error, term()}
  def compile_and_load(source, opts \\ []) do
    file = Keyword.get(opts, :file, "nofile")
    emit? = Keyword.get(opts, :emit_events, false)
    declared_phases = Keyword.get(opts, :declared_phases)

    with_source_roots(file, opts, fn ->
      with {:ok, edition} <- resolve_edition(source, opts),
           {:ok, tokens} <- lex(source, file, emit?, edition),
           {:ok, ast} <- parse(tokens, file, emit?, edition),
           {:ok, ast} <- Cure.Elab.Program.expand_declaration_uses(ast),
           {:ok, units, _cg_warnings} <- codegen(ast, file, emit?, nil, declared_phases) do
        # compile_and_load/2 intentionally does NOT persist bytecode to
        # disk -- it only loads into the current VM.
        compile_and_load_units(units)
      end
    end)
  end

  # The dependent elaborator resolves `use` imports from source, not from the
  # BEAM loader. Keep roots process-local for one compilation so recursive
  # imported-module elaboration and parallel callers cannot leak project state.
  defp with_source_roots(file, opts, fun) do
    roots =
      Keyword.get(opts, :source_roots, default_source_roots(file))
      |> List.wrap()
      |> Enum.filter(&is_binary/1)
      |> Enum.map(&Path.expand/1)
      |> Enum.uniq()

    previous = Process.get(:cure_source_roots)
    Process.put(:cure_source_roots, roots)

    try do
      fun.()
    after
      if previous == nil,
        do: Process.delete(:cure_source_roots),
        else: Process.put(:cure_source_roots, previous)
    end
  end

  defp default_source_roots(file) when file in [nil, "nofile"], do: []
  defp default_source_roots(file), do: [Path.dirname(Path.expand(file))]

  # -- Pipeline Steps ----------------------------------------------------------

  defp lex(source, file, emit?, edition) do
    case Lexer.tokenize(source, file: file, emit_events: emit?, edition: edition) do
      {:ok, tokens} -> {:ok, tokens}
      {:error, reason} -> {:error, {:lex_error, reason}}
    end
  end

  defp parse(tokens, file, emit?, edition) do
    case Parser.parse(tokens, file: file, emit_events: emit?, edition: edition) do
      {:ok, ast} -> {:ok, ast}
      {:error, errors} -> {:error, {:parse_error, errors}}
    end
  end

  # Resolve the edition this source compiles under (spec §3.2 precedence: file
  # `@edition` pragma > `Cure.toml` `[project].edition` > compiler default). The
  # resolved edition drives the lexer's keyword set (§4), so a file pinned to an
  # older edition still parses a since-retired keyword under `cure build` — the
  # feature's headline purpose (F-A). The project root is taken from `:project_dir`
  # when a caller supplies it, else discovered from the file's path (see below); a
  # bare source with no file and no manifest resolves to the file pragma alone,
  # else default (§3.2 point 3). An unknown edition (typo'd pragma / bad manifest)
  # fails loudly HERE (§3.1) rather than compiling silently under the default.
  defp resolve_edition(source, opts) do
    input = %{source: source}

    # A caller that knows the project root passes `:project_dir`; otherwise it is
    # DISCOVERED from the file's own path — the nearest ancestor `Cure.toml`. This
    # is what lets `cure build`/`run` honour a project's `[project].edition`
    # without every CLI caller threading a dir, while a file deep in a dependency
    # tree still binds to its own manifest (nearest wins), not a far-away app's.
    project_dir =
      Keyword.get(opts, :project_dir) ||
        Cure.Project.find_root(Keyword.get(opts, :file))

    input =
      case project_dir do
        nil -> input
        dir -> Map.put(input, :project_dir, dir)
      end

    case Cure.Edition.resolve(input) do
      {:ok, edition} -> {:ok, edition}
      {:error, reason} -> {:error, {:edition_error, reason}}
    end
  end

  # `cure build` warn-and-tolerate consumer of the migration facility (spec
  # §5.1): run the deprecation rules, print each warning to stderr, and continue
  # compiling on the *tolerated* (rewritten-in-memory) AST — the source file is
  # never modified. `cure migrate` is the separate rewrite-and-write consumer.
  defp migrate_warn(ast, file) do
    {ast, warnings} = Cure.Migrate.run(ast, file: file, apply: :safe_only)
    registry = migration_source_registry(file)

    Enum.each(warnings, fn w ->
      IO.puts(:stderr, Cure.Diagnostic.Renderer.plain(Cure.Diagnostic.Operational.migration_warning(w), registry))
    end)

    {:ok, ast}
  end

  defp migration_source_registry(file) do
    case File.read(file) do
      {:ok, source} ->
        Cure.Diagnostic.SourceRegistry.new()
        |> Cure.Diagnostic.SourceRegistry.register(file, source, file)

      {:error, _reason} ->
        nil
    end
  end

  defp codegen(ast, _file, _emit?, _output_dir, _declared_phases) do
    case Cure.Compiler.LiftModule.collect(ast) do
      {:ok, lifted_requests} ->
        codegen_modules(ast, Cure.Compiler.LiftModule.strip(ast), lifted_requests)

      {:error, reason} ->
        {:error, {:codegen_error, reason}}
    end
  end

  defp codegen_modules(original_ast, main_ast, lifted_requests) do
    if match?({:lift_module, _, _}, main_ast) do
      case emit_lifted_modules(lifted_requests) do
        {:ok, lifted_units} -> {:ok, lifted_units, []}
        {:error, _} = error -> error
      end
    else
      codegen_modules_with_main(original_ast, main_ast, lifted_requests)
    end
  end

  defp codegen_modules_with_main(original_ast, main_ast, lifted_requests) do
    # Single pipeline: every module is lowered by the kernel (dependent codegen).
    # The classic `Cure.Compiler.Codegen` branch was deleted in the #18 rip-out.
    result =
      with :ok <- Cure.Elab.Program.validate_stdlib_imports(main_ast) do
        case dependent_codegen(main_ast) do
          {:ok, forms} -> {:ok, forms, []}
          {:error, {:codegen_error, {:expansion_ill_typed, _} = reason}} -> {:error, reason}
          {:error, _} = err -> err
        end
      else
        {:error, reason} -> {:error, {:codegen_error, reason}}
      end

    # Inject the module's `@group(:g)` decorator as a BEAM `-group([:g]).`
    # attribute after the ordinary dependent pipeline has produced forms.
    case result do
      {:ok, forms, warnings} when is_list(forms) ->
        with {:ok, lifted_units} <- emit_lifted_modules(lifted_requests) do
          main_forms = inject_group_attribute(forms, original_ast)
          {:ok, [{forms_module(main_forms), main_forms} | lifted_units], warnings}
        end

      other ->
        other
    end
  end

  defp emit_lifted_modules(requests) do
    Enum.reduce_while(requests, {:ok, []}, fn request, {:ok, acc} ->
      case Cure.Compiler.LiftModule.emit(request) do
        {:ok, unit} -> {:cont, {:ok, acc ++ [{unit.module, unit.forms}]}}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp forms_module([{:attribute, _line, :module, module} | _]), do: module

  defp forms_module(forms) do
    case Enum.find(forms, &match?({:attribute, _, :module, _}, &1)) do
      {:attribute, _line, :module, module} -> module
      _ -> raise ArgumentError, "compiled forms are missing a module attribute"
    end
  end

  # Walk the original AST for the first standalone `@group(:g)` decorator node
  # and, if present, splice `{:attribute, 1, :group, [g]}` into `forms` right
  # after the last leading module attribute (before any function form).
  defp inject_group_attribute(forms, ast) do
    case group_atom(ast) do
      nil ->
        forms

      atom ->
        {attrs, rest} = Enum.split_while(forms, &match?({:attribute, _, _, _}, &1))
        attrs ++ [{:attribute, 1, :group, [atom]}] ++ rest
    end
  end

  # The `@group(:g)` atom for the parsed program, or nil. `@group` above `mod`
  # attaches to the module container's meta; the in-body form is a parse error
  # (spec 2026-07-10-group-decorator-placement), so meta is the only source.
  defp group_atom(node) do
    node |> group_atoms() |> List.first()
  end

  # A module container with `@group(:g)` attached above `mod` carries the group
  # in its meta as a canonical decorator node
  # (`decorator: {:decorator, [name: :group], [{:literal, _, atom}]}`). Read it
  # there, then descend into the body for nested containers.
  defp group_atoms({:container, meta, children}) when is_list(meta) and is_list(children) do
    from_meta =
      case Keyword.get(meta, :decorator) do
        {:decorator, dm, [{:literal, _, atom}]} when is_atom(atom) ->
          if Keyword.get(dm, :name) == :group, do: [atom], else: []

        _ ->
          []
      end

    from_meta ++ Enum.flat_map(children, &group_atoms/1)
  end

  defp group_atoms({_tag, _meta, children}) when is_list(children),
    do: Enum.flat_map(children, &group_atoms/1)

  defp group_atoms(list) when is_list(list), do: Enum.flat_map(list, &group_atoms/1)
  defp group_atoms(_other), do: []

  # A dependent module is lowered by the kernel: elaborate to `Cure.Core`, erase
  # its {0,ω} index arguments, and emit the erased residue as real BEAM forms.
  defp dependent_codegen(ast) do
    with {:ok, env, local_defs} <- Cure.Elab.Program.check_ast_with_locals(ast),
         {:ok, forms} <-
           Cure.Elab.Emit.compile_forms(
             env,
             Cure.Elab.Program.module_atom(ast),
             local_defs
           ) do
      {:ok, forms}
    else
      {:error, reason} -> {:error, {:codegen_error, reason}}
    end
  end
end
