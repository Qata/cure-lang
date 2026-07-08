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

  alias Cure.Compiler.{Lexer, Parser, Codegen, BeamWriter}
  alias Cure.Types.Checker
  alias Cure.Optimizer

  @doc """
  Compile a `.cure` source file to BEAM bytecode.

  Reads the file, runs the full pipeline, and writes a `.beam` file
  to the output directory.

  ## Options

  - `:output_dir` -- directory for `.beam` output (default: `"_build/cure/ebin"`)
  - `:emit_events` -- whether to emit pipeline events (default: `true`)
  - `:check_types` -- whether to run the type checker (default: `true`).
    Set to `false` to skip type checking.
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
    path = Path.join(output_dir, "#{module}.beam")

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
    check? = Keyword.get(opts, :check_types, true)

    optimize? = Keyword.get(opts, :optimize, false)
    monomorph? = Keyword.get(opts, :monomorphise, true)
    monomorph_budget = Keyword.get(opts, :monomorph_budget, 16)
    declared_phases = Keyword.get(opts, :declared_phases)

    optimize_opts = [
      monomorphise: monomorph?,
      monomorph_budget: monomorph_budget,
      emit_events: emit?,
      file: file
    ]

    with {:ok, tokens} <- lex(source, file, emit?),
         {:ok, ast} <- parse(tokens, file, emit?),
         {:ok, _} <- maybe_check(ast, file, emit?, check?),
         {:ok, ast} <- maybe_optimize(ast, optimize?, optimize_opts),
         {:ok, forms, cg_warnings} <- codegen(ast, file, emit?, output_dir, declared_phases) do
      # Callback-mode FSMs, typed actors, supervisors, and
      # applications are already compiled, loaded, *and* persisted to
      # `<output_dir>/<mod>.beam` by the codegen step (the dispatcher
      # passed `output_dir` through to the respective compilers). In
      # that case `forms` is one of the `{:callback_mode, module}`,
      # `{:actor, module}`, `{:supervisor, module}`, or `{:app,
      # module}` markers, and there is nothing left for this
      # orchestrator to write.
      case forms do
        {:callback_mode, mod_atom} ->
          {:ok, mod_atom, []}

        {:actor, mod_atom} ->
          {:ok, mod_atom, []}

        {:supervisor, mod_atom} ->
          {:ok, mod_atom, []}

        {:app, mod_atom} ->
          {:ok, mod_atom, []}

        forms when is_list(forms) ->
          write_beam_forms(forms, output_dir, emit?, file, cg_warnings)
      end
    end
  end

  # `BeamWriter.compile_forms/2` returns `{:error, errors, warnings}` (3-tuple)
  # on lint/compile failures, but the public `compile_string/2`,
  # `compile_file/2`, and `compile_and_load/2` contracts are `{:ok, ...}` or
  # `{:error, reason}` (2-tuple). Normalize the BEAM-writer failure here so
  # downstream consumers (CLI, `cure check`, `mix cure.check.examples`, test
  # suites) can rely on the 2-tuple shape without `CaseClauseError` crashes.
  defp write_beam_forms(forms, output_dir, emit?, file, cg_warnings) do
    case BeamWriter.compile_forms(forms) do
      {:ok, module, binary, warnings} ->
        case BeamWriter.write_beam(module, binary, output_dir, emit_events: emit?, file: file) do
          :ok -> {:ok, module, cg_warnings ++ warnings}
          {:error, _} = err -> err
        end

      # Codegen warnings (e.g. W088 unresolved imports) get carried onto the
      # lint-error path in a 3-tuple *only* when there are any, so no other
      # caller's 2-tuple `{:beam_lint_error, errors}` match is disturbed.
      {:error, errors, _warnings} when cg_warnings != [] ->
        {:error, {:beam_lint_error, errors, cg_warnings}}

      {:error, errors, _warnings} ->
        {:error, {:beam_lint_error, errors}}
    end
  end

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

  Returns `{:ok, ast}` or `{:error, {:lex_error | :parse_error, reason}}`.

  ## Examples

      iex> {:ok, ast} = Cure.Compiler.parse_source("mod X\\n  type T = A | B\\n")
      iex> is_list(ast)
      true
  """
  @spec parse_source(String.t(), keyword()) :: {:ok, list()} | {:error, term()}
  def parse_source(source, opts \\ []) do
    file = Keyword.get(opts, :file, "nofile")

    with {:ok, tokens} <- lex(source, file, false) do
      parse(tokens, file, false)
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
    check? = Keyword.get(opts, :check_types, true)

    optimize? = Keyword.get(opts, :optimize, false)
    monomorph? = Keyword.get(opts, :monomorphise, true)
    monomorph_budget = Keyword.get(opts, :monomorph_budget, 16)
    declared_phases = Keyword.get(opts, :declared_phases)

    optimize_opts = [
      monomorphise: monomorph?,
      monomorph_budget: monomorph_budget,
      emit_events: emit?,
      file: file
    ]

    with {:ok, tokens} <- lex(source, file, emit?),
         {:ok, ast} <- parse(tokens, file, emit?),
         {:ok, _} <- maybe_check(ast, file, emit?, check?),
         {:ok, ast} <- maybe_optimize(ast, optimize?, optimize_opts),
         {:ok, forms, _cg_warnings} <- codegen(ast, file, emit?, nil, declared_phases) do
      # compile_and_load/2 intentionally does NOT persist bytecode to
      # disk -- it only loads into the current VM -- so we pass `nil`
      # for `output_dir` and the container compilers skip their
      # `BeamWriter.write_beam/4` calls.
      case forms do
        {:callback_mode, mod_atom} ->
          {:ok, mod_atom}

        {:actor, mod_atom} ->
          {:ok, mod_atom}

        {:supervisor, mod_atom} ->
          {:ok, mod_atom}

        {:app, mod_atom} ->
          {:ok, mod_atom}

        forms when is_list(forms) ->
          BeamWriter.compile_and_load(forms)
      end
    end
  end

  # -- Pipeline Steps ----------------------------------------------------------

  defp lex(source, file, emit?) do
    case Lexer.tokenize(source, file: file, emit_events: emit?) do
      {:ok, tokens} -> {:ok, tokens}
      {:error, reason} -> {:error, {:lex_error, reason}}
    end
  end

  defp parse(tokens, file, emit?) do
    case Parser.parse(tokens, file: file, emit_events: emit?) do
      {:ok, ast} -> {:ok, ast}
      {:error, errors} -> {:error, {:parse_error, errors}}
    end
  end

  defp maybe_optimize(ast, false, _opts), do: {:ok, ast}

  defp maybe_optimize(ast, true, opts) do
    {:ok, optimized, _stats} = Optimizer.optimize(ast, opts)
    {:ok, optimized}
  end

  defp maybe_check(_ast, _file, _emit?, false), do: {:ok, :skipped}

  defp maybe_check(ast, file, emit?, true) do
    # Proof-collect mode: when `Cure.Project.Proof.collect/1` sets up the
    # `cure_proof_certs` ETS table before invoking the compiler, any proof
    # certificates discharged inside `Cure.Types.Checker` are expected to
    # be deposited directly via `Cure.Project.Proof.deposit/1`. The
    # compiler pipeline itself does not intercept the checker's return
    # value for this purpose -- the checker's public API always returns
    # `{:ok, term()}` and the side-channel ETS table is the handshake.
    case Checker.check_module(ast, file: file, emit_events: emit?) do
      {:ok, _} = ok -> ok
      {:error, errors} -> {:error, {:type_error, errors}}
    end
  end

  defp codegen(ast, file, emit?, output_dir, declared_phases) do
    result =
      if Cure.Elab.Program.dependent?(ast) do
        # The kernel-lowering path never produces codegen warnings.
        case dependent_codegen(ast) do
          {:ok, forms} -> {:ok, forms, []}
          {:error, _} = err -> err
        end
      else
        opts = [file: file, emit_events: emit?, output_dir: output_dir]

        opts =
          if is_list(declared_phases),
            do: Keyword.put(opts, :declared_phases, declared_phases),
            else: opts

        case Codegen.compile_module(ast, opts) do
          {:ok, forms, cg_warnings} -> {:ok, forms, cg_warnings}
          {:error, reason} -> {:error, {:codegen_error, reason}}
        end
      end

    # Inject the module's `@group(:g)` decorator as a BEAM `-group([:g]).`
    # attribute. This runs once here so BOTH the classic and dependent
    # pipelines get it from one mechanism. Container compilers that already
    # emitted/loaded their module (fsm/actor/sup/app) return a marker tuple,
    # not a forms list, so they pass through untouched.
    case result do
      {:ok, forms, warnings} when is_list(forms) ->
        {:ok, inject_group_attribute(forms, ast), warnings}

      other ->
        other
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

  # First `{:decorator, [name: "group"...], [{:literal, _, atom}]}` node found
  # anywhere in the parsed program, or nil. Mirrors the parser's standalone
  # module-level decorator shape.
  defp group_atom(node) do
    node |> group_atoms() |> List.first()
  end

  defp group_atoms({:decorator, meta, [{:literal, _, atom}]})
       when is_list(meta) and is_atom(atom) do
    if Keyword.get(meta, :name) == "group", do: [atom], else: []
  end

  defp group_atoms({_tag, _meta, children}) when is_list(children),
    do: Enum.flat_map(children, &group_atoms/1)

  defp group_atoms(list) when is_list(list), do: Enum.flat_map(list, &group_atoms/1)
  defp group_atoms(_other), do: []

  # A dependent module is lowered by the kernel: elaborate to `Cure.Core`, erase
  # its {0,ω} index arguments, and emit the erased residue as real BEAM forms.
  defp dependent_codegen(ast) do
    with {:ok, env, local_defs} <- Cure.Elab.Program.check_ast_with_locals(ast),
         {:ok, forms} <- Cure.Elab.Emit.compile_forms(env, Cure.Elab.Program.module_atom(ast), local_defs) do
      {:ok, forms}
    else
      {:error, reason} -> {:error, {:codegen_error, reason}}
    end
  end
end
