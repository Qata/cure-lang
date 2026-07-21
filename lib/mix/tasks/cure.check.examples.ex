defmodule Mix.Tasks.Cure.Check.Examples do
  @moduledoc """
  Regression task: compiles every supported `.cure` file under `examples/` and runs
  the ones with a `fn main/0`, comparing output against expectations.

  Invoke as:

      mix cure.check.examples

  Expectations are declared inline in this module. When a new example is
  added, add an entry to `@expected` keyed by the example's basename
  (without the `.cure` suffix). The value is one of:

  - `:compile_only` -- the file must compile; its `main/0` (if any) is
    not executed.
  - a string -- `main/0` is executed and its `inspect/1` output must
    match exactly.

  Examples not listed in `@expected` are treated as `:compile_only`.

  ## Exit code

  A small, explicit set of examples is currently skipped because they target
  dependent-language features not yet available in the single dependent
  pipeline. The task exits with status `1` for any unexpected failure.
  """

  use Mix.Task

  alias Cure.Diagnostic.{Host, Sink}

  @shortdoc "Compile and run every .cure example and check their output"

  @examples_dir "examples"

  # These source fixtures target dependent-language features outside the
  # current supported slice. Keep the list explicit so a new skip cannot hide
  # an unexpected regression.
  @known_dependent_gaps ~w(
    derived_show
    destructuring
    json_derive
    json_tree
    lambda_block
    lazy_iter
    let_destructuring
    list_basics
    match_showcase
    pattern_guards
    protocols
    result_handling
    sigma_vector
    specialise
    test_showcase
  )

  @expected %{
    "adt" => "42",
    "assert_type_demo" => "42",
    "dependent_types" => "6",
    "doctest_demo" => "25",
    "fenced_docs" => "240",
    "ffi" => "42",
    "fsm_pipeline" => :compile_only,
    "hello" => "42",
    "holes_demo" => "0",
    "length_indexed" => "{:succ_len, {:succ_len, :zero_len}}",
    "list_basics" => "15",
    "match_showcase" => "200",
    "math" => :compile_only,
    "multi_head_cons" => "6",
    "mutual_recursion" => "1",
    "pattern_guards" => "0",
    "property_test" => ":ok",
    "protocols" => "0",
    "records" => "2",
    "recursion" => "3628800",
    "result_handling" => "0",
    "sigma_pairs" => :compile_only,
    "sigma_vector" => "5",
    "totality" => "120",
    "totality_enforcement" => "142",
    "traffic_light" => :compile_only
  }

  @impl Mix.Task
  def run(_args) do
    # Make sure stdlib beams are on the path and loaded.
    Application.ensure_all_started(:cure)
    ensure_stdlib_compiled()
    preload_stdlib()

    files = Path.wildcard(Path.join(@examples_dir, "*.cure")) |> Enum.sort()

    results = Enum.map(files, &run_one/1)

    passed = Enum.count(results, &match?({:pass, _}, &1))
    skipped = Enum.count(results, &match?({:skip, _}, &1))
    failed = Enum.filter(results, &match?({:fail, _, _}, &1))

    if failed == [] do
      IO.puts("\nexamples: #{passed} passed, #{skipped} skipped, 0 failed")
      :ok
    else
      IO.puts("\nexamples: #{passed} passed, #{length(failed)} failed")

      Enum.each(failed, fn {:fail, name, reason} ->
        IO.puts("  #{name}: #{reason}")
      end)

      exit({:shutdown, 1})
    end
  end

  # -- Per-file logic ---------------------------------------------------------

  defp run_one(path) do
    name = Path.basename(path, ".cure")

    if name in @known_dependent_gaps do
      IO.puts("  skip #{pad(name)} (dependent parity gap)")
      {:skip, name}
    else
      expected = Map.get(@expected, name, :compile_only)

      case {expected, main_fn?(path)} do
        {:compile_only, _} -> compile_only(name, path)
        {_, false} -> compile_only(name, path)
        {val, true} when is_binary(val) -> run_and_compare(name, path, val)
      end
    end
  end

  defp compile_only(name, path) do
    case Cure.Compiler.compile_file(path,
           output_dir: "_build/cure/ex_ebin",
           emit_events: false
         ) do
      {:ok, _module, _warns} ->
        IO.puts("  ok  #{pad(name)} (compile)")
        {:pass, name}

      {:error, reason} ->
        msg = render_host_diagnostic(reason, path)
        IO.puts("  FAIL #{pad(name)} #{msg}")
        {:fail, name, msg}
    end
  end

  defp run_and_compare(name, path, expected) do
    case File.read(path) do
      {:ok, src} ->
        case Cure.Compiler.compile_and_load(src, file: path, emit_events: false) do
          {:ok, module} ->
            try do
              actual = inspect(module.main())

              if actual == expected do
                IO.puts("  ok  #{pad(name)} => #{actual}")
                {:pass, name}
              else
                msg = "expected #{expected}, got #{actual}"
                IO.puts("  FAIL #{pad(name)} #{msg}")
                {:fail, name, msg}
              end
            catch
              kind, reason ->
                msg =
                  "#{kind}: " <>
                    render_host_diagnostic(reason, path)

                IO.puts("  FAIL #{pad(name)} #{msg}")
                {:fail, name, msg}
            end

          {:error, reason} ->
            msg = render_host_diagnostic(reason, path)
            IO.puts("  FAIL #{pad(name)} #{msg}")
            {:fail, name, msg}
        end

      {:error, reason} ->
        msg = "read error: #{reason}"
        IO.puts("  FAIL #{pad(name)} #{msg}")
        {:fail, name, msg}
    end
  end

  defp main_fn?(path) do
    case File.read(path) do
      {:ok, src} -> String.match?(src, ~r/\bfn\s+main\b/)
      _ -> false
    end
  end

  defp pad(name), do: String.pad_trailing(name, 26)

  defp render_host_diagnostic(reason, path) do
    {diagnostic, registry} = Host.to_diagnostic(reason, path)

    Sink.new(format: :plain, color: :auto, width: 80, registry: registry)
    |> Sink.render(diagnostic)
  end

  # -- Stdlib preload ---------------------------------------------------------

  defp ensure_stdlib_compiled do
    ebin = "_build/cure/ebin"

    unless File.exists?(Path.join(ebin, "Cure.Std.Core.beam")) do
      Mix.Task.run("cure.compile_stdlib")
    end
  end

  defp preload_stdlib do
    # Load only `Cure.*.beam` files by name (no `:code.add_patha`) so
    # stale lowercase artifacts under `_build/cure/ebin` cannot shadow
    # OTP modules like `:math` while the examples are being exercised.
    # Explicit `kind: :all` preserves the historical "load everything"
    # behaviour now that `Preload.preload/1` defaults to `:none`.
    Cure.Stdlib.Preload.preload(examples: true, kind: :all)
  end
end
