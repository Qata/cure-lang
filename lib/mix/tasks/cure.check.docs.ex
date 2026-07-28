defmodule Mix.Tasks.Cure.Check.Docs do
  @moduledoc """
  Compile every `cure` fenced code block in tracked Markdown documents and
  `.cure` docstrings.

      mix cure.check.docs

  Snippets may be complete modules, declarations, or expressions. Add `expr`
  or `declarations` to a fence's info string when automatic classification is
  ambiguous:

      ```cure expr
      map([1, 2], fn x -> x + 1)
      ```

  Use the expected diagnostic code for an intentionally rejected example, such
  as `cure E093`. It passes only when the compiler returns that exact code; a
  different error, compiler crash, or unexpected successful compilation fails
  the check. Incomplete pseudocode is not Cure source and should use a plain
  `text` fence.

  The declaration-only support surface in `priv/doc_snippets/support.cure` is
  appended to synthetic modules. It is intentionally small: documentation
  should use real standard-library imports for public APIs.
  """

  use Mix.Task

  alias Cure.Diagnostic.{Host, Sink}
  alias Cure.Doc.Snippets

  @shortdoc "Compile every Cure code fence in repository documentation"
  @support_path "priv/doc_snippets/support.cure"

  @impl Mix.Task
  def run(args) do
    if args != [] do
      usage_error("Usage: mix cure.check.docs")
    end

    Application.ensure_all_started(:cure)
    support = File.read!(@support_path)

    root = File.cwd!()

    snippets =
      Enum.flat_map(Snippets.markdown_files(root), &extract_markdown/1) ++
        Enum.flat_map(Snippets.cure_files(root), &extract_cure/1)

    results = Enum.map(snippets, &check(&1, support))
    passed = Enum.count(results, &(&1 == :pass))
    failed = Enum.count(results, &(&1 == :fail))

    IO.puts("\ndoc snippets: #{passed} passed, #{failed} failed")

    if failed > 0 do
      exit({:shutdown, 1})
    end
  end

  defp extract_markdown(path) do
    case Snippets.extract_file(path) do
      {:ok, found} -> found
      {:error, reason} -> Mix.raise("cannot read #{path}: #{:file.format_error(reason)}")
    end
  end

  defp extract_cure(path) do
    case Snippets.extract_cure_file(path) do
      {:ok, found} -> found
      {:error, reason} -> Mix.raise("cannot read #{path}: #{:file.format_error(reason)}")
    end
  end

  defp check(snippet, support) do
    label = relative_label(snippet)
    source = Snippets.source(snippet, support)

    case Snippets.expected_error(snippet) do
      {:error, codes} ->
        IO.puts("  FAIL #{label} (multiple expected error codes: #{Enum.join(codes, ", ")})")
        :fail

      expected ->
        compile_and_classify(snippet, support, source, label, expected)
    end
  end

  defp compile_and_classify(snippet, support, source, label, expected) do
    try do
      case Snippets.compile(snippet, support: support) do
        {:ok, _module, []} when expected != nil ->
          {:ok, code} = expected
          IO.puts("  FAIL #{label} (expected #{code} but compiled)")
          :fail

        {:ok, _module, []} ->
          IO.puts("  ok  #{label}")
          :pass

        {:ok, _module, warnings} when warnings != [] ->
          IO.puts("  FAIL #{label} (#{length(warnings)} warning(s))")

          Enum.each(warnings, fn warning ->
            Mix.shell().error(render({:compiler_warning, warning}, snippet.path, source))
          end)

          :fail

        {:error, reason} ->
          classify_error(reason, snippet.path, source, label, expected)
      end
    rescue
      error ->
        IO.puts("  FAIL #{label} (compiler crashed)")
        Mix.shell().error(Exception.format(:error, error, __STACKTRACE__))
        :fail
    catch
      kind, reason ->
        IO.puts("  FAIL #{label} (compiler #{kind})")
        Mix.shell().error(Exception.format(kind, reason, __STACKTRACE__))
        :fail
    end
  end

  defp classify_error(reason, path, source, label, {:ok, expected}) do
    {diagnostic, _registry} = Host.to_diagnostic(reason, path, source)

    if diagnostic.code == expected do
      IO.puts("  ok  #{label} (#{expected} as documented)")
      :pass
    else
      IO.puts("  FAIL #{label} (expected #{expected}, got #{diagnostic.code})")
      Mix.shell().error(render(reason, path, source))
      :fail
    end
  end

  defp classify_error(reason, path, source, label, nil) do
    IO.puts("  FAIL #{label}")
    Mix.shell().error(render(reason, path, source))
    :fail
  end

  defp relative_label(snippet) do
    path = Path.relative_to_cwd(snippet.path)
    "#{path}:#{snippet.line}"
  end

  defp render(reason, path, source) do
    {diagnostic, registry} = Host.to_diagnostic(reason, path, source)

    Sink.new(format: :plain, color: :auto, width: 100, registry: registry)
    |> Sink.render(diagnostic)
  end

  defp usage_error(message) do
    diagnostic = Cure.Diagnostic.Operational.usage(message)

    Sink.new(format: :plain, color: :auto, width: 80)
    |> Sink.render(diagnostic)
    |> Mix.shell().error()

    exit({:shutdown, 1})
  end
end
