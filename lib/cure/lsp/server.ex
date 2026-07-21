defmodule Cure.LSP.Server do
  @moduledoc """
  Language Server Protocol implementation for Cure.

  Implements the LSP over stdio, providing:
  - Real-time diagnostics (compile errors) on document changes
  - Hover information (function signatures, types)
  - Document synchronization (full sync mode)

  ## Usage

  Start from the command line:

      mix cure.lsp

  Or programmatically:

      {:ok, pid} = Cure.LSP.Server.start_link()
  """

  use GenServer

  alias Cure.LSP.Transport
  alias Cure.LSP.Positions
  alias Cure.Compiler.{Formatter, Lexer, Parser, Printer}
  alias Cure.MetaAST.Metadata

  defstruct [
    :reader_pid,
    initialized: false,
    position_encoding: :utf16,
    documents: %{},
    ast_cache: %{},
    buffer: ""
  ]

  # -- Public API --------------------------------------------------------------

  @doc "Start the LSP server."
  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts, name: __MODULE__)
  end

  @doc """
  Process a raw incoming message (used by the stdin reader or tests).
  """
  def handle_raw_message(message) when is_map(message) do
    GenServer.cast(__MODULE__, {:message, message})
  end

  @doc """
  Process a raw message directly, returning the server's response action.

  Used for testing without the GenServer.
  """
  @spec process_message(map(), map()) :: {map(), [map()]}
  def process_message(message, state) do
    method = Map.get(message, "method")
    id = Map.get(message, "id")
    params = Map.get(message, "params", %{})

    do_handle(method, id, params, state)
  end

  # -- GenServer Callbacks -----------------------------------------------------

  @impl true
  def init(_opts) do
    # Start the stdin reader process that reads LSP frames and sends messages
    server = self()

    reader =
      spawn_link(fn ->
        lsp_reader_loop(server)
      end)

    {:ok, %__MODULE__{reader_pid: reader}}
  end

  @impl true
  def handle_cast({:message, message}, state) do
    {new_state, _responses} = process_message(message, state)
    {:noreply, struct(__MODULE__, new_state)}
  end

  @impl true
  def handle_info({:lsp_message, message}, state) do
    {new_state, _} = process_message(message, Map.from_struct(state))
    {:noreply, struct(__MODULE__, new_state)}
  end

  def handle_info(_msg, state), do: {:noreply, state}

  # -- Message Dispatch --------------------------------------------------------

  defp do_handle("initialize", id, params, state) do
    position_encoding = negotiate_position_encoding(params)

    result = %{
      "capabilities" => %{
        "positionEncoding" => position_encoding_name(position_encoding),
        "textDocumentSync" => %{
          "openClose" => true,
          "change" => 1,
          "save" => %{"includeText" => true}
        },
        "hoverProvider" => true,
        "definitionProvider" => true,
        "documentSymbolProvider" => true,
        "workspaceSymbolProvider" => true,
        # Formatting is handled by `Cure.Compiler.Formatter`, a
        # source-preserving formatter that round-trip-validates its
        # output against the original AST before returning edits.
        # The destructive AST pretty printer is still available via
        # `cure fmt --aggressive` for users who want canonicalisation.
        "documentFormattingProvider" => true,
        "renameProvider" => %{"prepareProvider" => true},
        "signatureHelpProvider" => %{
          "triggerCharacters" => ["(", ","]
        },
        "inlayHintProvider" => %{"resolveProvider" => false},
        "semanticTokensProvider" => %{
          "legend" => %{
            "tokenTypes" => [
              "keyword",
              "function",
              "variable",
              "type",
              "string",
              "number",
              "comment",
              "operator"
            ],
            "tokenModifiers" => []
          },
          "full" => true,
          "range" => false
        },
        "codeLensProvider" => %{"resolveProvider" => false},
        "codeActionProvider" => %{
          "codeActionKinds" => ["quickfix"]
        },
        "completionProvider" => %{
          "triggerCharacters" => [".", ":", "?"]
        }
      },
      "serverInfo" => %{
        "name" => "cure-lsp",
        "version" => "0.2.0"
        # bumped for v0.17.0
      }
    }

    Transport.send_response(id, result)
    {state |> Map.put(:initialized, true) |> Map.put(:position_encoding, position_encoding), []}
  end

  defp do_handle("initialized", _id, _params, state) do
    {state, []}
  end

  defp do_handle("shutdown", id, _params, state) do
    Transport.send_response(id, nil)
    {state, []}
  end

  defp do_handle("exit", _id, _params, state) do
    System.halt(0)
    {state, []}
  end

  defp do_handle("textDocument/didOpen", _id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    text = Map.get(td, "text", "")

    docs = Map.get(state, :documents, %{})
    state = Map.put(state, :documents, Map.put(docs, uri, text))

    diagnostics = compute_diagnostics(uri, text, Map.get(state, :position_encoding, :utf16))
    publish_diagnostics(uri, diagnostics)

    {state, diagnostics}
  end

  defp do_handle("textDocument/didChange", _id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    version = Map.get(td, "version")
    changes = Map.get(params, "contentChanges", [])

    text =
      case changes do
        [%{"text" => full_text} | _] -> full_text
        _ -> Map.get(Map.get(state, :documents, %{}), uri, "")
      end

    docs = Map.get(state, :documents, %{})
    state = Map.put(state, :documents, Map.put(docs, uri, text))

    # Check AST cache -- skip reparse if version unchanged
    cache = Map.get(state, :ast_cache, %{})
    cached_version = get_in(cache, [uri, :version])

    if cached_version == version and version != nil do
      # Same version, skip diagnostics
      {state, []}
    else
      diagnostics = compute_diagnostics(uri, text, Map.get(state, :position_encoding, :utf16))
      publish_diagnostics(uri, diagnostics)

      # Update cache
      cache = Map.put(cache, uri, %{version: version, diagnostics: diagnostics})
      state = Map.put(state, :ast_cache, cache)

      {state, diagnostics}
    end
  end

  defp do_handle("textDocument/didClose", _id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    docs = Map.get(state, :documents, %{})
    state = Map.put(state, :documents, Map.delete(docs, uri))

    # Clear diagnostics
    publish_diagnostics(uri, [])
    {state, []}
  end

  defp do_handle("textDocument/didSave", _id, _params, state) do
    {state, []}
  end

  defp do_handle("textDocument/hover", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    pos = Map.get(params, "position", %{})
    line = Map.get(pos, "line", 0)
    char = Map.get(pos, "character", 0)

    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")
    result = compute_hover(text, line, char)

    Transport.send_response(id, result)
    {state, []}
  end

  defp do_handle("textDocument/completion", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")

    items = keyword_completions() ++ context_completions(text)
    Transport.send_response(id, items)
    {state, []}
  end

  defp do_handle("textDocument/definition", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    pos = Map.get(params, "position", %{})
    line = Map.get(pos, "line", 0)
    char = Map.get(pos, "character", 0)

    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")
    result = find_definition(text, uri, line, char, Map.get(state, :position_encoding, :utf16))

    Transport.send_response(id, result)
    {state, []}
  end

  defp do_handle("textDocument/documentSymbol", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")

    symbols = compute_symbols(text, Map.get(state, :position_encoding, :utf16))
    Transport.send_response(id, symbols)
    {state, []}
  end

  defp do_handle("textDocument/codeAction", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    context = Map.get(params, "context", %{})
    diagnostics = Map.get(context, "diagnostics", [])

    actions = compute_code_actions(uri, diagnostics)
    Transport.send_response(id, actions)
    {state, []}
  end

  defp do_handle("textDocument/inlayHint", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")
    hints = compute_inlay_hints(text)
    Transport.send_response(id, hints)
    {state, []}
  end

  defp do_handle("textDocument/signatureHelp", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    pos = Map.get(params, "position", %{})
    line = Map.get(pos, "line", 0)
    char = Map.get(pos, "character", 0)
    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")

    Transport.send_response(id, compute_signature_help(text, line, char))
    {state, []}
  end

  defp do_handle("textDocument/formatting", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")

    Transport.send_response(id, compute_formatting_edits(text))
    {state, []}
  end

  defp do_handle("textDocument/prepareRename", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    pos = Map.get(params, "position", %{})
    line = Map.get(pos, "line", 0)
    char = Map.get(pos, "character", 0)
    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")

    Transport.send_response(id, prepare_rename(text, line, char))
    {state, []}
  end

  defp do_handle("textDocument/rename", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    pos = Map.get(params, "position", %{})
    line = Map.get(pos, "line", 0)
    char = Map.get(pos, "character", 0)
    new_name = Map.get(params, "newName", "")
    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")

    Transport.send_response(id, compute_rename(uri, text, line, char, new_name))
    {state, []}
  end

  defp do_handle("textDocument/codeLens", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")

    Transport.send_response(id, compute_code_lenses(uri, text))
    {state, []}
  end

  defp do_handle("textDocument/semanticTokens/full", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")

    Transport.send_response(id, %{"data" => compute_semantic_tokens(text)})
    {state, []}
  end

  defp do_handle("workspace/symbol", id, params, state) do
    query = Map.get(params, "query", "")
    docs = Map.get(state, :documents, %{})
    Transport.send_response(id, compute_workspace_symbols(query, docs, Map.get(state, :position_encoding, :utf16)))
    {state, []}
  end

  defp do_handle(_method, _id, _params, state) do
    {state, []}
  end

  # -- Diagnostics -------------------------------------------------------------

  @doc false
  def compute_diagnostics(uri, text, encoding \\ :utf16) do
    case Cure.Elab.Program.elaborate(text, file: uri) do
      {:ok, _env} ->
        []

      {:error, reason} ->
        reason
        |> lsp_error_list()
        |> Enum.map(&source_diagnostic(&1, uri, text, encoding))
    end
  end

  defp lsp_error_list({:parse_error, errors}) when is_list(errors), do: errors
  defp lsp_error_list({:type_error, errors}) when is_list(errors), do: errors
  defp lsp_error_list(errors) when is_list(errors), do: errors
  defp lsp_error_list(error), do: [error]

  @doc false
  def diagnostic_to_lsp(%Cure.Diagnostic{} = diagnostic, registry \\ nil, encoding \\ :utf16) do
    Cure.Diagnostic.Renderer.lsp(diagnostic, registry, encoding)
  end

  defp source_diagnostic(error, uri, source, encoding) do
    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, uri, source)
    diagnostic_to_lsp(diagnostic, registry, encoding)
  end

  defp negotiate_position_encoding(params) do
    offered = get_in(params, ["capabilities", "general", "positionEncodings"]) || []

    cond do
      "utf-8" in offered -> :utf8
      "utf-16" in offered -> :utf16
      "utf-32" in offered -> :utf32
      true -> :utf16
    end
  end

  defp position_encoding_name(:utf8), do: "utf-8"
  defp position_encoding_name(:utf16), do: "utf-16"
  defp position_encoding_name(:utf32), do: "utf-32"

  defp publish_diagnostics(uri, diagnostics) do
    Transport.send_notification("textDocument/publishDiagnostics", %{
      "uri" => uri,
      "diagnostics" => diagnostics
    })
  end

  # -- Hover -------------------------------------------------------------------

  defp compute_hover(text, line, char) do
    # Try AST-based hover first, fall back to line-matching
    case parse_to_ast(text) do
      {:ok, ast} ->
        symbols = build_symbol_table(ast)
        lines = String.split(text, "\n")
        target_line = Enum.at(lines, line, "")
        word = extract_word_at(target_line, char)
        dotted_word = extract_dotted_word_at(target_line, char)

        case Enum.find(equation_symbols(ast), &(&1.name == dotted_word)) ||
               Enum.find(symbols, fn s -> s.name == word end) do
          %{kind: :equation, proposition: proposition, line: fn_line} ->
            hover_text = "```cure\n#{proposition}\n```\n\n*Certified from the definition at line #{fn_line}*"
            %{"contents" => %{"kind" => "markdown", "value" => hover_text}}

          %{kind: :function, signature: sig, line: fn_line} ->
            hover_text = "```cure\n#{sig}\n```\n\n*Defined at line #{fn_line}*"
            %{"contents" => %{"kind" => "markdown", "value" => hover_text}}

          _ ->
            compute_hover_fallback(target_line)
        end

      _ ->
        lines = String.split(text, "\n")
        target_line = Enum.at(lines, line, "")
        compute_hover_fallback(target_line)
    end
  end

  defp compute_hover_fallback(target_line) do
    cond do
      String.contains?(target_line, "fn ") ->
        effect_info = infer_hover_effects(target_line)

        hover_text =
          if effect_info != "" do
            "```cure\n#{String.trim(target_line)}\n```\n\n**Effects:** #{effect_info}"
          else
            "```cure\n#{String.trim(target_line)}\n```"
          end

        %{"contents" => %{"kind" => "markdown", "value" => hover_text}}

      String.contains?(target_line, "mod ") ->
        %{
          "contents" => %{
            "kind" => "markdown",
            "value" => "**Module definition**\n```cure\n#{String.trim(target_line)}\n```"
          }
        }

      Enum.any?(["actor ", "fsm ", "sup ", "app "], &String.contains?(target_line, &1)) ->
        %{
          "contents" => %{
            "kind" => "markdown",
            "value" => "**Standard-library macro**\n```cure\n#{String.trim(target_line)}\n```"
          }
        }

      true ->
        nil
    end
  end

  defp infer_hover_effects(line) do
    cond do
      String.contains?(line, "! ") ->
        case Regex.run(~r/!\s+(.+?)(?:\s+when|\s+=|$)/, line) do
          [_, effects] -> effects
          _ -> ""
        end

      Enum.any?(["println", "print", "put_chars"], &String.contains?(line, &1)) ->
        "Io"

      String.contains?(line, "throw") ->
        "Exception"

      String.contains?(line, "spawn") ->
        "Spawn"

      true ->
        ""
    end
  end

  # -- Go-to-Definition --------------------------------------------------------

  defp find_definition(text, uri, line, char, encoding) do
    lines = String.split(text, "\n")
    target_line = Enum.at(lines, line, "")
    word = extract_word_at(target_line, char)
    dotted_word = extract_dotted_word_at(target_line, char)

    if word != "" do
      # Try AST-based symbol table first
      definition_line =
        case parse_to_ast(text) do
          {:ok, ast} ->
            symbols = build_symbol_table(ast, text, encoding)

            case Enum.find(equation_symbols(ast), &(&1.name == dotted_word)) ||
                   Enum.find(symbols, fn s -> s.name == word and s.kind == :function end) do
              %{line: l} -> l - 1
              _ -> nil
            end

          _ ->
            nil
        end

      # Fall back to text search
      definition_line =
        definition_line ||
          Enum.find_index(lines, fn l ->
            String.contains?(l, "fn #{word}(") or String.contains?(l, "fn #{word} ")
          end)

      if definition_line do
        symbol_range =
          case parse_to_ast(text) do
            {:ok, ast} ->
              case Enum.find(build_symbol_table(ast, text, encoding), fn s -> s.name == word and s.kind == :function end) do
                %{span: span} -> Positions.range(span, text, encoding)
                _ -> Positions.line_range(definition_line + 1, text, encoding)
              end

            _ ->
              Positions.line_range(definition_line + 1, text, encoding)
          end

        %{
          "uri" => uri,
          "range" => symbol_range
        }
      else
        nil
      end
    else
      nil
    end
  end

  defp extract_word(line) do
    case Regex.run(~r/\b([a-z_][a-z0-9_]*)\s*\(/, line) do
      [_, word] ->
        word

      _ ->
        case Regex.run(~r/\b([a-z_][a-z0-9_]*)/, String.trim(line)) do
          [_, word] -> word
          _ -> ""
        end
    end
  end

  defp extract_word_at(line, char) do
    # Extract the identifier at the given character position
    graphemes = String.graphemes(line)
    # Walk backwards from char to find word start
    {before, _after} = Enum.split(graphemes, min(char, length(graphemes)))
    prefix = before |> Enum.reverse() |> Enum.take_while(&(&1 =~ ~r/[a-zA-Z0-9_]/)) |> Enum.reverse() |> Enum.join()

    suffix =
      graphemes |> Enum.drop(min(char, length(graphemes))) |> Enum.take_while(&(&1 =~ ~r/[a-zA-Z0-9_]/)) |> Enum.join()

    word = prefix <> suffix
    if word == "", do: extract_word(line), else: word
  end

  defp extract_dotted_word_at(line, char) do
    graphemes = String.graphemes(line)
    {before, after_cursor} = Enum.split(graphemes, min(char, length(graphemes)))
    allowed = &(&1 =~ ~r/[a-zA-Z0-9_.]/)
    prefix = before |> Enum.reverse() |> Enum.take_while(allowed) |> Enum.reverse() |> Enum.join()
    suffix = after_cursor |> Enum.take_while(allowed) |> Enum.join()
    prefix <> suffix
  end

  # -- Document Symbols --------------------------------------------------------

  defp compute_symbols(text, encoding) do
    with {:ok, tokens} <- Lexer.tokenize(text, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      Cure.LSP.Symbols.extract(ast, text, encoding)
    else
      _ -> []
    end
  end

  # -- Code Actions ------------------------------------------------------------

  @doc false
  def compute_code_actions(uri, diagnostics) do
    Enum.flat_map(diagnostics, fn diag ->
      message = Map.get(diag, "message", "")
      structured = structured_code_actions(uri, diag)

      cond do
        structured != [] ->
          structured

        String.contains?(message, "not exhaustive") ->
          range = Map.get(diag, "range", %{})
          end_line = get_in(range, ["end", "line"]) || 0

          [
            %{
              "title" => "Add wildcard pattern (_ -> ...)",
              "kind" => "quickfix",
              "diagnostics" => [diag],
              "edit" => %{
                "changes" => %{
                  uri => [
                    %{
                      "range" => %{
                        "start" => %{"line" => end_line + 1, "character" => 0},
                        "end" => %{"line" => end_line + 1, "character" => 0}
                      },
                      "newText" => "    | _ -> throw \"unhandled case\"\n"
                    }
                  ]
                }
              }
            }
          ]

        String.contains?(message, "undefined") or String.contains?(message, "unbound") ->
          # Try to suggest similar names
          case Regex.run(~r/'([^']+)'/, message) do
            [_, name] ->
              candidates = ~w(fn mod let if match type proto impl use)

              case Cure.Compiler.Errors.suggest(name, candidates) do
                nil ->
                  []

                suggestion ->
                  [
                    %{
                      "title" => "Did you mean '#{suggestion}'?",
                      "kind" => "quickfix",
                      "diagnostics" => [diag]
                    }
                  ]
              end

            _ ->
              []
          end

        true ->
          []
      end
    end)
  end

  defp structured_code_actions(default_uri, diagnostic) do
    diagnostic
    |> get_in(["data", "suggestions"])
    |> List.wrap()
    |> Enum.flat_map(fn suggestion ->
      edits = Map.get(suggestion, "edits", [])

      if Map.get(suggestion, "applicability") == "machine_applicable" and edits != [] do
        changes =
          Enum.group_by(
            edits,
            fn edit -> Map.get(edit, "uri") |> present_uri(default_uri) end,
            &Map.take(&1, ["range", "newText"])
          )

        [
          %{
            "title" => Map.fetch!(suggestion, "message"),
            "kind" => "quickfix",
            "diagnostics" => [diagnostic],
            "edit" => %{"changes" => changes}
          }
        ]
      else
        []
      end
    end)
  end

  defp present_uri(uri, default_uri) when uri in [nil, ""], do: default_uri
  defp present_uri(uri, _default_uri), do: uri

  # -- Completions -------------------------------------------------------------

  defp keyword_completions do
    keywords =
      ~w(fn mod rec actor fsm sup app proto impl type let have proof because if then else elif match return throw try catch finally use local when requires where)

    Enum.map(keywords, fn kw ->
      %{
        "label" => kw,
        "kind" => 14,
        "detail" => "Cure keyword"
      }
    end)
  end

  defp context_completions(text) do
    ast_completions =
      case parse_to_ast(text) do
        {:ok, ast} ->
          symbols = build_symbol_table(ast)

          ordinary =
            Enum.map(symbols, fn s ->
              kind = if s.kind == :function, do: 3, else: 2
              %{"label" => s.name, "kind" => kind, "detail" => s.signature}
            end)

          equations =
            Enum.map(equation_symbols(ast), fn equation ->
              %{"label" => equation.name, "kind" => 3, "detail" => equation.proposition}
            end)

          ordinary ++ equations

        _ ->
          []
      end

    ast_completions
  end

  @doc false
  def equation_symbols(ast) do
    ast
    |> collect_equation_symbols([])
    |> Enum.group_by(& &1.name)
    |> Enum.flat_map(fn
      {_name, [only]} -> [only]
      {_name, collisions} -> Enum.map(collisions, &%{&1 | name: &1.structural_name})
    end)
    |> Enum.sort_by(& &1.name)
  end

  defp collect_equation_symbols(list, acc) when is_list(list),
    do: Enum.flat_map(list, &collect_equation_symbols(&1, acc))

  defp collect_equation_symbols({:function_def, meta, body}, _acc) do
    name = Keyword.get(meta, :name, "?")

    params =
      meta
      |> Keyword.get(:params, [])
      |> Enum.map(fn {:param, _param_meta, param_name} -> param_name end)

    info = Metadata.source_info(meta)
    collect_equation_paths(body, name, params, %{}, [], Keyword.get(meta, :line, 1), info && info.whole)
  end

  defp collect_equation_symbols({_tag, _meta, children}, acc) when is_list(children),
    do: Enum.flat_map(children, &collect_equation_symbols(&1, acc))

  defp collect_equation_symbols(_other, _acc), do: []

  defp collect_equation_paths([single], name, params, replacements, path, line, span),
    do: collect_equation_paths(single, name, params, replacements, path, line, span)

  defp collect_equation_paths(
         {:pattern_match, _meta, [{:variable, _scrutinee_meta, scrutinee} | arms]},
         name,
         params,
         replacements,
         path,
         line,
         span
       ) do
    Enum.flat_map(arms, fn
      {:match_arm, arm_meta, body} ->
        pattern = Keyword.get(arm_meta, :pattern)

        case equation_pattern_name(pattern) do
          nil ->
            []

          constructor ->
            info = Metadata.source_info(arm_meta)

            collect_equation_paths(
              body,
              name,
              params,
              Map.put(replacements, scrutinee, pattern),
              path ++ [constructor],
              (info && info.whole.start_line) || line,
              (info && info.whole) || span
            )
        end

      _ ->
        []
    end)
  end

  defp collect_equation_paths(_leaf, _name, _params, _replacements, [], _line, _span), do: []

  defp collect_equation_paths(leaf, name, params, replacements, path, line, span) do
    member = List.last(path)
    full_name = "#{name}.#{member}"
    arguments = Enum.map(params, &Map.get(replacements, &1, {:variable, [scope: :local], &1}))
    left = Printer.quoted_to_string({:function_call, [name: name], arguments})
    right = leaf |> single_equation_body() |> Printer.quoted_to_string()

    [
      %{
        name: full_name,
        structural_name: name <> "/" <> Enum.join(path, "/"),
        kind: :equation,
        line: line,
        span: span,
        proposition: "#{full_name} : Equivalent(_, #{left}, #{right})"
      }
    ]
  end

  defp single_equation_body([body]), do: body
  defp single_equation_body(body), do: body

  defp equation_pattern_name({:variable, _meta, name}) when is_binary(name), do: name
  defp equation_pattern_name({:function_call, meta, _args}), do: Keyword.get(meta, :name)
  defp equation_pattern_name(_pattern), do: nil

  # -- AST Helpers for LSP -------------------------------------------------------

  defp parse_to_ast(text) do
    with {:ok, tokens} <- Lexer.tokenize(text, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      {:ok, ast}
    end
  end

  @doc false
  def build_symbol_table(ast, source \\ nil, encoding \\ :utf16) do
    extract_symbols(ast, [], source, encoding)
  end

  defp extract_symbols({:container, meta, body}, acc, source, encoding) do
    name = Keyword.get(meta, :name, "unknown")
    line = Keyword.get(meta, :line, 1)
    type = Keyword.get(meta, :container_type, :module)
    info = Metadata.source_info(meta)
    acc = [%{name: name, kind: :module, line: line, signature: "#{type} #{name}", span: info && info.whole} | acc]
    Enum.reduce(body, acc, &extract_symbols(&1, &2, source, encoding))
  end

  defp extract_symbols({:block, _, children}, acc, source, encoding) do
    Enum.reduce(children, acc, &extract_symbols(&1, &2, source, encoding))
  end

  defp extract_symbols({:function_def, meta, _body}, acc, _source, _encoding) do
    name = Keyword.get(meta, :name, "unknown")
    params = Keyword.get(meta, :params, [])
    line = Keyword.get(meta, :line, 1)

    param_str = Enum.map_join(params, ", ", &format_param/1)

    sig = "fn #{name}(#{param_str})"
    info = Metadata.source_info(meta)
    [%{name: name, kind: :function, line: line, signature: sig, span: info && info.whole} | acc]
  end

  defp extract_symbols(_, acc, _source, _encoding), do: acc

  # Parameter pretty-printer tolerant of the various AST shapes the parser
  # can emit (full `:param` tuples, bare `:variable` tuples in generic type
  # parameter position, raw identifiers, etc.). Any shape we don't know is
  # rendered with a safe fallback so inlay-hint / symbol requests cannot
  # crash the LSP server.
  defp format_param({:param, pm, pn}) when is_list(pm) do
    case Keyword.get(pm, :type) do
      nil -> to_string(pn)
      type -> "#{pn}: #{format_type(type)}"
    end
  end

  defp format_param({:variable, _, name}) when is_binary(name), do: name
  defp format_param({:variable, _, name}) when is_atom(name), do: Atom.to_string(name)
  defp format_param(name) when is_binary(name), do: name
  defp format_param(name) when is_atom(name), do: Atom.to_string(name)
  defp format_param(other), do: inspect(other)

  defp format_type({:variable, _, name}) when is_binary(name), do: name
  defp format_type({:variable, _, name}) when is_atom(name), do: Atom.to_string(name)

  defp format_type({:function_call, meta, _}) when is_list(meta),
    do: Keyword.get(meta, :name, "?") |> to_string()

  defp format_type(other) when is_binary(other), do: other
  defp format_type(other) when is_atom(other), do: Atom.to_string(other)
  defp format_type(_), do: "Any"

  # -- Inlay hints --------------------------------------------------------------

  @doc false
  def compute_inlay_hints(text) do
    case parse_to_ast(text) do
      {:ok, ast} ->
        ast
        |> build_symbol_table()
        |> Enum.flat_map(fn s ->
          case s do
            %{kind: :function, line: l, signature: sig} ->
              [
                %{
                  "position" => %{"line" => l - 1, "character" => 0},
                  "label" => "# " <> sig,
                  "kind" => 2,
                  "paddingRight" => true
                }
              ]

            _ ->
              []
          end
        end)

      _ ->
        []
    end
  end

  # -- Signature help -----------------------------------------------------------

  @doc false
  def compute_signature_help(text, line, char) do
    lines = String.split(text, "\n")
    target = Enum.at(lines, line, "")
    prefix = String.slice(target, 0, char)

    case Regex.run(~r/([a-z_][a-zA-Z0-9_]*)\s*\(/, prefix |> String.reverse() |> String.reverse()) do
      [_, name] ->
        case parse_to_ast(text) do
          {:ok, ast} ->
            symbols = build_symbol_table(ast)

            case Enum.find(symbols, fn s -> s.name == name and s.kind == :function end) do
              %{signature: sig} ->
                %{
                  "signatures" => [%{"label" => sig, "parameters" => []}],
                  "activeSignature" => 0,
                  "activeParameter" => 0
                }

              _ ->
                nil
            end

          _ ->
            nil
        end

      _ ->
        nil
    end
  end

  # -- Formatting ---------------------------------------------------------------

  @doc """
  Compute formatting edits for a document.

  Delegates to `Cure.Compiler.Formatter`, which performs a small set
  of source-preserving transformations (line-ending normalisation,
  trailing-whitespace stripping, tab-to-space in indentation,
  blank-line collapsing, and operator spacing) and validates the
  result against a re-parse of the original AST. Returns a single
  whole-document `TextEdit` when the formatter produces a change, or
  an empty list otherwise.
  """
  @spec compute_formatting_edits(String.t()) :: [map()]
  def compute_formatting_edits(text) when is_binary(text) do
    Formatter.format_to_edits(text)
  end

  def compute_formatting_edits(_), do: []

  # -- Rename -------------------------------------------------------------------

  @doc false
  def prepare_rename(text, line, char) do
    lines = String.split(text, "\n")
    target = Enum.at(lines, line, "")
    word = extract_word_at(target, char)

    if word == "" do
      nil
    else
      %{
        "start" => %{"line" => line, "character" => max(char - String.length(word), 0)},
        "end" => %{"line" => line, "character" => char + String.length(word)}
      }
    end
  end

  @doc false
  def compute_rename(uri, text, line, char, new_name) do
    lines = String.split(text, "\n")
    target = Enum.at(lines, line, "")
    old = extract_word_at(target, char)

    edits =
      lines
      |> Enum.with_index()
      |> Enum.flat_map(fn {l, i} ->
        case word_occurrences(l, old) do
          [] ->
            []

          ranges ->
            Enum.map(ranges, fn {start_col, end_col} ->
              %{
                "range" => %{
                  "start" => %{"line" => i, "character" => start_col},
                  "end" => %{"line" => i, "character" => end_col}
                },
                "newText" => new_name
              }
            end)
        end
      end)

    %{"changes" => %{uri => edits}}
  end

  defp word_occurrences(line, word) when word != "" do
    pattern = Regex.compile!("\\b" <> Regex.escape(word) <> "\\b")

    Regex.scan(pattern, line, return: :index)
    |> Enum.map(fn [{start, len}] -> {start, start + len} end)
  end

  defp word_occurrences(_line, _word), do: []

  # -- Code lens ----------------------------------------------------------------

  @doc false
  def compute_code_lenses(_uri, text) do
    case parse_to_ast(text) do
      {:ok, ast} ->
        ast
        |> build_symbol_table()
        |> Enum.flat_map(fn
          %{kind: :function, line: l, name: n} ->
            [
              %{
                "range" => %{
                  "start" => %{"line" => l - 1, "character" => 0},
                  "end" => %{"line" => l - 1, "character" => 0}
                },
                "command" => %{"title" => "Type | Effects", "command" => "cure.type." <> n}
              }
            ]

          _ ->
            []
        end)

      _ ->
        []
    end
  end

  # -- Semantic tokens ----------------------------------------------------------

  @doc false
  def compute_semantic_tokens(text) do
    keywords =
      ~w(fn mod rec fsm proto impl type let have proof because if then else elif match return throw try catch finally use local when requires where)

    lines = String.split(text, "\n")

    {data, _} =
      Enum.reduce(Enum.with_index(lines), {[], {0, 0}}, fn {line, idx}, {acc, prev} ->
        tokens = scan_keyword_tokens(line, keywords, idx)

        Enum.reduce(tokens, {acc, prev}, fn {l, c, len, ttype}, {acc2, {pl, pc}} ->
          delta_line = l - pl
          delta_start = if delta_line == 0, do: c - pc, else: c
          # Prepend in reverse field order so that the final Enum.reverse/1
          # produces the LSP-required 5-int tuple sequence
          # [delta_line, delta_start, length, token_type, token_modifiers].
          {[0, ttype, len, delta_start, delta_line | acc2], {l, c}}
        end)
      end)

    Enum.reverse(data)
  end

  defp scan_keyword_tokens(line, keywords, line_idx) do
    keywords
    |> Enum.flat_map(fn kw ->
      pat = Regex.compile!("\\b" <> Regex.escape(kw) <> "\\b")

      Regex.scan(pat, line, return: :index)
      |> Enum.map(fn [{start, len}] -> {line_idx, start, len, 0} end)
    end)
    |> Enum.sort()
  end

  # -- Workspace symbols --------------------------------------------------------

  @doc false
  def compute_workspace_symbols(query, documents, encoding \\ :utf16) do
    documents
    |> Enum.flat_map(fn {uri, text} ->
      case parse_to_ast(text) do
        {:ok, ast} ->
          ast
          |> build_symbol_table(text, encoding)
          |> Enum.filter(fn s -> query == "" or String.contains?(s.name, query) end)
          |> Enum.map(fn s ->
            %{
              "name" => s.name,
              "kind" => if(s.kind == :function, do: 12, else: 2),
              "location" => %{
                "uri" => uri,
                "range" =>
                  if(s.span,
                    do: Positions.range(s.span, text, encoding),
                    else: Positions.line_range(s.line, text, encoding)
                  )
              }
            }
          end)

        _ ->
          []
      end
    end)
  end

  # -- Stdin Reader (Content-Length aware) -------------------------------------

  defp lsp_reader_loop(server) do
    case read_lsp_message() do
      {:ok, message} ->
        send(server, {:lsp_message, message})
        lsp_reader_loop(server)

      :eof ->
        :ok

      {:error, _} ->
        :ok
    end
  end

  defp read_lsp_message do
    # Read headers until blank line (\r\n\r\n)
    case read_headers(%{}) do
      {:ok, headers} ->
        content_length = Map.get(headers, "content-length", "0") |> String.to_integer()

        if content_length > 0 do
          case IO.binread(:stdio, content_length) do
            data when is_binary(data) ->
              case safe_json_decode(data) do
                {:ok, msg} -> {:ok, msg}
                :error -> {:error, :json_decode}
              end

            _ ->
              :eof
          end
        else
          {:error, :no_content_length}
        end

      :eof ->
        :eof
    end
  end

  defp read_headers(acc) do
    case IO.binread(:stdio, :line) do
      line when is_binary(line) ->
        trimmed = String.trim_trailing(line, "\r\n") |> String.trim_trailing("\n")

        cond do
          # Blank line = end of headers
          trimmed == "" or trimmed == "\r" ->
            {:ok, acc}

          # Header line: Key: Value
          String.contains?(trimmed, ":") ->
            [key | rest] = String.split(trimmed, ":", parts: 2)
            value = Enum.join(rest, ":") |> String.trim()
            read_headers(Map.put(acc, String.downcase(String.trim(key)), value))

          true ->
            read_headers(acc)
        end

      _ ->
        :eof
    end
  end

  defp safe_json_decode(binary) do
    {:ok, :json.decode(binary)}
  rescue
    _ -> :error
  end
end
