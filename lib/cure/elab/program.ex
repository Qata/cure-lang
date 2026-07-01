defmodule Cure.Elab.Program do
  @moduledoc """
  Whole-program elaboration (design spec §5, M9.2 wiring): lex + parse a source
  string, elaborate every declaration into the `Cure.Core` signature, then run
  the type-level totality closure so that any function reduced by the type
  checker is kernel-certified total (§7). Returns the fully-elaborated,
  totality-certified signature.
  """

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.Env
  alias Cure.Elab.{Declarations, Erase, TotalityClosure}

  @spec elaborate(String.t()) :: {:ok, Env.t()} | {:error, term()}
  def elaborate(source) when is_binary(source) do
    with {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false),
         {:ok, env} <- elaborate_declarations(declarations(ast), Env.empty()) do
      TotalityClosure.certify_type_level(env)
    end
  end

  @doc """
  Codegen gate (§6 negative #5): a program with an unfilled hole typechecks but
  must not be emitted. Returns `{:error, {:unfilled_hole, name}}` for the first
  definition that still carries a hole.
  """
  @spec check_codegen_ready(Env.t()) :: :ok | {:error, {:unfilled_hole, atom()}}
  def check_codegen_ready(%Env{defs: defs}) do
    case Enum.find(defs, fn {_name, %{body: body}} -> Erase.has_hole?(body) end) do
      nil -> :ok
      {name, _def} -> {:error, {:unfilled_hole, name}}
    end
  end

  defp declarations({:block, _meta, items}), do: items
  defp declarations(single), do: [single]

  defp elaborate_declarations(items, env) do
    Enum.reduce_while(items, {:ok, env}, fn decl, {:ok, acc} ->
      case Declarations.elaborate(decl, acc) do
        {:ok, acc2} -> {:cont, {:ok, acc2}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end
end
