defmodule Cure.Kernel.Backend do
  @moduledoc """
  Runtime-selectable dependent-kernel backend.

  `:elixir_core` preserves the in-process `Cure.Core.Kernel` path. `:lean`
  routes dependent checking through the Lean bridge once translation is present.
  Selection order is explicit option, application config, then
  `CURE_KERNEL_BACKEND`. The default remains `:elixir_core` during migration.
  """

  @type backend_name :: :elixir_core | :lean

  @callback check_ast(tuple() | list(), keyword()) :: {:ok, Cure.Core.Env.t()} | {:error, term()}

  @spec check_ast(tuple() | list(), keyword()) :: {:ok, Cure.Core.Env.t()} | {:error, term()}
  def check_ast(ast, opts \\ []) do
    with {:ok, module} <- backend_module(opts) do
      module.check_ast(ast, opts)
    end
  end

  @spec selected_backend(keyword()) :: {:ok, backend_name()} | {:error, term()}
  def selected_backend(opts \\ []) do
    opts
    |> raw_backend()
    |> normalize_backend()
  end

  @spec backend_module(keyword()) :: {:ok, module()} | {:error, term()}
  def backend_module(opts \\ []) do
    case selected_backend(opts) do
      {:ok, :elixir_core} -> {:ok, Cure.Kernel.Backend.ElixirCore}
      {:ok, :lean} -> {:ok, Cure.Kernel.Backend.Lean}
      {:error, _} = err -> err
    end
  end

  defp raw_backend(opts) do
    Keyword.get(opts, :kernel_backend) ||
      Application.get_env(:cure, :kernel_backend) ||
      System.get_env("CURE_KERNEL_BACKEND") ||
      :elixir_core
  end

  defp normalize_backend(value) when value in [:elixir_core, :lean], do: {:ok, value}
  defp normalize_backend("elixir_core"), do: {:ok, :elixir_core}
  defp normalize_backend("lean"), do: {:ok, :lean}

  defp normalize_backend(value) when is_binary(value) do
    case value |> String.trim() |> String.downcase() do
      "elixir_core" -> {:ok, :elixir_core}
      "elixir-core" -> {:ok, :elixir_core}
      "elixir" -> {:ok, :elixir_core}
      "lean" -> {:ok, :lean}
      other -> {:error, {:unknown_kernel_backend, other}}
    end
  end

  defp normalize_backend(value), do: {:error, {:unknown_kernel_backend, value}}
end
