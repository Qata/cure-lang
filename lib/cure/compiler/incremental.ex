defmodule Cure.Compiler.Incremental do
  @moduledoc """
  Interface-level incremental driver for multi-file Cure builds.

  Recompiles a module only when its source content changed, one of its output
  beams is missing, a direct dependency's interface changed, or the compiler
  itself changed. See `docs/superpowers/specs/2026-07-18-incremental-compilation-design.md`.
  """

  @doc """
  SHA-256 of a module's elaborated `export_env` — the exact artifact consumers
  merge in. If two versions of a module produce a byte-identical `export_env`,
  no consumer's compilation can differ, so its dependents need not recompile.
  """
  @spec interface_hash(map()) :: binary()
  def interface_hash(export_env) do
    :crypto.hash(:sha256, :erlang.term_to_binary(export_env, [:deterministic]))
  end
end
