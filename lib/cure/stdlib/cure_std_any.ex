defmodule :cure_std_any do
  @moduledoc """
  Runtime backend for `Std.Access`'s `Any` top type.

  `Std.Access` models Elixir's dynamic, heterogeneous
  [`Access`](https://hexdocs.pm/elixir/Access.html) behaviour: an accessor
  list walks nested maps, keyword-lists, and tuples whose element types are
  not known statically. Cure's dependent pipeline has no top type, so the
  module declares `opaque type Any` and lifts values across the typed/untyped
  boundary through `to_any`/`as_map`/`as_list`, each an `@extern` to
  `coerce/1` below.

  `coerce/1` is the identity — the BEAM is untyped, so lifting a value to
  `Any` (or lowering it back to a concrete container shape) is a no-op at
  runtime. This is exactly Idris's `believe_me`: the trust lives entirely in
  the `@extern` boundary (the same trust class as every other Cure FFI
  binding), and the kernel is never asked to prove the coercion sound. It is
  quarantined to this one dynamic-access module.
  """

  @doc "Identity coercion — the believe_me trust point for `Std.Access`."
  def coerce(x), do: x
end
