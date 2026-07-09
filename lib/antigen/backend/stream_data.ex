defmodule Antigen.Backend.StreamData do
  @moduledoc "The StreamData backend — the ONLY module allowed to reference StreamData."
  # `stream_data` is a `:test`-only dep (mix.exs), so in dev/prod compiles the
  # module is absent. That is by design — this backend is swappable and only the
  # test suite drives it — so silence the expected "undefined" warnings here
  # rather than pulling the dep into every environment.
  @compile {:no_warn_undefined, StreamData}
  @behaviour Antigen.Backend

  @impl true
  def interp({:return, x}), do: StreamData.constant(x)
  def interp({:member_of, xs}), do: StreamData.member_of(xs)
  def interp({:one_of, gs}), do: StreamData.one_of(Enum.map(gs, &interp/1))
  def interp({:frequency, ws}), do: StreamData.frequency(Enum.map(ws, fn {w, g} -> {w, interp(g)} end))
  def interp({:bind, g, f}), do: StreamData.bind(interp(g), fn x -> interp(f.(x)) end)
  def interp({:sized, f}), do: StreamData.sized(fn n -> interp(f.(n)) end)
  def interp({:resize, n, g}), do: StreamData.resize(interp(g), n)
  def interp({:tagged, _tag, g}), do: interp(g)

  # Deferred construction: `fun.()` (which builds the sub-generator's reified AST)
  # and its `interp` run only when generation descends here, so a recursive
  # generator unfolds one sampled path at a time. `bind` over a constant is the
  # StreamData idiom for "don't build this until asked".
  def interp({:lazy, fun}), do: StreamData.bind(StreamData.constant(nil), fn _ -> interp(fun.()) end)

  @impl true
  def sample(native, count), do: Enum.take(native, count)
end
