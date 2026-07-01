defmodule Antigen.Backend.StreamData do
  @moduledoc "The StreamData backend — the ONLY module allowed to reference StreamData."
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

  @impl true
  def sample(native, count), do: Enum.take(native, count)
end
