defmodule Cure.Stdlib.PreloadStickyTest do
  # async: false — mutates the global code table (loads/sticks a throwaway module).
  use ExUnit.Case, async: false

  alias Cure.Stdlib.Preload

  @throwaway :"Cure.Std.PreloadStickyProbe"

  # A minimal, valid BEAM binary for @throwaway: -module(...). with no exports.
  defp probe_binary do
    forms = [
      {:attribute, 1, :module, @throwaway},
      {:attribute, 1, :export, []}
    ]

    {:ok, @throwaway = mod, binary} = :compile.forms(forms, [:return_errors])
    {mod, binary}
  end

  test "a stuck stdlib module refuses load_binary and preload tolerates it" do
    {mod, binary} = probe_binary()

    # Load then stick it, mimicking the C1 startup stanza.
    # NB: `:code.stick_mod/1` returns `true` (not `:ok`) — pattern-match on `true`.
    {:module, ^mod} = :code.load_binary(mod, ~c"nofile", binary)
    true = :code.stick_mod(mod)

    try do
      assert :code.is_sticky(mod)

      # A second load is refused with :sticky_directory (the property Preload must tolerate).
      assert {:error, :sticky_directory} = :code.load_binary(mod, ~c"nofile", binary)

      # A preload pass that would otherwise reload stdlib modules must still return :ok,
      # i.e. it swallows the :sticky_directory refusal rather than raising.
      assert Preload.preload(kind: :none) == :ok
    after
      :code.unstick_mod(mod)
      :code.purge(mod)
      :code.delete(mod)
    end
  end
end
