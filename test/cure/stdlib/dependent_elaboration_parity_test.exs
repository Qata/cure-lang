defmodule Cure.Stdlib.DependentElaborationParityTest do
  @moduledoc """
  #18-readiness firewall for the STANDARD LIBRARY. Every stdlib module listed in
  `@green` must elaborate on the DEPENDENT pipeline (`Cure.Elab.Program.elaborate/1`
  resolves `use` imports from `lib/std`). This locks the value-surface-parity work
  (#23) in as an immutable regression set: the classic pipeline
  (`lib/cure/compiler/codegen.ex`, `lib/cure/types/*`) is slated for deletion once
  the stdlib reaches full dependent parity, and until then a silent regression in
  ANY green module's dependent elaboration would otherwise go uncaught (only a
  handful of modules had individual `*_elaborates_test.exs` guards).

  The `@green` list only ever GROWS. The eight modules NOT listed are the known
  remaining blockers, documented for the rip-out ledger (do NOT assert they fail —
  that would freeze current brokenness; they are promoted into `@green` as they are
  fixed):

    * `access`, `app` — irreducibly `Any`-typed (dynamic heterogeneous access /
      OTP `application:get_env` config `term()`); blocked on the `Any` top-type
      design fork (no in-language lower-risk default). `app` additionally needs
      `get_env/2` vs `/3` arity overloading.
    * `show`, `io` — dependent-green WITH `use Std.String` + `use Std.Semigroup`
      (proven separately), but the committed files omit those imports because the
      CLASSIC checker breaks on them (String=List(Char) vs binary). They flip green
      the instant classic is deleted.
    * `set` — needs a parameterised `Map(k, v)` (breaks classic) plus the
      foldl-accumulator poly-seed elaborator fix
      (`fold_accumulator_poly_seed_reach_test.exs`).
    * `http`, `regex` — AtomVM dead-ends (`:inets`/`:re` absent); excluded from the
      parity target by design.
    * `pair` — bare-`Tuple`/`Any` shaped, slated for retirement in favour of
      `Std.Tuple` + `Std.Match`; excluded.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @green ~w(
    actor atom binary bool bounded char comparable core crdt decision equatable
    equivalent float fsm functor gen int iter json list map match math nat
    non_empty option process proof result semigroup sigma string supervisor
    system telescope test time tuple unit vector
  )

  test "every dependent-green stdlib module elaborates on the dependent pipeline" do
    failures =
      Enum.reduce(@green, [], fn name, acc ->
        path = Path.join("lib/std", name <> ".cure")

        result =
          try do
            Program.elaborate(File.read!(path))
          rescue
            e -> {:raise, Exception.message(e)}
          catch
            kind, value -> {:raise, "#{inspect(kind)}: #{inspect(value)}"}
          end

        case result do
          {:ok, _env} -> acc
          other -> [{name, inspect(other, limit: 5)} | acc]
        end
      end)

    assert failures == [],
           "stdlib modules regressed on the dependent pipeline:\n" <>
             Enum.map_join(Enum.reverse(failures), "\n", fn {n, e} -> "  Std.#{n}: #{e}" end)
  end

  # The classic-coexistence contract: `show`/`io` elaborate cleanly on the
  # dependent pipeline the instant they can carry their held-out imports
  # (`use Std.String` + `use Std.Semigroup`). The committed files omit those
  # imports ONLY because the CLASSIC checker breaks on them (String=List(Char) vs
  # binary), so they cannot appear in the `@green` scan above — but they flip green
  # the moment classic is deleted (#18). This guard locks that "green-on-deletion"
  # property in as a regression: a future break in `show`/`io`'s dependent side is
  # caught HERE rather than only at rip-out time. `io` genuinely needs BOTH imports
  # (its `<>` routes through `Std.Semigroup.combine`).
  @coexistence [{"show", ~w(Std.String Std.Semigroup)}, {"io", ~w(Std.String Std.Semigroup)}]

  test "classic-coexistence modules (show/io) elaborate once their held-out imports are added" do
    failures =
      Enum.reduce(@coexistence, [], fn {name, uses}, acc ->
        src = inject_uses(Path.join("lib/std", name <> ".cure"), uses)

        result =
          try do
            Program.elaborate(src)
          rescue
            e -> {:raise, Exception.message(e)}
          catch
            kind, value -> {:raise, "#{inspect(kind)}: #{inspect(value)}"}
          end

        case result do
          {:ok, _env} -> acc
          other -> [{name, inspect(other, limit: 5)} | acc]
        end
      end)

    assert failures == [],
           "classic-coexistence modules no longer elaborate with imports (green-on-" <>
             "deletion contract broken):\n" <>
             Enum.map_join(Enum.reverse(failures), "\n", fn {n, e} -> "  Std.#{n}: #{e}" end)
  end

  # Insert `use <mod>` lines immediately after the `mod …` header line, mirroring
  # how `Cure.Stdlib.Preload` would supply them once classic is gone.
  defp inject_uses(path, uses) do
    lines = String.split(File.read!(path), "\n")
    {pre, [mod_line | post]} = Enum.split_while(lines, &(not String.match?(&1, ~r/^\s*mod\s/)))
    use_lines = Enum.map(uses, &("  use " <> &1))
    Enum.join(pre ++ [mod_line] ++ use_lines ++ post, "\n")
  end
end
