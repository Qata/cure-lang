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
end
