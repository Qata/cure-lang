defmodule Cure.Audit.CoherenceSubstTotalityTest do
  @moduledoc """
  Red tests for an audit of `lib/cure/elab/coherence.ex`, `lib/cure/elab/subst.ex`,
  and `lib/cure/elab/totality_closure.ex` (2026-07-10). Every test here is a
  specific executable claim of CORRECT behaviour that fails today. See each
  test's leading comment for the bug, why it is wrong, and what Idris/Agda/Lean
  do instead.
  """
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Elab.Program

  # ===========================================================================
  # CO — Cure.Elab.Coherence (global typeclass coherence)
  # ===========================================================================


  describe "CO2: an instance for a typealias that unfolds to an already-instantiated type is not detected as an overlap" do
    # `Cure.Elab.Implementation.register/2` (implementation.ex:31-32) derives the
    # coherence key's `head` from `meta[:for]`, which the parser
    # (compiler/parser.ex:3658-3663) sets to the RAW SURFACE NAME of the `for`
    # clause — `{:variable, _, n} -> n` for a bare name, with ZERO semantic
    # typealias unfolding. `typealias MyInt = Int` is a "TRANSPARENT type
    # synonym" (parser.ex:2979 comment) at the type-checking level, but
    # coherence keys `for Int` and `for MyInt` under two DIFFERENT atoms
    # (`:Int` vs `:MyInt`), so both anonymous instances register successfully —
    # two live dictionaries for what is definitionally the SAME type. Idris/
    # Agda/Lean/Rust coherence resolves the type to its head NORMAL FORM (through
    # transparent synonyms) before comparing/keying instances, precisely to rule
    # this out; two dictionaries for one type means an expression using `eqs`
    # can compute two different answers depending on which spelling of the type
    # the call site happens to use.
    test "an anonymous instance for Int and one for a transparent alias of Int overlap" do
      src = """
      mod M
        typealias MyInt = Int
        interface Eqs(a)
          fn eqs(x: a, y: a) -> Bool
        implementation Eqs for Int
          fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
        implementation Eqs for MyInt
          fn eqs(x: MyInt, y: MyInt) -> Bool = int_eq(x, y)
      end
      """

      assert {:error, {:overlapping_instance, :Eqs, :Int}} = Program.elaborate(src)
    end
  end

  # ===========================================================================
  # TC — Cure.Elab.TotalityClosure (untrusted type-level totality driver)
  # ===========================================================================

end
