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

  alias Cure.Core.{Env, Inductive, Certificate}
  alias Cure.Elab.{Program, TotalityClosure}

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

  describe "TC1: a self-call hidden inside a still-live :rewrite node bypasses termination analysis entirely" do
    # `{:rewrite, proof, motive, body}` is NOT a retired/dead node: validator.ex
    # keeps `no_rewrite_node: :warn` (not :reject) at dev time with the comment
    # "STILL PRODUCED as the transport eliminator (rewrite_plan/symmetry_proof/
    # bridge_step)" (validator.ex:209-215) — real elaborated Core terms carry it
    # today. `Cure.Core.Certificate.calls?/2` (certificate.ex:595-611) is the
    # self-call FAST PATH gating the whole size-change analysis:
    # `if calls?(name, body), do: size_change_total?(name, body), else: true`
    # (certificate.ex:110) — if `calls?` says "no self-call", the function is
    # certified total WITHOUT ANY termination analysis. `calls?/2` is hand-
    # enumerated (global/pi/lam/app/data/ctor/case) with a catch-all `false` and
    # has NO `:rewrite` clause, so a self-call sitting inside a `:rewrite`
    # node's proof/motive/body is invisible to it. A function whose only
    # self-call is hidden this way is therefore certified total unconditionally
    # -- even an unrestricted, non-decreasing self-loop. Idris/Agda/Lean's
    # termination checkers walk the FULL term grammar (every node that can host
    # a call) before ever deciding "no recursion" is a valid exit; skipping an
    # entire live node shape is not a completeness gap here, it is unsoundness:
    # the kernel would now be willing to δ-unfold a function that may not
    # terminate.
    test "Certificate.terminating?/3 must not certify a self-call reachable only through a :rewrite node" do
      dom = {:type, 0}
      self_call = {:app, {:global, :loop}, {:var, 0}}
      # loop(x) = rewrite(<proof>, <motive>, loop(x)) -- no decrease, ever.
      body = {:lam, dom, {:rewrite, dom, dom, self_call}}

      refute Certificate.terminating?(:loop, body, Env.empty())
    end
  end

  describe "TC2: a global call hidden inside a :rewrite node is invisible to TotalityClosure's type-level reachability walk" do
    # The same missing-clause shape recurs in the untrusted driver:
    # `TotalityClosure.collect/1` (totality_closure.ex:85-98) hand-enumerates
    # global/pi/lam/app/data/ctor/case with a catch-all `[]`, and also has no
    # `:rewrite` clause -- contrast `Cure.Core.Certificate.gather_globals/2`
    # (certificate.ex:549-553), which IS structurally generic (walks every
    # tuple/list) and would not miss this. A family/ctor index that calls
    # `outer`, whose body in turn calls `inner` ONLY from inside a `:rewrite`
    # node, must still require `inner` to be certified: normalising the index
    # expression may need to δ-unfold `outer` and then `inner`. Because `inner`
    # never enters the type-level set, `certify_type_level/1` never asks the
    # kernel to certify it, so a non-terminating `inner` reachable this way is
    # never caught by §7's `:totality_required` gate (soundness rests entirely
    # on this closure being complete; §7 says as much).
    #
    # NOTE: `lib/antigen/assays/totality_closure_assay.ex`'s "independent"
    # completeness oracle (`__reachable__/1` / `globals/1`) is a near-verbatim
    # COPY of this same hand-enumerated walker (same clause set, same missing
    # `:rewrite`), so the existing completeness property test can never catch
    # this: both sides of that comparison share the identical blind spot.
    test "TotalityClosure.type_level_fns/1 must find a global reachable only through a :rewrite node" do
      dec = {:data, :Dec, [], []}

      outer_body = {:lam, dec, {:rewrite, dec, dec, {:app, {:global, :inner}, {:var, 0}}}}

      env =
        Env.empty()
        |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [Inductive.ctor(:Dcoupled, [], [])])
        |> Env.add_def(:outer, {:pi, dec, dec}, outer_body)
        |> Env.add_def(:inner, {:pi, dec, dec}, {:lam, dec, {:var, 0}})
        |> Inductive.declare(Inductive.family(:Wrap, [], [{:d, dec}], 0), [
          Inductive.ctor(:mkWrap, [{:x, dec}], [{:app, {:global, :outer}, {:var, 0}}])
        ])

      assert MapSet.member?(TotalityClosure.type_level_fns(env), :inner)
    end
  end
end
