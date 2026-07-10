defmodule Antigen.KernelDependentMatchTailsTest do
  @moduledoc """
  Coverage-plateau follow-up (index-unification / dependent-matching TAILS).

  The campaign hard-plateaued at 90.2% kernel line coverage: the pre-existing
  `BranchUnify` generator/assay exercised the HEAD of the index unifier (a fresh
  bind, a consistent re-bind, a same-key merge conflict, rigid-head clashes) but
  never emitted the shapes that reach:

    - the occurs-check (`var_cycle?`/`strongly_rigid_occurs?`, kernel.ex 1028/1038)
    - the compact-Nat-literal <-> ctor-tower bridge in `unify_one` (1003/1006/1009)
    - `unify_spine`'s element-wise `:undecided`-drop arm (1047)
    - the multi-key union-find self-loop no-op in `bind_index` (1073)
    - `subst_params`'s `:data`/`:case` recursion arms (953, 960, 961)
    - `apply_motive_checked`'s two bad-motive halts (634, 635)

  This test drives `Antigen.Generators.BranchUnify.gen/1` through its assay
  (`Antigen.Assays.BranchUnify`) via a real `Antigen.Runner.explore/1` campaign,
  instrumented with `:cover`, and asserts every one of those lines is now hit.
  Before the generator/assay extension (see git history), every line below was
  permanently cold — 4000+ iterations of the full mixed campaign moved zero of
  them (see the campaign coverage plateau note).

  Three lines from the same tails are proven UNREACHABLE / impractical given the
  kernel's current invariants and are deliberately NOT asserted here:

    - 1055 (`unify_spine`'s length-mismatch catch-all): unreachable — both callers
      of `unify_spine` (`unify_one`'s `:ctor`/`:data` clauses) already guard equal
      spine length before recursing, and the recursive calls stay in lockstep.
    - 1217 (`replace_branch_var`'s "same var" no-op inside `replace_branch_vars`):
      unreachable — `subst` is a union-find forest maintained by `bind_index`
      (only 3 `Map.put`/`Map.merge`/`Map.new` sites in the whole file), and the
      forest invariant it maintains means a key is never re-mapped to itself by
      the time `replace_branch_vars` walks it.
    - 1223 (`resolve_index_var`'s depth-bound defensive fallback, mirrored in
      `replace_branch_var`): constructible only via a ~100,000-entry union-find
      staleness chain; the sibling comment on `resolve_index_var` states the
      bound "is never hit" in practice. Not built (impractical, not unreachable).
  """
  use ExUnit.Case, async: false
  alias Antigen.{Cover, Runner}

  @target_lines [953, 960, 961, 1003, 1006, 1009, 1028, 1038, 1047, 1073, 634, 635]

  test "the BranchUnify generator drives its assay through every dependent-matching tail" do
    tmp = Path.join("tmp", "antigen_kernel_tails_#{System.unique_integer([:positive])}")
    File.mkdir_p!(tmp)

    cov =
      Cover.with_cover([Cure.Core.Kernel], fn ->
        _ =
          Runner.explore(
            gen: Antigen.Generators.BranchUnify.gen(),
            count: 3000,
            corpus_path: Path.join(tmp, "corpus.sexp"),
            seeds_path: Path.join(tmp, "seeds.sexp"),
            report_dir: tmp,
            bias: false,
            seed: 7
          )

        Cover.line_coverage(Cure.Core.Kernel)
      end)

    File.rm_rf!(tmp)

    missing = Enum.reject(@target_lines, &(&1 in cov.covered))

    assert missing == [],
           "kernel.ex tail lines not covered by the campaign: #{inspect(missing)}"
  end
end
