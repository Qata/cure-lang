defmodule Cure.MetaAST.ConformanceTripwireTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.MetaAST.Conformance

  @moduledoc false

  # The MetaAST-conformance tripwire over the whole first-party .cure corpus
  # (stdlib + examples + oracle probes + fixtures — every committed source).
  #
  # Metastatic's traversal loses a subterm in three ways — a `:bad_shape` tuple it
  # cannot enter, a `:node_in_meta` subterm parked in a meta value it never walks,
  # or a `:node_child` bare node in a children slot where a list was required (see
  # `Cure.MetaAST.Conformance`). The end-state invariant is ZERO of all three. The
  # corpus does not satisfy that yet (~7,000 node_in_meta + ~200 node_child/
  # bad_shape across the four trees), and it cannot be flipped to a hard "zero
  # violations" assertion without red-lighting the suite before the Option-C
  # refactor exists.
  #
  # So this is a SHRINKING ALLOWLIST. `@allowlist` is the set of {kind, tag, key}
  # buckets currently tolerated. The tripwire fails if:
  #
  #   * a NEW bucket appears that is not allowlisted — i.e. someone introduced a
  #     fresh non-conformant shape or a new meta-embedded subterm (regression), or
  #   * an allowlisted bucket no longer occurs — i.e. a migration eliminated it and
  #     the entry is now STALE and must be deleted (keeps the allowlist honest and
  #     forces it to shrink).
  #
  # Each Option-C step deletes the bucket it fixes from this list. The allowlist
  # reaching `[]` is the definition of done.
  @allowlist MapSet.new([
               {:bad_shape, :builtin, nil},
               # `erases` erasure-grade annotation in the OTP raw-algebra module;
               # same tolerated backlog class as the other :bad_shape buckets.
               {:bad_shape, :erases, nil},
               {:bad_shape, :group, nil},
               {:bad_shape, :named_dom, nil},
               {:bad_shape, :named_implicit_pat, nil},
               {:node_child, :forced_pattern, nil},
               {:node_child, :gadt_ctor, nil},
               # Typed assignment (`x: T = e`) inside the OTP macro templates
               # (actor/app/fsm/supervisor): the `:type_annotation` rides in meta.
               {:node_in_meta, :assignment, :type_annotation},
               {:node_in_meta, :bin_segment, :size},
               {:node_in_meta, :container, :decorator},
               {:node_in_meta, :container, :for_type},
               {:node_in_meta, :function_call, :callee},
               {:node_in_meta, :function_def, :constraints},
               {:node_in_meta, :function_def, :guards},
               {:node_in_meta, :function_def, :params},
               {:node_in_meta, :function_def, :return_type},
               {:node_in_meta, :implementation, :for_type},
               {:node_in_meta, :indexed_type, :decorator},
               {:node_in_meta, :indexed_type, :indices},
               {:node_in_meta, :indexed_type, :params},
               {:node_in_meta, :lambda, :params},
               {:node_in_meta, :lift_module, :declarations},
               {:node_in_meta, :match_arm, :guard},
               {:node_in_meta, :match_arm, :pattern},
               {:node_in_meta, :param, :default},
               {:node_in_meta, :param, :type},
               {:node_in_meta, :with_rematch_arm, :parent_patterns},
               {:node_in_meta, :with_rematch_arm, :pattern}
             ])

  # Every committed first-party .cure tree. Detection is structural, so widening
  # the corpus only ever adds buckets — it never changes how a node is judged.
  @corpus_globs [
    "lib/std/*.cure",
    "examples/**/*.cure",
    "test/oracle/**/*.cure",
    "test/fixtures/*.cure"
  ]

  defp corpus_buckets do
    @corpus_globs
    |> Enum.flat_map(&Path.wildcard/1)
    |> Enum.uniq()
    |> Enum.reduce({MapSet.new(), []}, fn file, {buckets, failed} ->
      with {:ok, toks} <- Lexer.tokenize(File.read!(file), emit_events: false),
           {:ok, ast} <- Parser.parse(toks, emit_events: false) do
        {MapSet.union(buckets, Conformance.violation_buckets(ast)), failed}
      else
        _ -> {buckets, [Path.basename(file) | failed]}
      end
    end)
  end

  test "every first-party file parses (a parse failure would silently shrink coverage)" do
    {_buckets, failed} = corpus_buckets()
    assert failed == [], "files failed to parse: #{Enum.join(failed, ", ")}"
  end

  test "no MetaAST-conformance violation outside the allowlist" do
    {buckets, _failed} = corpus_buckets()
    unexpected = MapSet.difference(buckets, @allowlist)

    assert MapSet.equal?(unexpected, MapSet.new()), """
    New MetaAST-conformance violation(s) not in the allowlist:

    #{format(unexpected)}

    A subterm here is invisible to Metastatic's traversal (RAG/MCP/migrator).
    Either bring the node to the conformant shape (subterm in children, scalars
    in meta) or, if this is a deliberate new construct, add its {kind, tag, key}
    bucket to @allowlist in this file with a note.
    """
  end

  test "the allowlist has no stale entries (forces it to shrink as C lands)" do
    {buckets, _failed} = corpus_buckets()
    stale = MapSet.difference(@allowlist, buckets)

    assert MapSet.equal?(stale, MapSet.new()), """
    Allowlisted bucket(s) no longer occur in the corpus:

    #{format(stale)}

    These were fixed (or the construct was removed). Delete them from @allowlist —
    the allowlist must only ever shrink.
    """
  end

  defp format(set) do
    set
    |> Enum.sort()
    |> Enum.map_join("\n", fn {kind, tag, key} -> "  #{kind}  #{inspect(tag)}  #{inspect(key)}" end)
  end
end
