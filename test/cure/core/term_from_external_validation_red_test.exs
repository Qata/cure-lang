defmodule Cure.Core.TermFromExternalValidationRedTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Serialize, Term}

  # FINDING B (lib/cure/core/term.ex:374 `from_external/1`):
  #
  # `Serialize.decode/1` is documented (serialize.ex:104-113) as the trust
  # boundary for untrusted on-disk term encodings: after building the raw
  # tuple it re-checks the result against `Term.term?/1` and rejects malformed
  # shapes such as `{:var, -1}` (a negative de Bruijn index), returning
  # `{:error, {:ill_formed_term, {:var, -1}}}` instead of a term an independent
  # checker could be handed.
  #
  # `Term.from_external/1` is the OTHER external-decode entry point for the
  # exact same node grammar (same "node"/"index" JSON-able map shape
  # `to_external/1` produces) and is exercised by `term_test.exs`'s "fails
  # closed" test for unknown atoms (K12 §D) — i.e. it is understood elsewhere
  # in this suite to have a real untrusted-input threat model, and it DOES
  # already fail closed for one class of malformed input (atoms it has never
  # interned). But for a malformed *integer* field — a negative "index", the
  # very case `Serialize.decode` calls out by name in its own justifying
  # comment — `from_external/1` has no `Term.term?/1` gate at all and silently
  # builds `{:var, -1}`, a shape `Term.term?/1` itself rejects.
  test "from_external rejects a negative de Bruijn index the same way Serialize.decode rejects it" do
    malformed_index = -1

    # The `Serialize` entry point for the identical malformed value is
    # rejected outright: it never returns the ill-formed tuple to a caller.
    assert {:error, {:ill_formed_term, {:var, -1}}} ==
             Serialize.decode("(var #{malformed_index})")

    # `Term.from_external/1` is fed the analogous untrusted external encoding
    # (the same "node"/"index" shape `to_external({:var, k})` produces, per
    # term.ex:312). Whatever it returns must be a well-formed term — the same
    # invariant `Serialize.decode` enforces — not the raw, ungated
    # `{:var, -1}` that `Term.term?/1` itself considers ill-formed.
    assert_raise ArgumentError, ~r/ill-formed external Core term/, fn ->
      Term.from_external(%{"node" => "var", "index" => malformed_index})
    end
  end
end
