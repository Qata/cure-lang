defmodule Cure.Audit.EraseRelevanceTest do
  @moduledoc """
  Audit of `Cure.Elab.Erase` / `Cure.Elab.Relevance` (the `{0,ω}` erasure pass
  and its soundness-dual relevance check). Each test is a specific, executable
  correctness claim that is RED today and should turn GREEN once the
  corresponding gap is fixed. See the audit report for full rationale;
  comments above each test summarize the bug, why it is wrong, and what
  Idris's `Core/LinearCheck.idr` / Agda's `@0` erasure do instead.
  """
  use ExUnit.Case, async: true
  @moduletag :audit

  alias Cure.Elab.{Erase, Program}
  alias Cure.Core.Inductive

  # -- shared fixtures ---------------------------------------------------------

  # `SNat` mirrors the indexed-singleton shape used throughout the existing
  # erasure/relevance test suite (erasure_relevance_test.exs, kernel-adjacent
  # tests): `ssuc`'s auto-generalized index `n` is an erased implicit
  # (position 0), its explicit `SNat(n)` argument is present (position 1) —
  # quantities `[:erased, :present]`, arity 2.
  @snat_preamble """
    type Nat = Z | S(Nat)
    type SNat indices (n: Nat)
      szero : SNat(Z)
      ssuc : SNat(n) -> SNat(S(n))
  """

  defp snat_env do
    {:ok, env} = Program.elaborate("mod P\n" <> @snat_preamble <> "end\n")
    env
  end

  # `Box`'s sole constructor `bmk : Box(m)` has exactly ONE field: the
  # auto-generalized erased implicit index `m` (quantities `[:erased]`,
  # arity 1) — a "collapsible-looking" but still ordinary (non-collapsible,
  # since Box has an index, not a proof-only carrier) ctor. Copied verbatim
  # from test/cure/elab/named_implicit_tail_test.exs's "C-c prerequisite"
  # preamble.
  @box_preamble """
    type Nat = Z | S(Nat)
    type Box indices (n: Nat)
      bmk : Box(m)
  """

  defp box_env do
    {:ok, env} = Program.elaborate("mod P\n" <> @box_preamble <> "end\n")
    env
  end

  # The elaborated ctor/global name may be bare or module-qualified
  # (`:bmk` vs `:"P.bmk"`); pick whichever this env actually resolves.
  # Copied from named_implicit_tail_test.exs.
  defp ctor_atom(env, base) do
    Enum.find([base, String.to_atom("P." <> to_string(base))], base, fn c ->
      is_list(Inductive.ctor_quantities(env, c))
    end)
  end

  # ---------------------------------------------------------------------------
  # ER2 — Erase.erase does not drop erased ctor args when the ctor heads a
  # curried `:app` spine instead of appearing as one flat `{:ctor, name, args}`
  # node
  # ---------------------------------------------------------------------------

  # THE BUG: `Erase.erase/2`'s `{:app, _, _}` clause (erase.ex:42-78) only
  # special-cases a `{:global, name}` spine head — every other head (line
  # 73-77, the bare `_ ->` fallback) is passed through with NO quantity-based
  # arg filtering at all:
  #
  #     _ ->
  #       args
  #       |> Enum.map(&erase(env, &1))
  #       |> Enum.reduce(erase(env, head), fn arg, acc -> {:app, acc, arg} end)
  #
  # `Cure.Elab.Relevance`'s dual function, `callee_quantities/3`
  # (relevance.ex:188-199), explicitly anticipates a `{:ctor, cname, _args}`
  # spine head and computes its erased/present split from
  # `Inductive.ctor_quantities/2` — the SAME lookup `Erase.erase`'s own
  # `{:ctor, ...}` clause (erase.ex:20-38) uses for a flat ctor node. So the
  # two files DISAGREE about what an app-spine-headed constructor means:
  # Relevance is prepared to treat it exactly like a flat ctor application
  # (erased-then-present split), but Erase keeps every argument, erased ones
  # included.
  #
  # The result: erasing the SAME logical constructor application produces
  # two different runtime shapes depending purely on which of two
  # structurally-equivalent Core encodings was used (one flat `{:ctor, ...}`
  # node vs. the same constructor curried through `:app`) — breaking both
  # the "erase drops every `:erased` constructor argument" invariant (an
  # erased value literally survives into the runtime term, violating the
  # zero-footprint guarantee) and confluence between two term shapes that
  # both type-check to the same value (Idris/Agda erasure is invariant under
  # such eta-shape differences; Cure's is not).
  test "ER2: erasing a constructor via a curried app-spine must match erasing the same constructor as one flat node" do
    env = snat_env()
    ssuc = ctor_atom(env, :ssuc)

    erased_index_val = {:nat_lit, 0}
    present_val = {:ctor, ctor_atom(env, :szero), []}

    direct = Erase.erase(env, {:ctor, ssuc, [erased_index_val, present_val]})

    via_app_spine =
      Erase.erase(env, {:app, {:app, {:ctor, ssuc, []}, erased_index_val}, present_val})

    assert via_app_spine == direct
  end

  # ---------------------------------------------------------------------------
  # ER3 — Relevance.walk's `:ctor` clause silently misaligns a shrunk
  # (already-partially-erased-shaped) constructor argument list
  # ---------------------------------------------------------------------------

  # THE BUG: `Relevance.walk`'s `{:ctor, cname, args}` clause (relevance.ex:
  # 111-119) zips `args` against the ctor's FULL registered quantity vector
  # with no length guard:
  #
  #     quantities = Inductive.ctor_quantities(st.env, cname) || ...
  #     args |> Enum.zip(quantities) |> each(...)
  #
  # `Enum.zip/2` silently truncates to the shorter list. If `args` is
  # SHORTER than `quantities` — exactly the shape `Erase.erase`'s OWN
  # `{:ctor, ...}` clause (erase.ex:20-38) explicitly documents and guards
  # against ("Fewer ... args than the ctor's full arity means the term is
  # ALREADY ERASED — re-zipping the full quantity vector against the shrunk
  # arg list would realign survivors onto leading positions and DROP them" —
  # erase.ex:32-37) — the raw zip here re-aligns the survivor(s) onto the
  # LEADING quantity-vector positions instead of their true (trailing, post-
  # erasure) positions. A genuinely PRESENT survivor lands on an `:erased`
  # label and is silently exempted from the relevance check — the exact
  # false negative Erase.erase's own comment warns about, just on the
  # Relevance side, which has no matching guard.
  #
  # `ssuc`'s real quantities are `[:erased, :present]` (erased index `n` at
  # position 0, present `SNat(n)` field at position 1). By Erase.erase's own
  # documented convention, a shrunk one-arg `ssuc` ctor node is a term whose
  # erased field has ALREADY been dropped, so its surviving arg occupies the
  # ORIGINAL present slot (position 1) — Relevance, as the "exact dual" of
  # Erase (relevance.ex:5-7 moduledoc), must classify it the same way. It
  # currently does not: the raw zip labels the sole surviving arg with
  # quantities[0] = `:erased` and skips it outright.
  test "ER3: Relevance.check must not silently exempt a shrunk ctor's surviving argument" do
    env = snat_env()
    ssuc = ctor_atom(env, :ssuc)

    # A shrunk ctor node (one arg where the real arity is two) whose sole
    # surviving argument is the OUTER erased parameter — a genuinely
    # relevant (present-field) use once the shrunk shape is read the same
    # way Erase.erase reads it.
    body = {:ctor, ssuc, [{:var, 0}]}

    assert {:error, {:erased_used_relevantly, _}} =
             Cure.Elab.Relevance.check(env, :probe2, [:erased], body)
  end
end
