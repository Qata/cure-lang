defmodule Antigen.Generators.ElabGuardLint do
  @moduledoc """
  Lint-soundness vertical for the Z3 guard-coverage lint (spec
  2026-07-08-guard-coverage-lint §6, locked Antigen-V6 decision): source-level
  `:elab_program` challenges pinning that `guard_chain`'s exhaustiveness
  recovery accepts exactly the hand-verified-exhaustive guard sets and nothing
  else. `drop_guard` (`:flip`) is the load-bearing pin: removing one guard
  from a proven-exhaustive set MUST flip accept -> reject — a lint that keeps
  accepting is over-proving (the soundness failure this assay exists to catch).
  `alpha_rename` (`:same`) pins frame-insensitivity. Transforms operate on the
  probe-fn BODY only, never `preamble <> body`.
  """

  alias Antigen.Challenge

  @preamble """
    type Nat = Z | S(Nat)
  """

  @doc "Wrap a probe body into a self-contained, elaborable module."
  @spec module(String.t()) :: String.t()
  def module(body), do: "mod P\n" <> @preamble <> body <> "end\n"

  # -- Two-sided catalog: {id, expect, expect_error | nil, note, body} ---------
  @catalog [
    {"exhaustive/trichotomy", :accept, nil,
     "lt/eq/gt trichotomy over Int, no catch-all — the headline recovery cell",
     """
       fn cmp(a: Int, b: Int) -> Nat = match a
         x when x < b -> Z()
         x when x == b -> S(Z())
         x when x > b -> S(S(Z()))
     """},
    {"exhaustive/complement", :accept, nil,
     "two-guard complement over Int, no catch-all",
     """
       fn cmp(a: Int, b: Int) -> Nat = match a
         x when x < b -> Z()
         x when x >= b -> S(Z())
     """},
    {"gap/missing_eq", :reject, :unsupported_guard,
     "lt/gt with the equality case missing — genuinely non-exhaustive",
     """
       fn cmp(a: Int, b: Int) -> Nat = match a
         x when x < b -> Z()
         x when x > b -> S(Z())
     """},
    {"untranslatable/user_fn", :reject, :unsupported_guard,
     "semantically exhaustive via user Bool fns, but outside the fragment — K13 keeps it rejected",
     """
       fn pos(i: Int) -> Bool = i > 0
       fn nonpos(i: Int) -> Bool = i <= 0
       fn cls(n: Int) -> Nat = match n
         x when pos(x) -> Z()
         x when nonpos(x) -> S(Z())
     """},
    {"shadowed/with_catchall", :accept, nil,
     "repeated guard with a catch-all — warns (channel tested at unit level) but accepts",
     """
       fn cls(n: Int, b: Int) -> Nat = match n
         x when x < b -> Z()
         x when x < b -> S(Z())
         x -> S(S(Z()))
     """},
    {"control/guarded_catchall", :accept, nil,
     "structurally exhaustive control — the lint never runs here",
     """
       fn cls(n: Int) -> Nat = match n
         x when x == 0 -> Z()
         x -> S(Z())
     """}
  ]

  @doc "All two-sided catalog challenges as `%Challenge{}` structs (deterministic)."
  @spec guard_lint_challenges() :: [Challenge.t()]
  def guard_lint_challenges do
    Enum.map(@catalog, fn {id, expect, err, note, body} ->
      payload = %{id: id, src: module(body), expect: expect}
      payload = if err, do: Map.put(payload, :expect_error, err), else: payload

      Challenge.new(
        kind: :elab_program,
        assay: "elab/guard_lint",
        label: expect,
        payload: payload,
        note: note
      )
    end)
  end

  @doc "The catalog ids paired with their expected verdicts."
  @spec catalog() :: [{String.t(), :accept | :reject}]
  def catalog, do: Enum.map(@catalog, fn {id, expect, _e, _n, _b} -> {id, expect} end)

  @doc "Look up a catalog entry's full module source by id."
  @spec source(String.t()) :: String.t() | nil
  def source(id) do
    case entry(id) do
      {_id, _e, _err, _n, body} -> module(body)
      nil -> nil
    end
  end

  @doc "Look up a catalog entry's probe-fn BODY by id (transform input)."
  @spec body(String.t()) :: String.t() | nil
  def body(id) do
    case entry(id) do
      {_id, _e, _err, _n, body} -> body
      nil -> nil
    end
  end

  defp entry(id), do: Enum.find(@catalog, fn {i, _, _, _, _} -> i == id end)

  # -- Metamorphic challenges --------------------------------------------------

  @doc """
  Metamorphic challenges.

    * `drop_guard` (`:flip`) — on each proven-exhaustive ACCEPTING base, remove
      one guarded arm; the set is no longer exhaustive and the verdict must
      flip to reject. This is the lint-soundness pin (never over-prove).
    * `alpha_rename` (`:same`) — rename the guard-bound variable on EVERY
      base; the verdict must not change.
  """
  @spec metamorphic_challenges() :: [Challenge.t()]
  def metamorphic_challenges do
    Enum.flat_map(@catalog, fn {id, expect, _err, _note, body} ->
      base_src = module(body)

      invariance =
        [{"alpha_rename", alpha_rename(body)}]
        |> Enum.filter(fn {_t, b} -> is_binary(b) and b != body end)
        |> Enum.map(fn {t, vbody} -> challenge(id, t, :same, base_src, module(vbody)) end)

      flips =
        case expect do
          :accept ->
            [{"drop_guard", drop_guard(body)}]
            |> Enum.filter(fn {_t, b} -> is_binary(b) and b != body end)
            |> Enum.map(fn {t, vbody} -> challenge(id, t, :flip, base_src, module(vbody)) end)

          _ ->
            []
        end

      invariance ++ flips
    end)
  end

  defp challenge(id, transform, relation, base_src, variant_src) do
    Challenge.new(
      kind: :elab_program,
      assay: "elab/guard_lint",
      label: :none,
      payload: %{
        id: id,
        transform: transform,
        relation: relation,
        base_src: base_src,
        variant_src: variant_src
      },
      note: "#{id} #{relation} under #{transform}"
    )
  end

  # -- Metamorphic transforms (probe-fn BODY input only) ------------------------

  # Remove the middle/closing guarded arm of a proven-exhaustive set. Matches on
  # the arm's CONTENT only (no leading-whitespace/newline dependence) — mirrors
  # ElabDotForcing's corrupt_dot/promote_use convention, which matches an
  # unanchored substring rather than an exact indented line, so this stays
  # correct regardless of how the `@catalog` heredocs happen to be indented
  # (the shadowed and control cells — whose arms differ — return nil and
  # produce no flip; a future rewording that removes the fragment entirely
  # would surface as a missing flip in "drop_guard produces flips for exactly
  # the two proven-exhaustive cells", not a silent no-op).
  defp drop_guard(body) do
    cond do
      String.contains?(body, "x when x == b -> S(Z())") ->
        remove_line_containing(body, "x when x == b -> S(Z())")

      String.contains?(body, "x when x >= b -> S(Z())") ->
        remove_line_containing(body, "x when x >= b -> S(Z())")

      true ->
        nil
    end
  end

  # Delete the one line containing `fragment` (indentation and all), leaving
  # the surrounding lines correctly stitched together.
  defp remove_line_containing(body, fragment) do
    body
    |> String.split("\n")
    |> Enum.reject(&String.contains?(&1, fragment))
    |> Enum.join("\n")
  end

  # Rename the guard-bound variable `x` consistently (alpha-equivalence);
  # standalone `x` only, so `x0` collisions cannot arise from the catalog text.
  defp alpha_rename(body), do: String.replace(body, ~r/\bx\b/, "x0")
end
