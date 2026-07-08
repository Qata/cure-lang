defmodule Antigen.Generators.ElabDotForcing do
  @moduledoc """
  Source-level dot-forcing vertical (spec 2026-07-08-antigen-elab-dot-forcing):
  `:elab_program` challenges entering at `Cure.Elab.Program.elaborate/1`, so the
  named-implicit check's CALL-SITE WIRING is probed — the class the value-level
  `forcing/dot` oracle is structurally blind to (it calls the check directly and
  can never observe a dispatch path that skips it, as C-a's carried-eq path did
  pre-#12).

  Six two-sided catalog cells (labels correct-by-construction — the generator
  writes both the forced solution and the written dot value):

    * forced axis, {plain, carried} × {right, wrong} — `wrong` cells pin error
      head `:forced_pattern_mismatch`;
    * unforced C-c axis, {bind_erased, bind_relevant} — `bind_relevant` pins
      `:erased_used_relevantly` (the quantity gate, not a named-implicit error).

  Sources are verbatim the #12-landed fixtures (`named_implicit_tail_test.exs`);
  carried cells are the only landed programs reaching
  `elaborate_carried_eq_branch`. Metamorphic layer: `corrupt_dot` /
  `promote_use` are `:flip` relations (the C-a-class causal pin — base held
  fixed, only the checked property mutated); `alpha_rename` /
  `extra_unused_param` are `:same` perturbations. Transforms operate on the
  probe-fn BODY only, never `preamble <> body` (first-match regex safety —
  spec §2.2 structural note).
  """

  alias Antigen.Challenge

  # Carried + forced mixed shape (#12 Task 2): H's first index is ctor-pinned
  # (forced m := j), the second is a stuck function index carried via the
  # sibling `w : G(app(p, q))` (detect_carried_index).
  @carried_preamble """
    type Nat = Z | S(Nat)
    type SList = SNil | SCons(Nat, SList)
    fn app(xs: SList, ys: SList) -> SList = match xs
      SNil() -> ys
      SCons(h, t) -> SCons(h, app(t, ys))
    type H indices (n: Nat, xs: SList)
      hmk : H(S(m), app(as, bs))
    type G indices (xs: SList)
      gwrap : G(cs)
  """

  # Vec (plain forced cells) + Pack (unforced C-c cells) — the landed
  # @exist_preamble of #12 Task 4.
  @exist_preamble """
    type Nat = Z | S(Nat)
    type Vec(a: Type) indices (n: Nat)
      vnil : Vec(a, Z)
      vcons : a -> Vec(a, n) -> Vec(a, S(n))
    type Pack(a: Type) indices ()
      pk : Vec(a, m) -> Pack(a)
  """

  defp preamble(:carried), do: @carried_preamble
  defp preamble(:exist), do: @exist_preamble

  @doc "Wrap a probe-`fn` body into a self-contained, elaborable module."
  @spec module(:carried | :exist, String.t()) :: String.t()
  def module(pre, body), do: "mod P\n" <> preamble(pre) <> body <> "end\n"

  # -- Two-sided catalog: {id, expect, expect_error | nil, preamble, note, body}
  @catalog [
    {"forced/carried/right", :accept, nil, :carried,
     "right dot on the carried-eq path (over-rejection guard)",
     """
       fn g({j: Nat}, {p: SList}, {q: SList}, v: H(S(j), app(p, q)), w: G(app(p, q))) -> Nat = match v
         hmk({m = .j}) -> Z()
     """},
    {"forced/carried/wrong", :reject, :forced_pattern_mismatch, :carried,
     "wrong dot on the carried-eq path (the C-a cell — pre-#12 this ACCEPTED)",
     """
       fn f({j: Nat}, {p: SList}, {q: SList}, v: H(S(j), app(p, q)), w: G(app(p, q))) -> Nat = match v
         hmk({m = .(S(j))}) -> Z()
     """},
    {"forced/plain/right", :accept, nil, :exist,
     "right dot on the plain dispatch path (landed C-b shape)",
     """
       fn f({a: Type}, {k: Nat}, v: Vec(a, S(k))) -> Vec(a, S(k)) = match v
         vcons({n = .k}, h, t) -> v
     """},
    {"forced/plain/wrong", :reject, :forced_pattern_mismatch, :exist,
     "wrong dot on the plain dispatch path",
     """
       fn f({a: Type}, {k: Nat}, v: Vec(a, S(k))) -> Vec(a, S(k)) = match v
         vcons({n = .(S(k))}, h, t) -> v
     """},
    {"unforced/bind_erased", :accept, nil, :exist,
     "unforced bare-variable named implicit bound at quantity 0, used only erasedly",
     """
       fn f({a: Type}, p: Pack(a)) -> Nat = match p
         pk({m = mm}, v) -> Z()
     """},
    {"unforced/bind_relevant", :reject, :erased_used_relevantly, :exist,
     "quantity-0 binding used relevantly rejects via Relevance (C-c gate)",
     """
       fn g({a: Type}, p: Pack(a)) -> Nat = match p
         pk({m = mm}, v) -> mm
     """}
  ]

  @doc "All two-sided catalog challenges as `%Challenge{}` structs (deterministic)."
  @spec dot_forcing_challenges() :: [Challenge.t()]
  def dot_forcing_challenges do
    Enum.map(@catalog, fn {id, expect, err, pre, note, body} ->
      payload = %{id: id, src: module(pre, body), expect: expect}
      payload = if err, do: Map.put(payload, :expect_error, err), else: payload

      Challenge.new(
        kind: :elab_program,
        assay: "elab/dot_forcing",
        label: expect,
        payload: payload,
        note: note
      )
    end)
  end

  @doc "The catalog ids paired with their expected verdicts."
  @spec catalog() :: [{String.t(), :accept | :reject}]
  def catalog, do: Enum.map(@catalog, fn {id, expect, _e, _p, _n, _b} -> {id, expect} end)

  @doc "Look up a catalog entry's full module source by id."
  @spec source(String.t()) :: String.t() | nil
  def source(id) do
    case entry(id) do
      {_id, _e, _err, pre, _n, body} -> module(pre, body)
      nil -> nil
    end
  end

  @doc "Look up a catalog entry's probe-fn BODY by id (transform input)."
  @spec body(String.t()) :: String.t() | nil
  def body(id) do
    case entry(id) do
      {_id, _e, _err, _pre, _n, body} -> body
      nil -> nil
    end
  end

  defp entry(id), do: Enum.find(@catalog, fn {i, _, _, _, _, _} -> i == id end)
end
