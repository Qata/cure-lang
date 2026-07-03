defmodule Antigen.Generators.Totality do
  @moduledoc """
  Known-label totality generator (spec §5.1). Emits `:def_group` challenges whose
  ground-truth label (`:terminating` | `:diverging`) is correct **by construction**
  — the generator IS the oracle (umbrella §6), so the deterministic constructors
  below are cross-checked against the real certifier in the Task-12 self-tests.

  Def/family names are a fixed, literal, closed set (`:f`, `:g`, `:h`) so the atoms
  exist the instant this module is loaded — required for `:safe` corpus replay in a
  process that never ran the generator (see `Antigen.Corpus`, Task 5 safety note).
  """
  alias Antigen.{Gen, Challenge}
  alias Cure.Core.Env

  @dec {:data, :Dec, [], []}
  @nat {:data, :Nat, [], []}

  @doc "A Gen program over the known-label def groups."
  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.frequency([
      {1, Gen.return(diverging_mutual_pair())},
      {1, Gen.return(structural_terminating())}
    ])
  end

  @doc """
  The banked 2-cycle: `f = λx. g x`, `g = λx. f x` over `Dec → Dec`. Neither body
  references its own name, so single-body analysis alone cannot witness the cycle;
  `Cure.Core.Certificate` detects it through the signature (mutual-cycle detection,
  the fix for the once-live hole — see `d13d718`) and certifies neither. The pair
  genuinely diverges under δ. Label `:diverging`. Kept forever as the permanent
  regression guard for that fix.
  """
  @spec diverging_mutual_pair() :: Challenge.t()
  def diverging_mutual_pair do
    ty = {:pi, @dec, @dec}
    bf = {:lam, @dec, {:app, {:global, :g}, {:var, 0}}}
    bg = {:lam, @dec, {:app, {:global, :f}, {:var, 0}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{
        defs: [%{name: :f, type: ty, body: bf}, %{name: :g, type: ty, body: bg}],
        focus: [:f, :g]
      },
      note: "mutual cycle f->g->f (hole fixed d13d718; permanent regression guard)"
    )
  end

  @doc """
  A genuinely structural-recursive total def: `h = λn. case n of {Z -> Z; S y -> h y}`
  over `Nat → Nat`. The self-call is on the `S`-branch-bound subterm, so the
  certifier accepts it correctly. Label `:terminating` — guards the eventual
  mutual-recursion fix against over-correction (umbrella §6).
  """
  @spec structural_terminating() :: Challenge.t()
  def structural_terminating do
    motive = {:lam, @nat, @nat}

    body =
      {:lam, @nat,
       {:case, {:var, 0}, motive,
        [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:app, {:global, :h}, {:var, 0}}}]}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{defs: [%{name: :h, type: {:pi, @nat, @nat}, body: body}], focus: [:h]},
      note: "structural recursion h(S y) = h y"
    )
  end

  @doc """
  A non-total def whose non-decreasing self-call is hidden inside a `bool_elim`
  branch: `f = λn:Int. bool_elim (n == 0) (λ_.Int) 0 (f n)`. Diverges for every
  `n ≠ 0` (`f n → f n → …`). The self-call passes `n` unchanged, so it is not
  structurally decreasing. Label `:diverging`.

  This is the permanent regression guard for the `bool_elim` totality hole: the
  structural certifier's `calls?`/`guarded_node?` traversals *must* descend into
  both `bool_elim` branches. Before those clauses were added, `calls?` returned
  the catch-all `false` — the self-call was invisible, `terminating?` reported a
  spurious `true`, and this loop would have been certified total (a soundness
  infection). Kept forever.
  """
  @spec diverging_bool_elim_branch() :: Challenge.t()
  def diverging_bool_elim_branch do
    ty = {:pi, {:int_type}, {:int_type}}

    body =
      {:lam, {:int_type},
       {:bool_elim, {:prim, :eq, [{:var, 0}, {:int_lit, 0}]}, {:lam, {:bool_type}, {:int_type}},
        {:int_lit, 0}, {:app, {:global, :f}, {:var, 0}}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{defs: [%{name: :f, type: ty, body: body}], focus: [:f]},
      note: "self-call hidden in a bool_elim branch (bool_elim totality-hole guard)"
    )
  end

  @doc """
  A genuinely total structural recursion whose decreasing self-call sits *inside*
  a `bool_elim` branch: `h = λn:Nat. case n of {Z -> Z; S y -> bool_elim true
  (λ_.Nat) (h y) (h y)}`. Each self-call passes `y`, the `S`-branch-bound subterm,
  so it is structurally smaller. Label `:terminating`.

  Companion to `diverging_bool_elim_branch/0`: it guards against the certifier
  *over*-correcting — the new `guarded_node?` clause for `bool_elim` must *recurse*
  into the branches carrying the current `root`/`smaller`, not blanket-reject (or
  blanket-accept) a term that contains one.
  """
  @spec terminating_bool_elim_branch() :: Challenge.t()
  def terminating_bool_elim_branch do
    inner =
      {:bool_elim, {:bool_lit, true}, {:lam, {:bool_type}, @nat},
       {:app, {:global, :h}, {:var, 0}}, {:app, {:global, :h}, {:var, 0}}}

    body =
      {:lam, @nat,
       {:case, {:var, 0}, {:lam, @nat, @nat},
        [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, inner}]}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{defs: [%{name: :h, type: {:pi, @nat, @nat}, body: body}], focus: [:h]},
      note: "structural recursion with the decreasing self-call inside a bool_elim branch"
    )
  end

  # -- W1: adversarial diverging set (pre-port banking spec §4 W1) ------------
  # Each is diverging BY CONSTRUCTION (argument in @doc). All are rejected by
  # today's conservative certifier (mutual cycles rejected wholesale; the
  # self-call variants fail the fixed-position structural guard) — and must
  # STAY rejected forever, including after the P1 size-change port.

  @doc """
  Diverging 3-cycle `f → g → h → f` over `Dec → Dec`. No body references its own
  name; only signature-level cycle detection sees it (generalizes the banked
  2-cycle). Diverges on every input: `f x → g x → h x → f x → …`. Label `:diverging`.
  """
  @spec diverging_three_cycle() :: Challenge.t()
  def diverging_three_cycle do
    ty = {:pi, @dec, @dec}
    bf = {:lam, @dec, {:app, {:global, :g}, {:var, 0}}}
    bg = {:lam, @dec, {:app, {:global, :h}, {:var, 0}}}
    bh = {:lam, @dec, {:app, {:global, :f}, {:var, 0}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{
        defs: [
          %{name: :f, type: ty, body: bf},
          %{name: :g, type: ty, body: bg},
          %{name: :h, type: ty, body: bh}
        ],
        focus: [:f, :g, :h]
      },
      note: "W1 3-cycle f->g->h->f; every body self-call-free"
    )
  end

  @doc """
  Diverging cycle whose every direct callee looks innocent: `f = λx. total_id (g x)`,
  `g = λx. f x`, with `total_id = λx. x` genuinely total. The cycle f→g→f exists but
  is interleaved with a plain subroutine call. `total_id` is deliberately NOT in
  `focus` — it must keep certifying (asserted separately). Diverges on every input.
  Label `:diverging`.
  """
  @spec diverging_mediated_cycle() :: Challenge.t()
  def diverging_mediated_cycle do
    ty = {:pi, @dec, @dec}
    b_id = {:lam, @dec, {:var, 0}}
    bf = {:lam, @dec, {:app, {:global, :total_id}, {:app, {:global, :g}, {:var, 0}}}}
    bg = {:lam, @dec, {:app, {:global, :f}, {:var, 0}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{
        defs: [
          %{name: :total_id, type: ty, body: b_id},
          %{name: :f, type: ty, body: bf},
          %{name: :g, type: ty, body: bg}
        ],
        focus: [:f, :g]
      },
      note: "W1 cycle f->g->f mediated by a total helper (total_id excluded from focus)"
    )
  end

  @doc """
  Argument-permuting, size-preserving mutual pair over `Dec → Dec → Dec`:
  `f x y = g y x`, `g x y = f x y`. Every argument-to-argument flow is `≤`, none
  is `<` — the classic size-change discriminator: a naive "some argument shrinks
  somewhere" analysis wrongly certifies it, LJB composition does not. Diverges on
  every input pair. Label `:diverging`.
  """
  @spec diverging_permuting_pair() :: Challenge.t()
  def diverging_permuting_pair do
    ty = {:pi, @dec, {:pi, @dec, @dec}}
    # inner frame: y = var 0, x = var 1
    bf = {:lam, @dec, {:lam, @dec, {:app, {:app, {:global, :g}, {:var, 0}}, {:var, 1}}}}
    bg = {:lam, @dec, {:lam, @dec, {:app, {:app, {:global, :f}, {:var, 1}}, {:var, 0}}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{
        defs: [%{name: :f, type: ty, body: bf}, %{name: :g, type: ty, body: bg}],
        focus: [:f, :g]
      },
      note: "W1 permuting pair f x y = g y x; g x y = f x y — all flows ≤, none <"
    )
  end

  @doc """
  Constructor-regrowing self-call: `h = λn. case n of {Z -> Z; S y -> h (S y)}`
  over `Nat → Nat`. The self-call re-wraps the just-unpacked field, so descent is
  claimed by shape and refuted by size: `h (S m) → h (S m) → …` diverges on every
  `S`-input. Label `:diverging`.
  """
  @spec diverging_regrowing_self() :: Challenge.t()
  def diverging_regrowing_self do
    motive = {:lam, @nat, @nat}

    body =
      {:lam, @nat,
       {:case, {:var, 0}, motive,
        [
          {:Z, 0, {:ctor, :Z, []}},
          {:S, 1, {:app, {:global, :h}, {:ctor, :S, [{:var, 0}]}}}
        ]}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{defs: [%{name: :h, type: {:pi, @nat, @nat}, body: body}], focus: [:h]},
      note: "W1 regrowing self-call h (S y) — diverges on every S input"
    )
  end

  @doc """
  One-leg-decreasing mutual pair: `f = λn. case n of {Z -> Z; S y -> g y}` and
  `g = λn. f (S n)` over `Nat → Nat`. The f→g call strictly decreases; the g→f
  call regrows; the COMPOSED cycle is non-decreasing: `f (S m) → g m → f (S m) → …`.
  LJB's motivating case — certification must consider cycle composition, not
  individual calls. Label `:diverging`.
  """
  @spec diverging_one_leg_pair() :: Challenge.t()
  def diverging_one_leg_pair do
    motive = {:lam, @nat, @nat}

    bf =
      {:lam, @nat,
       {:case, {:var, 0}, motive,
        [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:app, {:global, :g}, {:var, 0}}}]}}

    bg = {:lam, @nat, {:app, {:global, :f}, {:ctor, :S, [{:var, 0}]}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{
        defs: [
          %{name: :f, type: {:pi, @nat, @nat}, body: bf},
          %{name: :g, type: {:pi, @nat, @nat}, body: bg}
        ],
        focus: [:f, :g]
      },
      note: "W1 one-leg pair: f decreases, g regrows; composed cycle non-decreasing"
    )
  end

  # -- W2: reach pins (pre-port banking spec §4 W2) ----------------------------
  # Ground-truth :terminating (argument in each @doc), conservatively rejected by
  # today's certifier (mutual groups rejected wholesale; multi-argument descent
  # fails the fixed-position guard). Banked in test/antigen/reach.sexp, NOT
  # corpus.sexp; P1 migrates them. Labels are truth, not checker behavior (D3).

  @doc """
  Well-founded structural mutual pair: `even = λn. case n of {Z -> Z; S y -> odd y}`,
  `odd = λn. case n of {Z -> S Z; S y -> even y}` over `Nat → Nat` (Nat-valued to
  stay in one family). Every cross-call passes the strict predecessor, so the
  composed cycle strictly decreases: total. Label `:terminating` — rejected today
  only because the certifier rejects all mutual cycles.
  """
  @spec wellfounded_even_odd() :: Challenge.t()
  def wellfounded_even_odd do
    motive = {:lam, @nat, @nat}

    be =
      {:lam, @nat,
       {:case, {:var, 0}, motive,
        [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:app, {:global, :odd}, {:var, 0}}}]}}

    bo =
      {:lam, @nat,
       {:case, {:var, 0}, motive,
        [
          {:Z, 0, {:ctor, :S, [{:ctor, :Z, []}]}},
          {:S, 1, {:app, {:global, :even}, {:var, 0}}}
        ]}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{
        defs: [
          %{name: :even, type: {:pi, @nat, @nat}, body: be},
          %{name: :odd, type: {:pi, @nat, @nat}, body: bo}
        ],
        focus: [:even, :odd]
      },
      note: "W2 reach pin: well-founded mutual even/odd (P1 target)"
    )
  end

  @doc """
  Ackermann over `Nat → Nat → Nat`:
  `ack Z n = S n; ack (S m') Z = ack m' (S Z); ack (S m') (S n') = ack m' (ack (S m') n')`.
  Total by the lexicographic measure (m, n): every call either decreases m, or
  keeps m and decreases n. Rejected today: no SINGLE fixed argument position
  decreases at every self-call (the inner call's first argument is `S m'`, a
  constructor, not a bound variable). Label `:terminating`.
  """
  @spec wellfounded_ackermann() :: Challenge.t()
  def wellfounded_ackermann do
    motive = {:lam, @nat, @nat}

    # frame under λm. λn.: m = var 1, n = var 0
    body =
      {:lam, @nat,
       {:lam, @nat,
        {:case, {:var, 1}, motive,
         [
           # Z: S n
           {:Z, 0, {:ctor, :S, [{:var, 0}]}},
           # S m' (binds m' at 0; n shifts to 1, m to 2)
           {:S, 1,
            {:case, {:var, 1}, motive,
             [
               # n = Z: ack m' (S Z)
               {:Z, 0,
                {:app, {:app, {:global, :ack}, {:var, 0}}, {:ctor, :S, [{:ctor, :Z, []}]}}},
               # n = S n' (binds n' at 0; m' shifts to 1): ack m' (ack (S m') n')
               {:S, 1,
                {:app, {:app, {:global, :ack}, {:var, 1}},
                 {:app, {:app, {:global, :ack}, {:ctor, :S, [{:var, 1}]}}, {:var, 0}}}}
             ]}}
         ]}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{
        defs: [%{name: :ack, type: {:pi, @nat, {:pi, @nat, @nat}}, body: body}],
        focus: [:ack]
      },
      note: "W2 reach pin: Ackermann, lexicographic (m, n) descent (P1 target)"
    )
  end

  @doc """
  Permuted well-founded pair over `Nat`: `f = λn. λm. case n of {Z -> m; S y -> g m y}`
  and `g = λa. λb. f b a`. Descent is visible only by tracking arguments across the
  swap: `f (S y) m → g m y → f y m` — f's first argument strictly decreases every
  round trip. Total; rejected today as a mutual cycle. The accept-side twin of W1's
  `diverging_permuting_pair`. Label `:terminating`.
  """
  @spec wellfounded_permuted_pair() :: Challenge.t()
  def wellfounded_permuted_pair do
    motive = {:lam, @nat, @nat}

    # f frame: n = var 1, m = var 0; S-branch binds y at 0 (m -> 1, n -> 2)
    bf =
      {:lam, @nat,
       {:lam, @nat,
        {:case, {:var, 1}, motive,
         [
           {:Z, 0, {:var, 0}},
           {:S, 1, {:app, {:app, {:global, :g}, {:var, 1}}, {:var, 0}}}
         ]}}}

    # g a b = f b a; frame: a = var 1, b = var 0
    bg = {:lam, @nat, {:lam, @nat, {:app, {:app, {:global, :f}, {:var, 0}}, {:var, 1}}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{
        defs: [
          %{name: :f, type: {:pi, @nat, {:pi, @nat, @nat}}, body: bf},
          %{name: :g, type: {:pi, @nat, {:pi, @nat, @nat}}, body: bg}
        ],
        focus: [:f, :g]
      },
      note: "W2 reach pin: descent visible only across the argument swap (P1 target)"
    )
  end

  @doc "Rebuild the def-group's `Env` by folding `Env.add_def/4` over the payload."
  @spec env_of(Challenge.t()) :: Env.t()
  def env_of(%Challenge{payload: %{defs: defs}}) do
    Enum.reduce(defs, Env.empty(), fn d, env -> Env.add_def(env, d.name, d.type, d.body) end)
  end
end
