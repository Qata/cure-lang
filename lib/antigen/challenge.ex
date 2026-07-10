defmodule Antigen.Challenge.UnknownAtomError do
  @moduledoc """
  Raised when a serialized record needs an atom that is absent from
  `Antigen.Challenge.__known_atoms__/0` — the portability whitelist every replay
  VM is guaranteed to have interned. Such a record would crash a fresh replay
  VM's decode with an opaque `ArgumentError: not an already existing atom`;
  surfacing it as this typed error lets the banker reject it loudly instead.
  """
  defexception [:name]

  @impl true
  def message(%{name: name}) do
    "atom #{inspect(name)} is absent from Antigen.Challenge.__known_atoms__/0 — " <>
      "add it there (see the :many precedent) or a fresh replay VM will fail to decode this record"
  end
end

defmodule Antigen.Challenge do
  @moduledoc "A generated challenge injected into the kernel (umbrella §3)."
  alias Cure.Core.Inductive
  @enforce_keys [:kind, :assay, :label, :payload]
  # `cover_tag` is run-time coverage metadata (a generator-chosen shape-cell id for
  # the coverage manifest gate), NOT part of a challenge's semantic identity: it is
  # deliberately absent from `encode_record`/`from_pieces`, so replayed corpus
  # records carry `cover_tag: nil`. See `Antigen.CoverManifest`.
  defstruct [:kind, :assay, :label, :payload, :seed, :note, :cover_tag]

  @type kind ::
          :stub
          | :def_group
          | :family
          | :forcing_pair
          | :indexed_case
          | :rewrite_eq
          | :stuck_elim
          | :typed_term
          | :mutant_term
          | :elab_program
          | :surface_expr
          | :unify_problem
          | :closure_env
          | :erasure_term
          | :smt_query
  @type label :: :terminating | :diverging | :positive | :negative | :none | :well_typed | :ill_typed
  @type t :: %__MODULE__{
          kind: kind(),
          assay: String.t(),
          label: label(),
          payload: map(),
          seed: integer() | nil,
          note: String.t() | nil,
          cover_tag: atom() | nil
        }

  # Force-intern the closed set of atoms that `decode_record`/`from_pieces/7`
  # reconstruct via `String.to_existing_atom/1` (Task 5 safety note): the challenge
  # `kind`s and `label`s (otherwise only present in `@type` specs, which don't
  # reliably intern at runtime) plus every generator-produced name. These literals
  # enter the atom table when this module loads — and it's always loaded before any
  # decode — so replay succeeds even in a process that never loaded a generator
  # (which would otherwise crash decoding a perfectly valid committed record). Keep
  # in sync with the generator modules' fixed, literal name sets.
  @known_atoms [
    # kinds
    :stub, :def_group, :family, :forcing_pair, :stuck_elim,
    # labels
    :terminating, :diverging, :positive, :negative, :none,
    # generator-produced names
    :f, :g, :h, :plus, :total_id, :even, :odd, :ack, :Dec, :Nat, :Z, :S, :Causal,
    :Natp, :Zp, :Sp, :pred, :Bad, :MkBad, :b, :present, :erased,
    # indexed-case vertical: kind, labels, family/ctor/def names
    :indexed_case, :well_typed, :ill_typed,
    # reify / data-split verticals (lean-shape-matching): indexed-case def names
    :data_split, :reify_distinct, :reify_eq,
    :Dcoupled, :Foo, :MkFoo, :Box, :mk, :d, :x,
    :probe, :branch_family, :coverage_gap, :refine, :motive_wf, :discharge, :inject,
    :motive_dom, :SNat, :snat0,
    :Tri, :A, :B, :C, :Ix, :wrap, :n, :p,
    :Wr, :MkWr, :IW, :iw, :w, :IxN, :wrapn, :delete, :i,
    # rewrite/eq vertical: kind, def-names, motive family name, and the
    # inductive identity family the migrated builders declare (Phase C —
    # `Equivalent`/`reflexive` with param `a`, indices `x`/`y`, witness `w`)
    :rewrite_eq, :eq_formation, :refl_typing, :rewrite_premise, :transport_type, :P,
    :Equivalent, :reflexive, :y,
    # universes vertical
    :u,
    # erasure quantities: the ω annotation `:many` on a ctor field (siblings
    # `:present`/`:erased` already interned). Family seeds carry it as text in the
    # scaffold and reconstruct it via `to_existing_atom`, so it must be interned or
    # a fresh-VM decode raises "not an already existing atom" (found banking
    # universes/family seeds — see many_quantity_decode_test).
    :many,
    # tier-B typed-term vertical: kind, family/ctor/def names, sig version
    # (:MkF is the shrink-test family F's ctor — a bloated-ctor-arg pieces-bridge probe)
    :typed_term, :v1, :Bd, :T, :F, :MkF, :Vec, :vnil, :vcons, :plus, :dbl, :x, :xs,
    # mutation corpus: kind, fault kinds, witness enum, extra type-former head
    # (:ill_typed already above; :Z/:S/:Nat/:Vec already interned above)
    :mutant_term,
    :head_swap, :ctor_arg, :index_mismatch, :app_domain,
    :out_of_scope_var, :proj_non_pair, :universe,
    :pair_component, :app_result, :type_param_mismatch,
    :head, :index, :level, :scope, :Sigma, :Bd,
    # fault-map KEY atoms (must be interned: the fault map rides through
    # binary_to_term [:safe] in the scaffold field — keys count, not just values)
    :kind, :witness, :expected_head, :injected_head,
    # deep-propagation: wrapper kinds (values) + the two new fault-field keys.
    # :pair doubles as a Core term tag but must be listed for the [:safe] decode.
    # (:ctor_vec is NOT a wrapper here — dropped for Nat→Nat composability.)
    :app_arg, :ctor_nat, :case_scrut, :case_branch, :pair, :depth, :wrap_path,
    # conversion-at-depth: carrier kinds + witness + field keys/values
    :conv_index, :conv_motive, :conv, :expected_index, :actual_index,
    :reduction, :required, :carrier,
    # elaborator completeness/metamorphic vertical: kind + label
    :elab_program, :well_typed,
    # totality-closure vertical (V5): kind + generator-produced env names
    # (:total_id, :i, :positive, :diverging already interned above)
    :closure_env, :loop, :callee, :Vessel, :Wrap,
    # erasure/relevance vertical (V4): kind + generator ctor/arg names
    # (:f, :g, :d, :b, :P already interned above)
    :erasure_term, :MkQ, :MkP, :a,
    # SMT-lint vertical (V6): kind (MetaAST predicate payloads use string keys/var
    # names, not atoms, so no extra generator atoms beyond the kind itself)
    :smt_query,
    # Tier-B reach expansion: List parametric family + param binder name
    :List, :Nil, :Cons, :A,
    # Structure-directed levers (coverage campaign): Bool builtin ctors (Primitive
    # generator) + the through-constructor-positive subject ctor (Positivity).
    # Node tags (:prim/:eq/:refl/:rewrite/:int_lit/:float_lit) are fixed Serialize
    # dispatch atoms, already interned by the code; only dynamic ctor/family names
    # need listing here.
    :Bool, :True, :False, :MkT,
    # parametric positivity generator: subject family + ctor/binder name pools
    :Pgen, :PC0, :PC1, :pq0, :pq1, :pq2,
    # S8: inert app-head used in app/lam-headed ctor field types
    :Fp,
    # family-level universe ceiling probe (Kernel.check_family range-check)
    :Over, :MkOver,
    # totality: pending-sibling marker in a def-group payload (premature-cert guard)
    :pending,
    # Sq: two-index diagonal family (dependent-matching unification tail) + binder :j
    :Sq, :mksq, :j,
    # Ty: Type0-indexed family (non-Nat rigid index unification) + its constructors
    :Ty, :tnat, :tbd, :tint, :tflt, :tpi, :tsig, :tvec,
    # IdxI: Int-indexed family (check_result_indices declaration-check driver)
    :IdxI, :mki, :mkb,
    # P/pc: parameterized indexed family (check_uniform_params / check_ctor_args)
    :P, :pc, :x,
    # MyEqK/mreflK: Type-param family, generalized field repeated across ≥2 indices
    # (check_result_indices parameter-seeding path — the dp01/dp02 datatype)
    :MyEqK, :mreflK,
    # Tg/Tgf: Int/Float-value-indexed families (rigid_index? int_lit/float_lit)
    :Tg, :tg0, :tg1, :Tgf, :tgf0, :tgf1,
    # Malformed negative vertical: kind + undeclared names the kernel must reject
    :malformed, :NoSuchFamily, :nosuchctor, :nosuchdef, :nosuchop,
    # Serialization roundtrip vertical: kind + label
    :serialize, :lossless,
    # Serialization decode-robustness vertical: kind + labels
    :decode_probe, :valid_sexp, :invalid_sexp,
    # Conversion-decision vertical: kind + labels
    :conv_pair, :convertible, :distinct,
    # Branch-unification vertical: kind + verdict labels + crossing-family names
    :branch_unify, :solved, :impossible, :trivial, :Cyc4, :mkcyc,
    # Dot-forcing vertical (#24): kind + verdict labels + the carried-index family
    # H/hmk (its Sq/mksq + Vec/vcons siblings are interned above). These ride the
    # scaffold `family`/`cname` fields through `known_atom!` on decode.
    :dot_forcing, :accept, :reject, :unforced, :H, :hmk,
    # Check-mode vertical: kind + the Bd ctor T used in a reject case
    :check_mode, :T,
    # Delta-reduction vertical: kind + label + the certified global names
    :delta_reduce, :reduces, :idnat, :kpair
  ]
  @doc false
  def __known_atoms__, do: @known_atoms

  # String view of the whitelist — decode gets strings and must check membership
  # WITHOUT minting an atom for a miss (a miss is the error path, not a new atom).
  @known_atom_strings MapSet.new(@known_atoms, &Atom.to_string/1)

  @doc """
  Reconstruct a whitelisted atom from its serialized string, or raise
  `Antigen.Challenge.UnknownAtomError`. Every decode-side `String.to_existing_atom`
  in `from_pieces/7` goes through here.

  Unlike `String.to_existing_atom/1` — which only asks "is this atom interned in
  THIS VM?" — this checks membership in the portability whitelist `@known_atoms`,
  the set every replay VM is guaranteed to have interned when this module loads.
  An atom interned here (e.g. a generator built a term literally carrying it) but
  absent from the whitelist decodes fine locally yet crashes a fresh replay VM;
  checking membership turns that latent poison into a loud, specific error at the
  point of reconstruction — and, via `Corpus.append/3`'s self-check, at banking
  time so `mix antigen` rejects it instead of poisoning the store.
  """
  @spec known_atom!(String.t()) :: atom()
  def known_atom!(str) when is_binary(str) do
    if MapSet.member?(@known_atom_strings, str) do
      # safe: membership guarantees the atom is already interned (it is a literal
      # in @known_atoms), so this never mints.
      String.to_existing_atom(str)
    else
      raise Antigen.Challenge.UnknownAtomError, name: str
    end
  end

  @spec new(keyword()) :: t()
  def new(fields),
    do: struct!(__MODULE__, Keyword.merge([label: :none, seed: nil, note: nil, cover_tag: nil], fields))

  @spec stub(Cure.Core.Term.t()) :: t()
  def stub(term), do: new(kind: :stub, assay: "stub", label: :none, payload: %{term: term})

  # --- to_pieces: challenge → {non-Term scaffold, [{piece_id, Term}]} ---------

  @doc """
  Split a challenge into its non-`Term` scaffold metadata and its list of named
  `Term` pieces — the bridge the corpus serializes over (Task 5).
  """
  @spec to_pieces(t()) :: {map(), [{String.t(), Cure.Core.Term.t()}]}
  def to_pieces(%__MODULE__{kind: :stub, payload: %{term: t}}), do: {%{}, [{"term", t}]}

  def to_pieces(%__MODULE__{kind: :def_group, payload: %{defs: defs, focus: focus}}),
    do: def_group_pieces(defs, focus)

  def to_pieces(%__MODULE__{kind: kind, payload: %{defs: defs, focus: focus, t: t, tprime: tp}})
      when kind in [:forcing_pair, :stuck_elim] do
    {scaffold, pieces} = def_group_pieces(defs, focus)
    {scaffold, pieces ++ [{"t", t}, {"tprime", tp}]}
  end

  def to_pieces(%__MODULE__{kind: :family, payload: %{family: fam, ctors: ctors}}) do
    param_pieces = fam.params |> Enum.with_index() |> Enum.map(fn {{_n, t}, i} -> {"fam_param:#{i}", t} end)
    index_pieces = fam.indices |> Enum.with_index() |> Enum.map(fn {{_n, t}, i} -> {"fam_index:#{i}", t} end)

    ctor_pieces =
      ctors
      |> Enum.with_index()
      |> Enum.flat_map(fn {ct, j} ->
        arg_pieces = ct.args |> Enum.with_index() |> Enum.map(fn {{_n, t}, k} -> {"ctor:#{j}:arg:#{k}", t} end)
        ridx_pieces = ct.result_indices |> Enum.with_index() |> Enum.map(fn {t, k} -> {"ctor:#{j}:ridx:#{k}", t} end)
        rparam_pieces = ctor_result_params(ct) |> Enum.with_index() |> Enum.map(fn {t, k} -> {"ctor:#{j}:rparam:#{k}", t} end)
        arg_pieces ++ ridx_pieces ++ rparam_pieces
      end)

    ctor_scaffold =
      Enum.map(ctors, fn ct ->
        %{
          "name" => Atom.to_string(ct.name),
          "arg_names" => Enum.map(ct.args, fn {n, _t} -> Atom.to_string(n) end),
          "ridx_count" => length(ct.result_indices),
          "rparam_count" => length(ctor_result_params(ct)),
          "quantities" => Enum.map(ct.quantities, &Atom.to_string/1)
        }
      end)

    scaffold = %{
      "fam_name" => Atom.to_string(fam.name),
      "fam_level" => fam.level,
      "fam_param_names" => Enum.map(fam.params, fn {n, _t} -> Atom.to_string(n) end),
      "fam_index_names" => Enum.map(fam.indices, fn {n, _t} -> Atom.to_string(n) end),
      "ctors" => ctor_scaffold
    }

    {scaffold, param_pieces ++ index_pieces ++ ctor_pieces}
  end

  def to_pieces(%__MODULE__{kind: k, payload: p}) when k in [:indexed_case, :rewrite_eq] do
    %{families: families, def_name: dn, def_type: dt, def_body: db} = p

    {fam_scaffolds, fam_pieces} =
      families
      |> Enum.with_index()
      |> Enum.reduce({[], []}, fn {{fam, ctors}, i}, {scaffs, pcs} ->
        {s, ps} = family_pieces(fam, ctors, "fam:#{i}")
        {scaffs ++ [s], pcs ++ ps}
      end)

    scaffold = %{"families" => fam_scaffolds, "def_name" => Atom.to_string(dn)}
    pieces = fam_pieces ++ [{"def_type", dt}, {"def_body", db}]
    {scaffold, pieces}
  end

  def to_pieces(%__MODULE__{kind: :typed_term, payload: p}) do
    %{sig: sig, ctx: ctx, type: type, term: term} = p
    ctx_pieces = ctx |> Enum.with_index() |> Enum.map(fn {t, i} -> {"ctx#{i}", t} end)
    scaffold = %{"sig" => Atom.to_string(sig), "ctx_len" => length(ctx)}
    {scaffold, ctx_pieces ++ [{"type", type}, {"term", term}]}
  end

  def to_pieces(%__MODULE__{kind: :serialize, payload: %{term: t}}), do: {%{}, [{"term", t}]}

  # decode probe: the raw input string rides in the scaffold (no Core-term pieces).
  def to_pieces(%__MODULE__{kind: :decode_probe, payload: %{input: s}}), do: {%{"input" => s}, []}

  # conv pair: two terms as pieces; context size + expected verdict in the scaffold.
  def to_pieces(%__MODULE__{kind: :conv_pair, payload: %{t1: t1, t2: t2, ctx: n, expect: e}}),
    do: {%{"ctx" => n, "expect" => e}, [{"t1", t1}, {"t2", t2}]}

  # branch-unify: family/ctor/ctx-size in the scaffold; scrutinee index terms as pieces.
  def to_pieces(%__MODULE__{kind: :branch_unify, payload: %{ctx_vars: n, dname: d, cname: c, indices: idx}}) do
    scaffold = %{"ctx_vars" => n, "dname" => Atom.to_string(d), "cname" => Atom.to_string(c)}
    {scaffold, idx |> Enum.with_index() |> Enum.map(fn {t, i} -> {"idx:#{i}", t} end)}
  end

  def to_pieces(%__MODULE__{
        kind: :dot_forcing,
        payload: %{ctx_vars: n, family: f, cname: c, indices: idx, name: name, written: w}
      }) do
    scaffold = %{
      "ctx_vars" => n,
      "family" => Atom.to_string(f),
      "cname" => Atom.to_string(c),
      "name" => name
    }

    pieces =
      (idx |> Enum.with_index() |> Enum.map(fn {t, i} -> {"idx:#{i}", t} end)) ++ [{"written", w}]

    {scaffold, pieces}
  end

  def to_pieces(%__MODULE__{kind: :check_mode, payload: %{ctx_vars: n, term: term, type: ty}}),
    do: {%{"ctx_vars" => n}, [{"term", term}, {"type", ty}]}

  def to_pieces(%__MODULE__{kind: :delta_reduce, payload: %{term: term, expected: exp}}),
    do: {%{}, [{"term", term}, {"expected", exp}]}

  def to_pieces(%__MODULE__{kind: :malformed, payload: p}) do
    %{sig: sig, ctx: ctx, term: term} = p
    ctx_pieces = ctx |> Enum.with_index() |> Enum.map(fn {t, i} -> {"ctx#{i}", t} end)
    scaffold = %{"sig" => Atom.to_string(sig), "ctx_len" => length(ctx)}
    {scaffold, ctx_pieces ++ [{"term", term}]}
  end

  def to_pieces(%__MODULE__{kind: :mutant_term, payload: p}) do
    %{sig: sig, ctx: ctx, type: type, term: term, fault: fault} = p
    ctx_pieces = ctx |> Enum.with_index() |> Enum.map(fn {t, i} -> {"ctx#{i}", t} end)
    scaffold = %{"sig" => Atom.to_string(sig), "ctx_len" => length(ctx), "fault" => fault}
    {scaffold, ctx_pieces ++ [{"type", type}, {"term", term}]}
  end

  # The elaborator vertical carries only surface-program STRINGS, no Core Terms —
  # the entire payload rides in the scaffold (string keys → string values). The
  # `payload` map's atom keys are stringified here and restored in from_pieces.
  def to_pieces(%__MODULE__{kind: :elab_program, payload: p}) do
    scaffold = Map.new(p, fn {k, v} -> {Atom.to_string(k), v} end)
    {scaffold, []}
  end

  # One family's scaffold + Term pieces, keyed under `prefix` (e.g. "fam:0").
  defp family_pieces(fam, ctors, prefix) do
    param_pieces = fam.params |> Enum.with_index() |> Enum.map(fn {{_n, t}, k} -> {"#{prefix}:param:#{k}", t} end)
    index_pieces = fam.indices |> Enum.with_index() |> Enum.map(fn {{_n, t}, k} -> {"#{prefix}:index:#{k}", t} end)

    ctor_pieces =
      ctors
      |> Enum.with_index()
      |> Enum.flat_map(fn {ct, j} ->
        args = ct.args |> Enum.with_index() |> Enum.map(fn {{_n, t}, k} -> {"#{prefix}:ctor:#{j}:arg:#{k}", t} end)
        ridx = ct.result_indices |> Enum.with_index() |> Enum.map(fn {t, k} -> {"#{prefix}:ctor:#{j}:ridx:#{k}", t} end)
        rparam = ctor_result_params(ct) |> Enum.with_index() |> Enum.map(fn {t, k} -> {"#{prefix}:ctor:#{j}:rparam:#{k}", t} end)
        args ++ ridx ++ rparam
      end)

    ctor_scaffold =
      Enum.map(ctors, fn ct ->
        %{
          "name" => Atom.to_string(ct.name),
          "arg_names" => Enum.map(ct.args, fn {n, _t} -> Atom.to_string(n) end),
          "ridx_count" => length(ct.result_indices),
          "rparam_count" => length(ctor_result_params(ct)),
          "quantities" => Enum.map(ct.quantities, &Atom.to_string/1)
        }
      end)

    scaffold = %{
      "fam_name" => Atom.to_string(fam.name),
      "fam_level" => fam.level,
      "fam_param_names" => Enum.map(fam.params, fn {n, _t} -> Atom.to_string(n) end),
      "fam_index_names" => Enum.map(fam.indices, fn {n, _t} -> Atom.to_string(n) end),
      "ctors" => ctor_scaffold
    }

    {scaffold, param_pieces ++ index_pieces ++ ctor_pieces}
  end

  # --- from_pieces: decoded record fields → challenge -------------------------

  @doc "Rebuild a challenge from a decoded record's fields, scaffold, and term pieces."
  @spec from_pieces(atom(), String.t(), atom(), integer() | nil, String.t() | nil, map(), [{String.t(), Cure.Core.Term.t()}]) :: t()
  def from_pieces(:stub, assay, label, seed, note, _scaffold, [{"term", t}]),
    do: new(kind: :stub, assay: assay, label: label, payload: %{term: t}, seed: seed, note: note)

  def from_pieces(:def_group, assay, label, seed, note, scaffold, pieces) do
    {defs, focus} = rebuild_defs(scaffold, Map.new(pieces))
    new(kind: :def_group, assay: assay, label: label, payload: %{defs: defs, focus: focus}, seed: seed, note: note)
  end

  def from_pieces(kind, assay, label, seed, note, scaffold, pieces)
      when kind in [:forcing_pair, :stuck_elim] do
    pmap = Map.new(pieces)
    {defs, focus} = rebuild_defs(scaffold, pmap)
    payload = %{defs: defs, focus: focus, t: Map.fetch!(pmap, "t"), tprime: Map.fetch!(pmap, "tprime")}
    new(kind: kind, assay: assay, label: label, payload: payload, seed: seed, note: note)
  end

  def from_pieces(:family, assay, label, seed, note, scaffold, pieces) do
    pmap = Map.new(pieces)
    params = rebuild_telescope(scaffold["fam_param_names"], "fam_param", pmap)
    indices = rebuild_telescope(scaffold["fam_index_names"], "fam_index", pmap)
    fam = Inductive.family(known_atom!(scaffold["fam_name"]), params, indices, scaffold["fam_level"])

    ctors =
      scaffold["ctors"]
      |> Enum.with_index()
      |> Enum.map(fn {cs, j} ->
        args =
          cs["arg_names"]
          |> Enum.with_index()
          |> Enum.map(fn {n, k} -> {known_atom!(n), Map.fetch!(pmap, "ctor:#{j}:arg:#{k}")} end)

        ridx = for k <- 0..(cs["ridx_count"] - 1)//1, do: Map.fetch!(pmap, "ctor:#{j}:ridx:#{k}")
        rparam = for k <- 0..((cs["rparam_count"] || 0) - 1)//1, do: Map.fetch!(pmap, "ctor:#{j}:rparam:#{k}")
        quantities = Enum.map(cs["quantities"], &known_atom!/1)
        Inductive.ctor(known_atom!(cs["name"]), args, ridx, quantities, rparam)
      end)

    new(kind: :family, assay: assay, label: label, payload: %{family: fam, ctors: ctors}, seed: seed, note: note)
  end

  def from_pieces(:indexed_case, assay, label, seed, note, scaffold, pieces) do
    pmap = Map.new(pieces)

    families =
      scaffold["families"]
      |> Enum.with_index()
      |> Enum.map(fn {fam_scaffold, i} -> rebuild_family(fam_scaffold, "fam:#{i}", pmap) end)

    payload = %{
      families: families,
      def_name: known_atom!(scaffold["def_name"]),
      def_type: Map.fetch!(pmap, "def_type"),
      def_body: Map.fetch!(pmap, "def_body")
    }

    new(kind: :indexed_case, assay: assay, label: label, payload: payload, seed: seed, note: note)
  end

  def from_pieces(:rewrite_eq, assay, label, seed, note, scaffold, pieces),
    do: from_pieces(:indexed_case, assay, label, seed, note, scaffold, pieces)
        |> Map.put(:kind, :rewrite_eq)

  def from_pieces(:typed_term, assay, label, seed, note, scaffold, pieces) do
    pmap = Map.new(pieces)
    len = scaffold["ctx_len"]
    ctx = for i <- (if len == 0, do: [], else: 0..(len - 1)), do: Map.fetch!(pmap, "ctx#{i}")

    payload = %{
      sig: known_atom!(scaffold["sig"]),
      ctx: ctx,
      type: Map.fetch!(pmap, "type"),
      term: Map.fetch!(pmap, "term")
    }

    new(kind: :typed_term, assay: assay, label: label, payload: payload, seed: seed, note: note)
  end

  def from_pieces(:serialize, assay, label, seed, note, _scaffold, [{"term", t}]),
    do: new(kind: :serialize, assay: assay, label: label, payload: %{term: t}, seed: seed, note: note)

  def from_pieces(:decode_probe, assay, label, seed, note, scaffold, _pieces),
    do: new(kind: :decode_probe, assay: assay, label: label, payload: %{input: scaffold["input"]}, seed: seed, note: note)

  def from_pieces(:conv_pair, assay, label, seed, note, scaffold, pieces) do
    pmap = Map.new(pieces)

    payload = %{
      t1: Map.fetch!(pmap, "t1"),
      t2: Map.fetch!(pmap, "t2"),
      ctx: scaffold["ctx"],
      expect: scaffold["expect"]
    }

    new(kind: :conv_pair, assay: assay, label: label, payload: payload, seed: seed, note: note)
  end

  def from_pieces(:branch_unify, assay, label, seed, note, scaffold, pieces) do
    pmap = Map.new(pieces)
    n = length(pieces)
    indices = if n == 0, do: [], else: for(i <- 0..(n - 1)//1, do: Map.fetch!(pmap, "idx:#{i}"))

    payload = %{
      ctx_vars: scaffold["ctx_vars"],
      dname: known_atom!(scaffold["dname"]),
      cname: known_atom!(scaffold["cname"]),
      indices: indices
    }

    new(kind: :branch_unify, assay: assay, label: label, payload: payload, seed: seed, note: note)
  end

  def from_pieces(:dot_forcing, assay, label, seed, note, scaffold, pieces) do
    pmap = Map.new(pieces)
    written = Map.fetch!(pmap, "written")
    idx_n = pieces |> Enum.count(fn {k, _} -> String.starts_with?(k, "idx:") end)
    indices = if idx_n == 0, do: [], else: for(i <- 0..(idx_n - 1)//1, do: Map.fetch!(pmap, "idx:#{i}"))

    payload = %{
      ctx_vars: scaffold["ctx_vars"],
      family: known_atom!(scaffold["family"]),
      cname: known_atom!(scaffold["cname"]),
      indices: indices,
      name: scaffold["name"],
      written: written
    }

    new(kind: :dot_forcing, assay: assay, label: label, payload: payload, seed: seed, note: note)
  end

  def from_pieces(:check_mode, assay, label, seed, note, scaffold, pieces) do
    pmap = Map.new(pieces)
    payload = %{ctx_vars: scaffold["ctx_vars"], term: Map.fetch!(pmap, "term"), type: Map.fetch!(pmap, "type")}
    new(kind: :check_mode, assay: assay, label: label, payload: payload, seed: seed, note: note)
  end

  def from_pieces(:delta_reduce, assay, label, seed, note, _scaffold, pieces) do
    pmap = Map.new(pieces)
    payload = %{term: Map.fetch!(pmap, "term"), expected: Map.fetch!(pmap, "expected")}
    new(kind: :delta_reduce, assay: assay, label: label, payload: payload, seed: seed, note: note)
  end

  def from_pieces(:malformed, assay, label, seed, note, scaffold, pieces) do
    pmap = Map.new(pieces)
    len = scaffold["ctx_len"]
    ctx = for i <- (if len == 0, do: [], else: 0..(len - 1)), do: Map.fetch!(pmap, "ctx#{i}")

    payload = %{sig: known_atom!(scaffold["sig"]), ctx: ctx, term: Map.fetch!(pmap, "term")}
    new(kind: :malformed, assay: assay, label: label, payload: payload, seed: seed, note: note)
  end

  def from_pieces(:mutant_term, assay, label, seed, note, scaffold, pieces) do
    pmap = Map.new(pieces)
    len = scaffold["ctx_len"]
    ctx = for i <- (if len == 0, do: [], else: 0..(len - 1)), do: Map.fetch!(pmap, "ctx#{i}")

    payload = %{
      sig: known_atom!(scaffold["sig"]),
      ctx: ctx,
      type: Map.fetch!(pmap, "type"),
      term: Map.fetch!(pmap, "term"),
      fault: scaffold["fault"]
    }

    new(kind: :mutant_term, assay: assay, label: label, payload: payload, seed: seed, note: note)
  end

  # Restore the string-keyed scaffold to an atom-keyed payload. The key set is
  # fixed and closed (the two elab assays' payloads), so keys map through an
  # explicit whitelist — never `String.to_atom` on decoded data.
  @elab_keys %{
    "id" => :id,
    "src" => :src,
    "transform" => :transform,
    "base_src" => :base_src,
    "variant_src" => :variant_src,
    "expect" => :expect,
    "relation" => :relation,
    "expect_error" => :expect_error,
    "functions" => :functions
  }
  def from_pieces(:elab_program, assay, label, seed, note, scaffold, _pieces) do
    payload =
      Map.new(scaffold, fn {k, v} ->
        {Map.get(@elab_keys, k) || raise(ArgumentError, "unknown elab payload key #{inspect(k)}"), v}
      end)

    new(kind: :elab_program, assay: assay, label: label, payload: payload, seed: seed, note: note)
  end

  # --- private helpers --------------------------------------------------------

  # Rebuild one {family, [ctor]} from its scaffold + the piece map, keyed under `prefix`.
  defp rebuild_family(fam_scaffold, prefix, pmap) do
    params =
      fam_scaffold["fam_param_names"]
      |> Enum.with_index()
      |> Enum.map(fn {n, k} -> {known_atom!(n), Map.fetch!(pmap, "#{prefix}:param:#{k}")} end)

    indices =
      fam_scaffold["fam_index_names"]
      |> Enum.with_index()
      |> Enum.map(fn {n, k} -> {known_atom!(n), Map.fetch!(pmap, "#{prefix}:index:#{k}")} end)

    fam = Inductive.family(known_atom!(fam_scaffold["fam_name"]), params, indices, fam_scaffold["fam_level"])

    ctors =
      fam_scaffold["ctors"]
      |> Enum.with_index()
      |> Enum.map(fn {cs, j} ->
        args =
          cs["arg_names"]
          |> Enum.with_index()
          |> Enum.map(fn {n, k} -> {known_atom!(n), Map.fetch!(pmap, "#{prefix}:ctor:#{j}:arg:#{k}")} end)

        ridx = for k <- 0..(cs["ridx_count"] - 1)//1, do: Map.fetch!(pmap, "#{prefix}:ctor:#{j}:ridx:#{k}")
        rparam = for k <- 0..((cs["rparam_count"] || 0) - 1)//1, do: Map.fetch!(pmap, "#{prefix}:ctor:#{j}:rparam:#{k}")
        quantities = Enum.map(cs["quantities"], &known_atom!/1)
        Inductive.ctor(known_atom!(cs["name"]), args, ridx, quantities, rparam)
      end)

    {fam, ctors}
  end

  # A constructor's result-parameter terms, tolerant of legacy records lacking
  # the field (defaults to []).
  defp ctor_result_params(ct), do: Map.get(ct, :result_params, [])

  defp def_group_pieces(defs, focus) do
    scaffold = %{
      "names" => Enum.map(defs, &Atom.to_string(&1.name)),
      "focus" => Enum.map(focus, &Atom.to_string/1)
    }

    pieces =
      Enum.flat_map(defs, fn d ->
        n = Atom.to_string(d.name)
        [{"type:" <> n, d.type}, {"body:" <> n, d.body}]
      end)

    {scaffold, pieces}
  end

  defp rebuild_defs(scaffold, pmap) do
    defs =
      Enum.map(scaffold["names"], fn n ->
        %{
          name: known_atom!(n),
          type: Map.fetch!(pmap, "type:" <> n),
          body: Map.fetch!(pmap, "body:" <> n)
        }
      end)

    {defs, Enum.map(scaffold["focus"], &known_atom!/1)}
  end

  defp rebuild_telescope(names, prefix, pmap) do
    names
    |> Enum.with_index()
    |> Enum.map(fn {n, i} -> {known_atom!(n), Map.fetch!(pmap, "#{prefix}:#{i}")} end)
  end
end
