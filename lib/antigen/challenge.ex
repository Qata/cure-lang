defmodule Antigen.Challenge do
  @moduledoc "A generated challenge injected into the kernel (umbrella §3)."
  alias Cure.Core.Inductive
  @enforce_keys [:kind, :assay, :label, :payload]
  defstruct [:kind, :assay, :label, :payload, :seed, :note]

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
          note: String.t() | nil
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
    # rewrite/eq vertical: kind, def-names, motive family name
    :rewrite_eq, :eq_formation, :refl_typing, :rewrite_premise, :transport_type, :P,
    # universes vertical
    :u,
    # tier-B typed-term vertical: kind, family/ctor/def names, sig version
    :typed_term, :v1, :Bd, :T, :F, :Vec, :vnil, :vcons, :plus, :dbl, :x, :xs,
    # mutation corpus: kind, fault kinds, witness enum, extra type-former head
    # (:ill_typed already above; :Z/:S/:Nat/:Vec already interned above)
    :mutant_term,
    :head_swap, :ctor_arg, :index_mismatch, :app_domain,
    :out_of_scope_var, :proj_non_pair, :universe,
    :head, :index, :level, :scope, :Sigma,
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
    :List, :Nil, :Cons, :A
  ]
  @doc false
  def __known_atoms__, do: @known_atoms

  @spec new(keyword()) :: t()
  def new(fields), do: struct!(__MODULE__, Keyword.merge([label: :none, seed: nil, note: nil], fields))

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
    fam = Inductive.family(String.to_existing_atom(scaffold["fam_name"]), params, indices, scaffold["fam_level"])

    ctors =
      scaffold["ctors"]
      |> Enum.with_index()
      |> Enum.map(fn {cs, j} ->
        args =
          cs["arg_names"]
          |> Enum.with_index()
          |> Enum.map(fn {n, k} -> {String.to_existing_atom(n), Map.fetch!(pmap, "ctor:#{j}:arg:#{k}")} end)

        ridx = for k <- 0..(cs["ridx_count"] - 1)//1, do: Map.fetch!(pmap, "ctor:#{j}:ridx:#{k}")
        rparam = for k <- 0..((cs["rparam_count"] || 0) - 1)//1, do: Map.fetch!(pmap, "ctor:#{j}:rparam:#{k}")
        quantities = Enum.map(cs["quantities"], &String.to_existing_atom/1)
        Inductive.ctor(String.to_existing_atom(cs["name"]), args, ridx, quantities, rparam)
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
      def_name: String.to_existing_atom(scaffold["def_name"]),
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
      sig: String.to_existing_atom(scaffold["sig"]),
      ctx: ctx,
      type: Map.fetch!(pmap, "type"),
      term: Map.fetch!(pmap, "term")
    }

    new(kind: :typed_term, assay: assay, label: label, payload: payload, seed: seed, note: note)
  end

  def from_pieces(:mutant_term, assay, label, seed, note, scaffold, pieces) do
    pmap = Map.new(pieces)
    len = scaffold["ctx_len"]
    ctx = for i <- (if len == 0, do: [], else: 0..(len - 1)), do: Map.fetch!(pmap, "ctx#{i}")

    payload = %{
      sig: String.to_existing_atom(scaffold["sig"]),
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
    "relation" => :relation
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
      |> Enum.map(fn {n, k} -> {String.to_existing_atom(n), Map.fetch!(pmap, "#{prefix}:param:#{k}")} end)

    indices =
      fam_scaffold["fam_index_names"]
      |> Enum.with_index()
      |> Enum.map(fn {n, k} -> {String.to_existing_atom(n), Map.fetch!(pmap, "#{prefix}:index:#{k}")} end)

    fam = Inductive.family(String.to_existing_atom(fam_scaffold["fam_name"]), params, indices, fam_scaffold["fam_level"])

    ctors =
      fam_scaffold["ctors"]
      |> Enum.with_index()
      |> Enum.map(fn {cs, j} ->
        args =
          cs["arg_names"]
          |> Enum.with_index()
          |> Enum.map(fn {n, k} -> {String.to_existing_atom(n), Map.fetch!(pmap, "#{prefix}:ctor:#{j}:arg:#{k}")} end)

        ridx = for k <- 0..(cs["ridx_count"] - 1)//1, do: Map.fetch!(pmap, "#{prefix}:ctor:#{j}:ridx:#{k}")
        rparam = for k <- 0..((cs["rparam_count"] || 0) - 1)//1, do: Map.fetch!(pmap, "#{prefix}:ctor:#{j}:rparam:#{k}")
        quantities = Enum.map(cs["quantities"], &String.to_existing_atom/1)
        Inductive.ctor(String.to_existing_atom(cs["name"]), args, ridx, quantities, rparam)
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
          name: String.to_existing_atom(n),
          type: Map.fetch!(pmap, "type:" <> n),
          body: Map.fetch!(pmap, "body:" <> n)
        }
      end)

    {defs, Enum.map(scaffold["focus"], &String.to_existing_atom/1)}
  end

  defp rebuild_telescope(names, prefix, pmap) do
    names
    |> Enum.with_index()
    |> Enum.map(fn {n, i} -> {String.to_existing_atom(n), Map.fetch!(pmap, "#{prefix}:#{i}")} end)
  end
end
