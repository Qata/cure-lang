defmodule Antigen.Generators.KernelProbe do
  @moduledoc """
  Generator for the `kernel/probe` vertical (`Antigen.Assays.KernelProbe`): a fixed
  menu of def-level / inference-mode probes driving *defensive* clauses across the
  trusted kernel modules that no term-shaped generator reaches — `Kernel.check_def`'s
  unknown-global and body-less builtin-op arms, `validate_certificate`'s builtin-op
  certification, `check_family`'s universe-ceiling rejection, `normalize/3`'s opts
  arity, the Final-Core validator's warning-emit fold, `infer`'s `{:absurd}` /
  fields-only-ctor / ctor-arity rejections, `remap_index_error`'s non-family
  passthrough, plus the sibling-module cold clauses: `Quote.split_data_args`'s
  foreign-family fallback, `Inductive.occurs_deep?`'s through-constructor recursion,
  `Serialize.sym_atom`'s un-interned-symbol rejection, and `Certificate`'s
  under-application (`arg_relation(nil,_)`) and dangling-callee (`callees_env` /
  `reaches?` leaf) paths.

  Each challenge carries only a probe tag (`Coverage.terms_of` → `[]`, bypassing the
  term-well-formedness gate the way `check/verdict` and `serialize/decode` do); the
  assay reconstructs the input and asserts the kernel's documented verdict.
  """
  alias Antigen.{Gen, Challenge}

  @probes [
    :infer_absurd,
    :infer_fields_only_ctor,
    :check_ctor_arity,
    :check_def_unknown,
    :check_def_builtin_op,
    :validate_cert_builtin_op,
    :family_ceiling,
    :normalize_opts,
    :validator_warn_emit,
    :remap_index_passthrough,
    :quote_foreign_vdata,
    :positivity_through_ctor,
    :decode_unknown_symbol,
    :cert_under_application,
    :cert_dangling_callee,
    # Adversarial "backstop" probes — feed malformed input straight at a kernel
    # boundary and assert the defensive guard fires (rather than assuming it does).
    :eval_no_branch,
    :eval_nondata_scrutinee,
    :apply_nonfun,
    :conv_unknown_ctor_fallback,
    :validator_rejects_hole_body
  ]

  @doc """
  Shape-coverage cells for the manifest gate. One cell per probe; the gate confirms
  every probe is actually produced by sampling `gen/0`.
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells, do: for(p <- @probes, do: {"kernel/probe", p})

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.member_of(@probes), fn probe ->
      Gen.return(
        Challenge.new(
          kind: :kernel_probe,
          assay: "kernel/probe",
          label: :probe,
          payload: %{probe: probe},
          note: "kernel def-level probe: #{probe}",
          cover_tag: probe
        )
      )
    end)
  end
end
