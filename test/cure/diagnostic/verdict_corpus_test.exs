defmodule Cure.Diagnostic.VerdictCorpusTest do
  @moduledoc """
  Frozen cross-boundary verdicts.

  This corpus deliberately records only the public-path verdict and its broad
  owner.  It is a regression gate for acceptance drift, not a snapshot of
  diagnostic wording, spans, or implementation error terms.
  """

  use ExUnit.Case, async: false

  alias Antigen.{Challenge, Generators.ElabComplete}
  alias Antigen.Assays.Elab
  alias Cure.Compiler
  alias Cure.Core.{Builtins, Context, Env, Kernel}
  alias Cure.Elab.Program

  @corpus [
    %{id: :parser_accept, domain: :parser, status: :accept},
    %{id: :parser_reject, domain: :parser, status: :reject},
    %{id: :elaboration_accept, domain: :elaboration, status: :accept},
    %{id: :elaboration_reject, domain: :elaboration, status: :reject},
    %{id: :kernel_accept, domain: :kernel, status: :accept},
    %{id: :kernel_reject, domain: :kernel, status: :reject},
    %{id: :macro_accept, domain: :macro, status: :accept},
    %{id: :macro_reject, domain: :macro, status: :reject},
    %{id: :stdlib_accept, domain: :stdlib, status: :accept},
    %{id: :stdlib_reject, domain: :stdlib, status: :reject},
    %{id: :antigen_accept, domain: :antigen, status: :accept},
    %{id: :antigen_reject, domain: :antigen, status: :reject}
  ]

  test "public-path verdicts match the frozen corpus" do
    assert Enum.map(@corpus, &Map.take(&1, [:id, :domain, :status])) ==
             Enum.map(@corpus, fn %{id: id, domain: domain} ->
               %{id: id, domain: domain, status: verdict(id)}
             end)
  end

  defp verdict(:parser_accept), do: status(Cure.Compiler.parse_source("sup App.Root\n  children []\n"))
  defp verdict(:parser_reject), do: status(Cure.Compiler.parse_source("mod Corpus\n  fn f( = 0\n"))

  defp verdict(:elaboration_accept), do: status(Program.elaborate("mod Corpus\n  fn id(x: Int) -> Int = x\nend\n"))
  defp verdict(:elaboration_reject), do: status(Program.elaborate("mod Corpus\n  fn id() -> Int = missing\nend\n"))

  defp verdict(:kernel_accept), do: status(Kernel.infer(kernel_context(), {:int_lit, 1}))
  defp verdict(:kernel_reject), do: status(Kernel.infer(kernel_context(), {:var, 0}))

  defp verdict(:macro_accept), do: status(Compiler.compile_string(macro_source("0"), emit_events: false))
  defp verdict(:macro_reject), do: status(Compiler.compile_string(macro_source("missing"), emit_events: false))

  defp verdict(:stdlib_accept), do: status(Program.elaborate(stdlib_source("Std.List")))
  defp verdict(:stdlib_reject), do: status(Program.elaborate(stdlib_source("Std.NoSuchModule")))

  defp verdict(:antigen_accept) do
    challenge =
      Challenge.new(
        kind: :elab_program,
        assay: "elab/completeness",
        label: :well_typed,
        payload: %{id: "corpus_accept", src: ElabComplete.source("idx_only/var/rebuild")}
      )

    status(Elab.run(challenge))
  end

  defp verdict(:antigen_reject) do
    source = "mod P\n  fn f() -> Int = true\nend\n"

    challenge =
      Challenge.new(
        kind: :elab_program,
        assay: "elab/completeness",
        label: :well_typed,
        payload: %{id: "corpus_reject", src: source}
      )

    status(Elab.run(challenge))
  end

  defp status({:ok, _}), do: :accept
  defp status({:ok, _, _}), do: :accept
  defp status(:ok), do: :accept
  defp status({:violation, _}), do: :reject
  defp status({:error, _}), do: :reject

  defp kernel_context, do: Context.empty(Builtins.seed(Env.empty()))

  defp macro_source(body),
    do: "mod Corpus\n  macro Value\n    syntax value becomes #{body}\n  fn f() -> Int = value\nend\n"

  defp stdlib_source(module), do: "mod Corpus\n  use #{module}\n  fn id(x: Int) -> Int = x\nend\n"
end
