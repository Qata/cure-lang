defmodule Antigen.Assays.DotForcing do
  @moduledoc """
  `forcing/dot` — the known-label oracle for the forced/dot-pattern
  ("dot-forcing") check (ledger row #24). Builds a v1-menu context, computes the
  branch-unify substitution the kernel pins for the chosen (family, ctor,
  scrutinee indices), and drives the exact forced-annotation check via the public
  `Cure.Elab.Elaborator.forced_check_probe/7` shim (which delegates to the real
  `named_implicit_forced_value/4` + `Conv.conv?/5`). The returned outcome category
  (`:accept` | `:reject` | `:unforced`) must match the correct-by-construction
  label; a disagreement is a dot-forcing soundness infection.

  Generality: this exercises the forced-value resolution
  (`named_implicit_forced_value`, telescope position `arity-1-p`), the `:unforced`
  gate, and the convertibility decision — the UNIQUE content of the named-implicit
  check. It does NOT cover the surface dot-syntax parse (852742a) nor the
  carried-eq motive branch, which skips the named-implicit check entirely per
  5409184; and being discard-only is structural (the check adds no binding), not
  asserted by this value oracle.
  """
  alias Antigen.{Challenge, Generators}
  alias Cure.Core.{Context, Eval, Kernel}
  alias Cure.Elab.Elaborator

  @nat_type {:vdata, :Nat, []}

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :dot_forcing, label: expected, payload: p}) do
    env = Generators.SigMenu.env_of(:v1)

    ctx =
      Enum.reduce(1..p.ctx_vars//1, Context.empty(env), fn _, c ->
        Context.extend(c, @nat_type)
      end)

    index_vals = Enum.map(p.indices, &Eval.eval(&1, Context.env(ctx)))

    # The kernel's branch-unify verdict IS the index inversion the elaborator
    # threads into check_named_implicits (`{:solved, s} -> s`; otherwise `%{}`).
    subst =
      case Kernel.branch_unify(ctx, p.family, p.cname, index_vals) do
        {:solved, s} -> s
        _ -> %{}
      end

    # v1 families are index-only (0 params), so scrut_param_vals is [].
    got =
      case Elaborator.forced_check_probe(env, ctx, p.cname, [], subst, p.name, p.written) do
        :ok -> :accept
        {:forced_pattern_mismatch, _t, _d} -> :reject
        {:named_implicit_unforced, _name} -> :unforced
      end

    if got == expected do
      :ok
    else
      {:violation, {:dot_forcing_disagreement, %{payload: p, expected: expected, got: got}}}
    end
  end
end
