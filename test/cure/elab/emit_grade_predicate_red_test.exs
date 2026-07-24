defmodule Cure.Elab.EmitGradePredicateRedTest do
  @moduledoc """
  FINDING C (erasure-unify cluster): `Cure.Elab.Emit.generic_branch_clause/3`
  (lib/cure/elab/emit.ex:1067) decides whether a constructor field's binder
  slot is "present" at runtime with a raw `q == :unrestricted` check, instead
  of `Cure.Core.Grade.present?/1` (`not erased?/1`) — the predicate
  `Cure.Elab.Erase.erase/2` itself uses to decide which constructor
  ARGUMENTS survive erasure (lib/cure/elab/erase.ex, `Grade.present?(q)`
  filter in the `:ctor` clause).

  For any grade OTHER than `:unrestricted` and `:erased` — i.e. `:linear` or
  `:affine` — the two disagree: `Grade.present?/1` says the field IS present
  (kept at construction), but emit's raw check says it is NOT (dropped from
  the `case` pattern). This test builds a synthetic single-constructor family
  with a `:linear`-graded field directly at the `Cure.Core.Inductive` level
  (bypassing surface syntax, which does not yet expose linear/affine ctor
  fields — see `docs/.../qtt-grades-progress` — so this is unreachable from
  today's parser but very much live at the Core/Emit boundary any future
  surface extension, or a hand-built Core term, can reach).
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Grade, Inductive}
  alias Cure.Elab.Emit

  test "a :linear-graded constructor field is emitted as present, matching Grade.present?/1" do
    dummy_type = {:type, 0}

    # `Box` has exactly one constructor, `MkBox`, with a SINGLE field graded
    # `:linear` (present, per `Grade.present?/1` — only `:erased` is absent).
    ctor = Inductive.ctor(:MkBox, [{:v, dummy_type}], [], [:linear], [])
    family = Inductive.family(:Box, [], [], 0)

    box_type = {:data, :Box, [], []}

    env =
      Env.empty()
      |> Inductive.declare(family, [ctor])

    mk_type = {:pi, Grade.unrestricted(), dummy_type, box_type}
    mk_body = {:lam, Grade.unrestricted(), dummy_type, {:ctor, :MkBox, [{:var, 0}]}}

    # `access` cases on the single `MkBox` branch and returns its one field.
    access_type = {:pi, Grade.unrestricted(), box_type, dummy_type}

    access_body =
      {:lam, Grade.unrestricted(), box_type, {:case, {:var, 0}, dummy_type, [{:MkBox, 1, {:var, 0}}]}}

    env =
      env
      |> Env.add_def(:mk, mk_type, mk_body, [Grade.unrestricted()])
      |> Env.add_def(:access, access_type, access_body, [Grade.unrestricted()])

    result =
      Emit.compile_and_load(env,
        module: Cure.Elab.EmitGradePredicateRedFixture,
        functions: [:mk, :access]
      )

    # DESIRED POST-FIX BEHAVIOR: `Grade.present?(:linear)` is `true`, so the
    # `MkBox` field must survive to the runtime tuple AND be bound by the
    # `case` pattern that reads it back out. `mk(42)` builds `MkBox` around
    # 42, and `access/1` must recover exactly that 42.
    assert {:ok, mod} = result, "expected the module to compile and load, got: #{inspect(result)}"
    assert mod.access(mod.mk(42)) == 42
  end
end
