# Audit findings (open, deliberately RED)

One file per audited source file, produced by a per-file agent sweep of the
dependent Core / kernel / normalizer / elaborator, plus codegen and parser.

**These tests are RED on purpose.** Each is an executable claim that the audit
believes describes correct behaviour. They are NOT regressions and are NOT part
of the verification gate — the gate is:

    MIX_ENV=test mix test test/cure test/antigen test/oracle \
        test/cure_test.exs test/oracle_replay_test.exs

which does not include `test/audit`. Every test here carries `@moduletag :audit`.

A red test here proves nothing on its own: it is red because it asserts behaviour
the code does not have, which is equally consistent with "the code is wrong" and
"the claim is wrong". Two failure modes seen in this batch:

  * a mis-authored CONTROL that aborts the test before its real assertion
    (the original `inductive_audit_test.exs` I1 declared family `:BadLiteral`
    but put a negative occurrence of a *different* family, `:Bad`, in its field —
    `:ok` was the correct answer);
  * a claim resting on a STALE COMMENT in `lib/` rather than on the live code
    (`validator.ex`'s "STILL PRODUCED" note about `{:rewrite, ...}`, which has no
    producer).

Confirm a finding by executing an independent probe against the real API before
believing it.

## Promoted out of this directory (confirmed, fixed, now gated)

  * `kernel_audit_test.exs`    -> `test/cure/core/bounded_lit_coverage_soundness_test.exs`
  * `inductive_audit_test.exs` -> `test/cure/core/positivity_typealias_soundness_test.exs`

## Running a probe without perturbing the build

`mix run` re-emits the 6 MB escript on every invocation (the `compile:` alias in
mix.exs), which makes concurrent probing unsafe and slow. Use the prebuilt beams:

    ERL_LIBS=_build/test/lib elixir path/to/probe.exs

No writes, ~0.4s startup.
