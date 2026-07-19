# Continuous Implementation Directive

The authoritative specification for this worktree is:

`docs/superpowers/specs/2026-07-14-compile-time-reflective-beam-macros-design.md`

Keep implementing, testing, documenting, reviewing, and committing the work
until that specification is fully implemented and every verification gate it
requires passes.

Do not stop or return control merely because an intermediate phase is complete,
a focused test suite passes, a useful partial implementation has landed, or the
next step is difficult. If the specification still contains an unimplemented
requirement, documented gap, unchecked invariant, missing test, compatibility
regression, or outstanding verification gate, continue working on it.

Treat plans and subsidiary specifications linked from the authoritative
specification as part of its implementation requirements. Keep their status
accurate as work proceeds, and commit each coherent completed phase with a
descriptive commit message.

Only declare completion when the authoritative specification and all of its
linked mandatory work are implemented, the repository is clean, and the full
required verification matrix is green. Stop earlier only when genuinely
blocked by missing user authority or information that cannot be discovered
from the repository; in that case, explain the exact blocker and the exhausted
in-scope alternatives.

Preserve unrelated user changes, avoid destructive git operations, keep the
compiler OTP-agnostic, and do not reintroduce runtime macro interpreters,
dispatchers, or bespoke opaque OTP containers. Macro expansion must remain
compile-time-only and produce direct checked runtime behavior.

For elaboration debugging, use `Cure.Dev.Trace` from `lib/cure/dev/trace.ex`
before adding ad-hoc instrumentation or modifying trusted Core code.
