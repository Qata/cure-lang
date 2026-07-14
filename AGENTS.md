# ABSOLUTELY CRITICAL SESSION DIRECTIVE

## Current authoritative macro specification

Follow:

`docs/superpowers/specs/2026-07-14-compile-time-reflective-beam-macros-design.md`

for the remaining macro and BEAM work. It is now the authoritative design
document for the implementation. The autopilot plan below remains the ordered
execution ledger, but older open-gate wording must be interpreted through this
specification. In particular, macros are compile-time-only: generated runtime
code must contain direct compiled behavior and must not contain a syntax
interpreter, runtime macro dispatcher, opaque OTP container, or other
indirection layer introduced by macro expansion.

The specification's ordered implementation phases are mandatory. Continue
through them and their verification gates without returning control while any
phase or documented gap remains.

Continue executing every phase and gate in the ordered plan in:

`docs/superpowers/plans/2026-07-12-macro-facility-autopilot-state.md`

The authoritative implementation sequence is the plan's `ORDERED TRANSPARENT
BEAM PLAN`: first merge `kernel-parity-batch` into `idris-parity`, then merge
`idris-parity` into `core-let-binder`; next implement the checked BEAM algebra,
transparent recursive inside-out macro expansion, `beam_ops`, the `actor`,
`fsm`, `sup`, and `app` standard-library macros, bespoke compiler-path removal,
and the final Unix/AtomVM verification gates. Follow that plan in order until
every item is implemented and verified.

Do not voluntarily return control to the user, stop at a partial implementation,
or end with a proposal while tasks remain. Continue through implementation,
verification, required reviews, documentation/state updates, and commits until
the autopilot document's remaining tasks and every gate in the ordered plan are
complete. Do not stop after documentation, a partial macro implementation, or
a passing intermediate test suite.

Maintain the repository's existing constraints throughout:

- Commit after every phase with a highly descriptive commit message.
- Do not modify trusted Core behavior under `lib/cure/core/*` for convenience
  or to add macro-specific behavior. A principled primitive-reduction
  completeness fix, such as compile-time Atom-literal equality, is permitted
  only when it follows the new specification and passes its full TCB,
  termination, Antigen, and full-suite gates.
- Run focused verification during each phase and the full test gate before
  declaring completion.
- Preserve unrelated user changes and never use destructive git operations.
- Do not restore bespoke OTP container classes deleted by the parity branch;
  resolve integration in favor of the transparent macro architecture.
- Keep the compiler OTP-agnostic: `actor`, `fsm`, `sup`, `app`, behavior names,
  callback vocabularies, and OTP lowering must be defined in Cure itself using
  ordinary language constructs, macros, checked algebra, and explicit foreign
  primitives. Moving the same knowledge into an Elixir helper is not enough.
  A user-defined actor-like abstraction must be possible without changing the
  compiler.
- Do not declare the work complete while any plan item, merge conflict, legacy
  regression, missing new test, runtime proof, or documented implementation gap
  remains.

This directive is absolutely critical for the duration of this worktree task.
