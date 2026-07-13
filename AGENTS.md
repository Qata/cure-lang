# ABSOLUTELY CRITICAL SESSION DIRECTIVE

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
- Keep the TCB delta at zero; do not modify trusted Core behavior under
  `lib/cure/core/*`.
- Run focused verification during each phase and the full test gate before
  declaring completion.
- Preserve unrelated user changes and never use destructive git operations.
- Do not restore bespoke OTP container classes deleted by the parity branch;
  resolve integration in favor of the transparent macro architecture.
- Do not declare the work complete while any plan item, merge conflict, legacy
  regression, missing new test, runtime proof, or documented implementation gap
  remains.

This directive is absolutely critical for the duration of this worktree task.
