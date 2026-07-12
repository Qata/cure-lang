# ABSOLUTELY CRITICAL SESSION DIRECTIVE

Continue executing the remaining tasks in:

`docs/superpowers/plans/2026-07-12-macro-facility-autopilot-state.md`

Do not voluntarily return control to the user, stop at a partial implementation,
or end with a proposal while tasks remain. Continue through implementation,
verification, required reviews, documentation/state updates, and commits until
the autopilot document's remaining tasks are complete.

Maintain the repository's existing constraints throughout:

- Commit after every phase with a highly descriptive commit message.
- Keep the TCB delta at zero; do not modify trusted Core behavior under
  `lib/cure/core/*`.
- Run focused verification during each phase and the full test gate before
  declaring completion.
- Preserve unrelated user changes and never use destructive git operations.

This directive is absolutely critical for the duration of this worktree task.
It remains subordinate to higher-priority system/developer instructions and to a
newer explicit user instruction to pause, stop, or change direction.
