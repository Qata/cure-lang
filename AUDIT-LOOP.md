# Editions Audit-Fix Loop

Self-perpetuating fix→audit→fix loop (operator-requested). Driver: cron `7e672a7d`
(every 10 min). Stop condition: **two consecutive clean audits** → cron self-deletes.
Branch `autopilot/editions`, worktree-local. **Do NOT merge.** All commits ghost-authored.

Convergence rule: a cycle fixes the current Outstanding list, runs the full suite, then
runs a fresh adversarial audit. Zero confirmed bugs on two consecutive audits = done.

---

## Iteration 1 — Outstanding findings (from the initial 4-agent audit, all verified)

Fix these this cycle. Severity in brackets. Grouped by file for commit batching.

### Parser (`lib/cure/compiler/parser.ex`)
- **[MED] F1 — placement guard bypassed by decorator-led defs.** `mark_seen_if_stmt/1`
  (~5525) skips flipping `seen_stmt?` on any `:at` token, but a whole decorated def
  (`@extern fn`, `@derive rec`) is one `:at`-led statement → never marks seen → a later
  misplaced `@edition` passes `file_leading?/1` and is silently accepted. CONFIRMED
  empirically. Fix: only a *leading `@edition` pragma* is non-substantive; every other
  decorator marks seen. Peek the decorator name after `:at`.
- **[LOW] F7 — malformed `@edition` value accepted silently.** parse_at edition branch
  (~5013) never validates the arg; `@edition(2026)` unquoted / `@edition("abc")` / bare
  `@edition` parse clean → pre-scan returns nil → silent default-edition fallback. Fix:
  validate the pragma arg is `"YYYY"` and error `{:edition_pragma_malformed, l, c}` else.
- **[LOW] F3 — multiple `@edition` pragmas accepted; only first honored.** Same root as
  F1. Fix: the edition branch marks `seen_stmt?` true after accepting, so a 2nd errors.

### Migrate engine (`lib/cure/migrate.ex`)
- **[MED] F2 — `run_to_fixpoint/2` duplicates warnings across passes.** (~165/175)
  `warns ++ pass_warns` each pass; a `:warn`/`:manual` rule firing on N passes → N copies.
  CONFIRMED (code + agent empirical). Fix: dedup the returned warns by {rule,file,line}.
- **[MED] F3b — fixpoint crashes on unrenderable/unparseable output.** (~153/192)
  baseline + verify `quoted_to_string` are outside try/rescue; a rule emitting an
  unprintable AST (or Lexer/Parser raising) crashes all of `cure migrate`. CONFIRMED
  empirically (crashed at :153). Fix: rescue → clean `{:error,{:verify_failed,_}}`.
- **[LOW] F-culprit — `verify_failed` blames `List.last(pass_warns)`** (~178), the last
  rule that *warned*, not the one that broke verify. Fix: report all fired rule ids
  (uniq), matching the `no_convergence` branch.
- **[LOW] F12 — verify reparses without the target `edition:` opt** (~194). Latent with
  one edition. Fix: thread the crossing target edition into verify's reparse.

### Edition core (`lib/cure/edition.ex`)
- **[MED] F6 — `resolve/1` crashes on explicit `%{source: nil}`** (~90). `Map.get(input,
  :source, "")` defaults only for an absent key; explicit nil → `is_binary` guard →
  FunctionClauseError. CONFIRMED (code + agent empirical). Fix: coalesce nil → "".
- **[LOW] F8 — `compare/2`/`year/1` raise on non-numeric 4-char string** (~52).
  `<<y::binary-size(4)>>` matches any 4 bytes then `String.to_integer` raises. Fix: match
  only 4-digit strings (regex/guard); non-edition input → clear error, not a crash.

### Project (`lib/cure/project.ex`)
- **[LOW] F10 — `set_edition/2` can duplicate the `[project]` table / cross-table edits**
  (~120). Header regex `^\s*\[project\]\s*$` misses a header with a trailing comment;
  existing-key replacement rewrites `edition=` in *all* tables. Fix: tolerate trailing
  comment on the header; scope the key replacement to the `[project]` table only.

### CLI (`lib/cure/cli.ex`)
- **[MED] F4 — downgrade guard measures against compiler-latest, not project edition**
  (~1225/1266). `:current` param plumbed but unwired → once 2027 mints, `--edition 2026`
  in a 2026 project wrongly refuses. Fix: pass the resolved project edition as `:current`.
- **[LOW] F5 — downgrade rejection is silent** (~1264/143). `{:error, :downgrade}` prints
  nothing, exits 1. Fix: route through `error/1` with a clear message.
- **[LOW] F9 — bump pragma regex looser than Edition → crash.** `migrate_edition_pragma/1`
  (~1545) captures `[^"]+`; `@edition("abc")` → `compare(target,"abc")` → String.to_integer
  crash. Fix: require `\d{4}` (consistent with Edition).

### Adjudicated NOT-a-bug (do not "fix")
- F11 (pragma-less standalone files left unpinned post-migration): by-design — default ==
  latest edition, so a rewritten pragma-less file correctly floats at latest. Documented.

**Outstanding count: 12 findings across 5 files (+1 adjudicated by-design).**

### Iteration 1 — FIXED (5 commits, full suite 3838 passed / 0 failed)
- `b01d049` parser F1/F3/F7 · `abe8d11` migrate F2/F3b/F12/culprit · `db1e64f`
  edition F6/F8 · `8dead22` project F10 · `711b11b` cli F4/F5/F9. All 12 fixed;
  +21 hardening tests. Then a fresh 4-agent audit ran on the fix commits.

---

## Iteration 2 — Outstanding findings (fresh audit of iteration 1's fixes)

The re-audit found real regressions the fixes introduced. Fix these this cycle.

- **[HIGH] I1 — set_edition ↔ load header-grammar divergence (REGRESSION).** My F10
  fix taught `project_header?` to accept `[project] # comment`, but the loader
  `parse_lines` (project.ex:821) requires the header line to END with `]`, so a
  comment-trailing header is not recognised and the written `edition` is dropped
  on read-back — defeating F10a's own headline scenario. Well-formed TOML. Fix:
  teach the loader to tolerate an inline comment after a table header (unify the
  grammar); add a load round-trip test (F10a only checked file text).
- **[MED] I2 — F12 fix is unwired (dead code).** `plan_migration_source` (cli.ex
  ~1309) calls `run_to_fixpoint(attached, rules: rules)` without `edition: target`,
  so verify still reparses under `current()`. Fix: pass `edition: target`.
- **[MED] I3 — set_edition regressed duplicate-edition-key handling.** The new
  first-match replace leaves a stale second `edition=` in the [project] table
  (load last-wins → stale). Pre-fix replaced all. Fix: replace ALL edition keys
  within the [project] section. (Malformed TOML; no clean red test under one
  edition — implement for correctness, document the test gap.)
- **[LOW] I4 — migrate_project_edition masks an invalid declared edition.** Maps
  any `{:error,_}` from resolve to `current()`, so a `Cure.toml` with a bad
  `[project].edition` silently defeats the downgrade guard in a multi-edition
  future. Fix: surface `{:unknown_edition,_}`; fall back only for no-project.
- **[LOW] I5 — `~r/^\d{4}$/` accepts a trailing newline (`$` pre-newline).**
  Unreachable (single-line literal), belt-and-suspenders. Fix: `\A\d{4}\z`.

### Iteration 2 — FIXED (3 commits, full suite 3841 passed / 0 failed)
- `ee07b6c` project I1 (loader `table_header_name/1` tolerates inline comment,
  matching the writer grammar) + I3 (`edition_in_section` replaces ALL edition
  keys in the [project] section) + 2 load round-trip tests.
- `a8bbbfa` cli I2 (`plan_migration_source` passes `edition: target` to the
  fixpoint) + I4 (`migrate_project_edition` surfaces `{:unknown_edition,_}`,
  cmd_migrate threads it through `with`) + 1 new red test (unknown declared ed).
- `817b45e` parser I5 (`\A\d{4}\z`).
Then a fresh audit ran on these fix commits (iteration 2's audit step).

### Iteration 2 — Adjudicated ACCEPTED (fail-safe / malformed-input, not fixed)
- I6 — bare `rescue _` in migrate `verify/3`+`safe_print/1` is broad. It fails
  SAFE (aborts, never emits wrong output); narrowing precisely is fragile. A
  compiler bug during migrate is relabelled verify_failed — diagnosability cost
  only. Accepted as defensive-by-design.
- Dup `[project]` tables (malformed TOML): set_edition updates the first, loader
  last-wins the second. Invalid input; both paths best-effort. Accepted.

---
