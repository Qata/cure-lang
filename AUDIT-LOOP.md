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

## Iteration 3 — audit of iteration 2's fixes (3 agents) + fixes

Fresh 3-agent Opus audit of `ee07b6c`/`a8bbbfa`/`817b45e`. Each finding verified
against source myself before counting.

- **CLI audit (I2/I4): CLEAN.** No new defects. One pre-existing non-regression
  noted (`migrate_project_edition(".")` keys off CWD, not the migrated files'
  dir) — unchanged by the fix, not counted.
- **project audit: two real defects** (one a regression the iteration-2 fix
  introduced). Both FIXED this cycle.
- **cross-cutting audit: F-A/F-B/F-C.** F-A had a LIVE sub-part (fixed) and a
  LATENT sub-part (escalated). F-B/F-C are LATENT. `compare/2`/`year/1` totality,
  the lexer keyword-gating fold, and the phase-2 bump write-side all verified
  CLEAN.

### Iteration 3 — FIXED (commit `86b9be3`, full suite 3845 passed / 0 failed)
- **I1b (MED regression):** iteration-2's `$`-anchored loader regex stopped
  recognising a TOML array-of-tables header `[[deps]]` as a section boundary →
  its keys leaked into the preceding `[project]` table, while the writer still
  bounded on it (writer/loader split again). Broadened `table_header_name/1` to
  `\[{1,2}..\]{1,2}` and derived BOTH writer boundary predicates from it —
  one grammar by construction. Red test: array-of-tables load round-trip.
- **I1c (LOW):** loader tolerated `[ project ]` (internal whitespace) but writer
  `project_header?` required literal `[project]` → duplicate table on write.
  `project_header?` is now `table_header_name(line) == "project"` (agrees with
  the loader; dotted `[project.env]` still excluded). Red test: no-duplicate.
- **F-A LIVE (MED):** the build pipeline (`compiler.ex` lex/parse) never calls
  `Cure.Edition.resolve`, so a well-formed but unknown `@edition("9999")` was
  only format-checked and compiled silently — violates spec §3.1 ("a typo'd
  edition must fail loudly") / §3.3. The parser now allow-list-validates the
  pragma via `Cure.Edition.valid?/1`, raising a distinct `:edition_pragma_unknown`
  error. Red test in `edition_pragma_hardening_test.exs`.

### Iteration 3 (cont.) — the escalated findings, now FIXED

Operator lifted the escalation gate ("just fix them; I don't care if you can't
TDD them, if you find a bug, fix it"). The three latent findings below were fixed
this cycle; full suite **3852 passed / 0 failed** (81s). Each is behaviourally
identical under the single minted edition (so the suite proves no regression) but
correct for a future second edition; F-A also closes a live spec-§3.1 gap and is
testable at the compile-resolve boundary.

- **F-A → FIXED (`2aee2e9`, `614f29a`).** `Cure.Compiler` (`compile_string`/
  `compile_and_load`/`parse_source`) now resolves each source's edition
  (`resolve_edition/2` = `Cure.Edition.resolve`) and threads it into the
  lexer/parser, so a file's `@edition` pragma actually drives its lexing on the
  build path and an unknown edition fails the compile loudly with
  `{:edition_error, reason}`. Tests: `edition_compile_test.exs` (unknown pragma
  and unknown manifest edition both fail loudly; valid ones compile). `pragma_edition`
  made a bounded leading-line scan (it now runs on every compile). **Deliberately
  NOT done:** blanket-passing `project_dir` from CLI build callers — that would
  misapply an app's manifest edition to stdlib/dep files compiled in the same
  build. The per-file pragma path is fully wired; manifest-wide build resolution
  needs per-file project-root discovery (walk up to the nearest `Cure.toml`) —
  a smaller, well-scoped follow-up, noted below.
- **F-B → FIXED (`671ec68`).** `cure migrate` now parses the INPUT under the
  file's source edition (`from` = its pragma, else the project edition threaded
  from `cmd_migrate`); the fixpoint verify reparse stays on `target`.
- **F-C → FIXED (`614f29a`, `671ec68`).** `pragma_capture`, `migrate_edition_pragma`,
  and `migrate_splice_edition` tolerate the parser's interior whitespace
  (`@\s*edition\s*\(`), so a spaced pragma is no longer invisible to resolution
  or duplicated by the bump.

## Outstanding after iteration 3 (fresh audit running)

- **Follow-up (from F-A, LOW/design):** wire manifest-wide edition into the CLI
  build path *correctly* — resolve each file under the nearest ancestor
  `Cure.toml`, not a blanket cwd `project_dir` (which would misapply the app
  edition to stdlib/deps). Deferred as a scoped task, not a blocker; the pragma
  path already covers per-file incremental migration.

## (superseded) Blocked — needs operator

The three remaining confirmed findings are all **LATENT** — none can misbehave
until a **second edition** is minted (today `@known == ["2026"]`, so every path
resolves to the one value). They are **not TDD-fixable now** (a red test needs a
real retired keyword / a 2nd edition to make the wrong behaviour observable), and
two require **design decisions on the compile / migrate pipelines that the spec &
plan deliberately did not scope**. Per the loop's escalation guardrail, recorded
here rather than blind-patched on hot paths. Operator: pick a resolution per item.

- **F-A LATENT [HIGH-when-live] — build pipeline is edition-blind for lexing.**
  `compiler.ex` `lex/parse` (245-256) and every `cure build`/`run` caller never
  call `Cure.Edition.resolve/1` nor pass `:edition`; the lexer always uses
  `current()`. So §4's edition-parameterized lexing is dead on the build path:
  once a keyword is retired at edition N, a file pinned to edition N-1 will fail
  to `cure build` (the retired word won't lex as a keyword) — defeating the
  feature's headline purpose. The LIVE half (unknown pragma) is already closed at
  the parser. **Decision needed:** wire `resolve/1` into the compile pipeline
  (where — `compiler.ex` vs each CLI caller? how is `project_dir` derived from a
  file path? per-build Cure.toml caching? does a resolve error abort the build?).
  This is an unplanned integration task on the hot path, not a localized fix.
- **F-B LATENT [HIGH-when-live] — `cure migrate` parses the INPUT under the
  TARGET edition, not the source.** `plan_migration_source` (cli ~1304-1305) and
  `migrate_preflight_file` tokenize/parse the source with `edition: target`. To
  detect a keyword retired *at* target you must parse under the OLD edition where
  it's still a keyword; under target the construct lexes as a bare identifier, the
  rule silently no-ops, and phase 2 bumps anyway. Masked today (proto/impl ship
  `enforced_in: nil`, 2026 is the floor). I2/F12 correctly fixed the *verify*
  reparse to use `target`; the two edition roles (parse-input = source,
  verify-output = target) are conflated onto `target`. **Decision needed:** thread
  the project (source) edition into parse-input while keeping verify at target.
  Not TDD-able now — the real migrate path uses the live registry, not injectable
  fixture rules, so no crossing exists that makes input-parse-edition observable.
- **F-C LATENT [MED] — pragma whitespace grammar drift.** The parser is
  whitespace-insensitive, so `@edition ("2026")` / `@ edition("2026")` parse as
  valid pragmas, but the regex surfaces (`Cure.Edition.pragma_edition`, cli
  `migrate_edition_pragma`/`migrate_splice_edition`) require tight `@edition(` →
  a spaced pragma is invisible to resolution and to the phase-2 bump splicer.
  Masked now (default == the only valid value). **Decision needed (low-stakes):**
  tighten the parser to reject interior whitespace, OR loosen the three regexes to
  tolerate it — semantics-only, prefer the lower-risk direction. Recorded, not
  guessed.

**Loop status:** iteration 3 fixed every LIVE/testable bug; the suite is green.
The residue is latent multi-edition/design work that the autonomous loop must not
self-decide. Operator notified once (see below). The cron is **left in place**
per the escalation guardrail; a subsequent fire that finds only this Blocked
section (no new testable findings) should STOP quietly WITHOUT re-notifying and
WITHOUT deleting the cron — await an operator design decision or an explicit
cancel. Do NOT merge.

---
