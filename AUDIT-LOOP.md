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

## Iteration 4 — audit of iteration 3's fixes (2 Opus agents) + fixes

The escalation gate was lifted by the operator ("just fix them… if you find a
bug, fix it"), so F-A/F-B/F-C — previously escalated as latent/design-blocked —
were all fixed in iteration 3's tail (build-path `resolve/1` wiring `2aee2e9`,
source-edition parse-input `671ec68`, pragma whitespace tolerance `614f29a`).
Iteration 4 audited those fixes and the F-A/F-B/F-C follow-ups.

### Iteration 4 — carried-over findings FIXED

- **CLI Finding 1 [MED, live regression] — `eb33b88`.** The phase-2 bump detected
  and spliced the `@edition` pragma with a whole-body regex, so an `@edition(...)`
  buried in a comment/string falsely triggered a bump (in-comment mutation, no
  real leading pragma added). The F-C whitespace widening extended this to spaced
  forms, making it reachable with the single minted edition. Fixed: detection
  routes through `Cure.Edition.pragma_edition` (anchored to the first substantive
  line); splice rewrites only that leading line. Red: a spaced `@ edition("2020")`
  in a comment no longer bumps.
- **Compiler F1 [latent] — `bfde322`.** The parser accepted pragma forms the
  single-line pre-parse resolver could not see: a **multi-line** pragma (parser
  honoured the declared edition while the resolver lexed under the default → silent
  wrong-edition once a 2nd edition exists) and an **indented** pragma (resolver's
  `^\s*@` over-matched a form the parser rejects as placement). Fixed both:
  parser rejects a multi-line pragma as `:edition_pragma_malformed`; resolver
  regex anchored at column 0 (`^@`). The two now agree on what a valid pragma is.
- **F2 [polish] — `e21f3b1`.** The `@edition` pragma errors and the compile-boundary
  `{:edition_error, {:unknown_edition, _}}` hit the catch-all `inspect`. Added
  dedicated `format_error` clauses; unknown-edition variants list the known set.
- **CLI Finding 2 [latent] — `5651ace`.** The downgrade guard measured target vs
  the *project* edition only; a file pinning a newer edition via its own pragma
  (`from`) slipped through and would be rewritten onto an older keyword set.
  Fixed: `plan_migration_source` refuses `from > target` (`{:error, :downgrade}`);
  `migrate_preflight` aborts the run with a precise message. Probed at the pure
  planner with hypothetical editions (unreachable end-to-end with one edition).

### Iteration 4 — fresh audit result (2 Opus agents, verified against source)

- **parser.ex / errors.ex slice — CLEAN.** Verified myself: the literal `meta`
  always carries `:line` (a plain `"YYYY"` arg lexes as a `:string` token with a
  line; the line-less literal only arises inside string interpolation, unreachable
  here); `single_line_edition_pragma?` runs after `valid_edition_pragma_arg?` so
  `args` is guaranteed a one-element literal list; the new formatter clauses
  precede the catch-all and their tuple shapes are disjoint from every earlier
  clause.
- **cli.ex / edition.ex slice — ONE confirmed LOW regression (now FIXED, `a5f8131`).**
  `replace_leading_pragma_line` split on `"\n"`, so on a CRLF file the replaced
  pragma line dropped its `\r` → mixed EOL (the old substring `Regex.replace`
  preserved CRLF). Latent (the bump path needs a 2nd edition to fire), but a
  genuine output-corruption regression I introduced. Red: `migrate_splice_edition`
  on a CRLF body now preserves `\r\n`. All other hunts (trivia-predicate agreement,
  `^@` missing a real pragma, downgrade-guard caller/shape preservation, result
  bucket double-handling) were traced and REFUTED against source.

### Iteration 4 — FIXED (5 commits, full suite 3864 passed / 0 failed)

`eb33b88` (CLI Finding 1) · `bfde322` (Compiler F1) · `e21f3b1` (F2 messages) ·
`5651ace` (CLI Finding 2) · `a5f8131` (CRLF, from this iteration's own audit).

## Iteration 5 — F-A follow-up fixed + audit of it (2 Opus agents)

### Iteration 5 — carried-over finding FIXED

- **F-A follow-up [was LOW/design] — `913aa99`.** The compile boundary honoured a
  project's `[project].edition` only when a caller passed `:project_dir`, but the
  `cure build`/`run` callers never did — so a project manifest's edition (incl. a
  typo'd one) was silently ignored on the build path (§3.1 "fail loudly" violated
  for a bad manifest). Added `Cure.Project.find_root/1` (walk up from the file's
  dir to the nearest ancestor `Cure.toml`) and had `resolve_edition/2` discover
  the project root from the file path when `:project_dir` is absent. Nearest wins;
  `parse_source` stays headless; a no-`:file` compile does not discover (nil
  guard). Red: `compile_file` under a dir with a typo'd `Cure.toml` now fails
  loudly; child-manifest shadows parent; pragma still overrides the manifest.

### Iteration 5 — fresh audit result (2 Opus agents, every finding verified against source)

Both agents: **no today-triggerable bug** (suite green because no ancestor
`Cure.toml` exists above the compiled sources today, and with one minted edition
a *valid* manifest can only resolve to the default). Two **latent** hazards from
the newly-broad auto-discovery, both confirmed by reproduction:

- **Unbounded upward walk [MED, latent] — FIXED `0b4d2f3`.** `find_root` walked to
  the filesystem root, so a file with no nearby manifest could bind to an
  unrelated ancestor `Cure.toml` (a sibling/parent project, a stray `~/Cure.toml`)
  — with a typo'd/foreign edition that would *spuriously fail* this repo's own
  internal stdlib/example/compile mix tasks, which previously consulted no
  manifest for such sources. Fixed: bound the walk at the enclosing git repo (a
  dir holding `.git`; a git worktree's `.git` file counts), returning nil at the
  repo root with no manifest. Red: a `Cure.toml` above a `.git` boundary is no
  longer discovered; a `Cure.toml` AT the repo root still is. This also corrects
  a **git dependency** (LATENT-1, git flavour): its checkout carries its own
  `.git`, so its sources now resolve under the dependency's OWN manifest/default
  instead of inheriting the consuming app's edition.
- **REPL `:load` of a file under an unrelated project [LOW, latent].** Same root
  cause; now bounded by the `.git` fix (a REPL-loaded file only binds to a
  manifest within its own repo). Considered resolved by `0b4d2f3`.

### Iteration 5 — FIXED (2 commits, full suite 3874 passed / 0 failed)

`913aa99` (F-A follow-up: nearest-ancestor discovery) ·
`0b4d2f3` (bound discovery at the git-repo root).

## Iteration 6 — LATENT-1 fixed + fresh 3-Opus audit of the editions slices + fixes

**Outstanding from iteration 5 (LATENT-1) — FIXED first:**

- **LATENT-1 residual (path/tarball dep edition inheritance)** — `4b300ef`: pinned
  `project_dir` at both dep-compile sites (path `resolve_one`, `install_tarball`)
  so a manifest-less dep resolves under its own base/default, never the consumer's
  edition. Red→green via a public `resolve_deps/1` path-dep fixture
  (`test/cure/project/dep_edition_isolation_test.exs`).

**Fresh audit — 3 parallel Opus agents over the changed slices** (project/dep,
compiler/edition resolve, CLI migrate). 10 raw claims; **each verified against
source before counting** (two agent line-refs were wrong — `detect_app` is
`project.ex:703` not `compiler.ex:711`; `compiler.ex` is only 424 lines — corrected
by reading the real code). Confirmed-real findings, all FIXED this cycle:

- **A3-F1 + A3-F2 (migrate splice data-loss)** — `e012adb`: `replace_leading_pragma_line`
  replaced the whole leading line, so it (a) dropped a trailing comment on the pragma
  line and (b) DESTROYED the entire body of a lone-CR file (no `\n` ⇒ one "line").
  Now rewrites only the matched `@edition(...)` token; trailing content + EOL survive.
- **A2-F1 (TOML inline comment → spurious hard fail)** — `e07fc24`: `edition = "2026"  # pin`
  leaked the comment into the value (`2026"  # pin`) and hard-failed a VALID edition.
  `parse_kv` now strips the first `#` outside quotes (a `#` inside a quoted value kept).
- **A1-F2 (blank-path dep crash)** — `be4c43b`: `{ path = "" }` routed to the git clause
  (a `git: nil` key) and crashed `System.cmd` on a nil URL. Now `{:error, {:invalid_dependency, name}}`;
  git clause guarded on a binary URL.
- **A1-F1 (nested dep manifest ignored)** — `d5f8e07`: `Cure.Project.load` reads `<dir>/Cure.toml`
  directly, so the fixed `project_dir: target` missed a tarball dep's own manifest under the
  nested `target/<pkg>-<vsn>/` layout the `**/lib/**` glob anticipates. New base-bounded
  `dep_project_dir/2` finds the dep's own Cure.toml yet never escapes into the consumer tree.
- **A2-F2 (app-detect pre-pass ignored per-file editions)** — `02a8b4c`: `detect_app` lexed under
  `current()`; now resolves each file's edition (pragma > project > default) and threads it.
  Latent (one edition) but a real precedence gap. Same commit corrects two stale comments
  (**A2-F3** `parse_source`, **A2-F5** parser unknown-pragma gate) that wrongly claimed the
  build path never calls `Edition.resolve`.

**Verified but DEFERRED as by-design (recorded, not "fixed"):**

- **A2-F4** — the "no edition declared" advisory is deduped once per OS process (a
  single `:persistent_term` key). This is intentional anti-spam for a long-lived
  compiler process; being once-per-process rather than once-per-project is a
  defensible advisory policy, not a correctness bug.
- **A3-F3** — the phase-2 bump's PREPEND branch is unreachable from `migrate_bump`
  (a pragma-less file returns `false` from `migrate_file_bump?`), so a standalone
  file with no `@edition` is not stamped on migration. This matches Rust parity:
  `cargo fix --edition` bumps the PACKAGE manifest (Cure's `migrate_project_bump?`
  path), not each file. Per-file stamping on migration is a separate design choice,
  not a bug; the prepend branch still serves the public `migrate_splice_edition/2`.

**Refuted on verification (not counted):** A1-F3 (git-dep site safe — the fresh
`git clone` always has a `.git` dir bounding `find_root`; the agent self-refuted).

**Full suite after all fixes: 3884 passed, 0 failing** (+9 new tests; 148 immune
responses expected; Antigen shape-coverage 309/309).

## Outstanding findings (after iteration 6)

- None open as bugs. The two items above (A2-F4, A3-F3) are **by-design**, kept
  here as rationale so a future audit doesn't re-flag them.

**Loop status:** iteration 6's fresh audit found 8 confirmed bugs — so it is **NOT
a clean audit**, and the Group-1–5 fixes are NEW code not yet independently audited.
Convergence (two consecutive clean audits) is **not** met. The cron is **left in
place**; the next fire (iteration 7) runs a fresh audit over the iteration-6
changes — a clean result there is the FIRST clean audit, and a second consecutive
clean audit closes the loop. Do NOT merge.

Commits this cycle: `4b300ef` (LATENT-1), `e012adb` (A3-F1/F2), `e07fc24` (A2-F1),
`be4c43b` (A1-F2), `d5f8e07` (A1-F1), `02a8b4c` (A2-F2 + doc A2-F3/F5).

---

## Iteration 7 — fresh 3-Opus audit of the iteration-6 changes + fixes

No open bugs entered this cycle (iteration 6's Outstanding was by-design only), so
this was a pure audit of the iteration-6 diff (`git log 9850ce9..b5d81a3`). Three
parallel Opus agents (project/dep, migrate splice, edition semantics), read-only.
**Every claim verified against source before counting.** The migrate-splice agent
came back **clean** (token-only replacement correct across LF/CRLF/lone-CR/trailing-
comment/empty). The other two surfaced **5 confirmed real bugs**, all fixed:

- **A1-F1 (escaped-quote data loss in `strip_inline_comment`)** — `99c1202`: the
  quote-state toggle ignored backslash escapes, so a `\"` inside a basic string
  wrongly closed it and a following `#` truncated the value. Now tracks `\`-escapes.
- **A1-F3 (whitespace-only path bypassed the blank-dep guard)** — `f9cc1d1`: the
  `!= ""` guard is literal, so `path = "   "` slipped through and silently resolved
  to zero files. Trim before deciding; extracted `resolve_path_dep/3`.
- **A3-F1 (a dep's own unknown edition failed SILENTLY)** — `857305f`: iteration-6's
  `dep_project_dir` routes the dep manifest into `resolve_edition`, so a typo'd dep
  edition makes `compile_file` error — but the `_ =` discard left the build green
  with no beams. New `compile_dep_files/4` propagates `{:dependency_edition_error,…}`
  (other dep compile errors stay non-fatal, as before). Git deps now also route
  through it + `dep_project_dir`, closing the "git dep vendored without .git" leak
  the semantics agent flagged as a consistency gap.
- **A1-F4 (O(N) redundant manifest re-parse in `detect_app`)** — `64e43ab`: resolved
  each file's edition by re-reading+validating the project Cure.toml once per file
  (plus a wasted `find_root` for pragma'd files). Check the cheap pragma first;
  memoize the manifest edition by project root. Behavior-identical, just faster.
- **A3-F2 (parse_source resolved a different edition than the compile path)** —
  `15f33f4`: it passed only `:source`, ignoring the project manifest, so a pragma-
  less file was inspected under `current()` while it compiles under the manifest
  edition (latent: one edition). Now discovers the project root from a real `:file`.

**Verified NON-bugs / by-design (recorded, not fixed):**

- **A3-F3** — `Edition.current` is a hardcoded constant, not `List.last(all())`. This
  is intentional: the default is decoupled from the newest *known* edition so a new
  edition can be minted as opt-in before it is promoted to default (Rust parity).
  Clarified the docstring (`15f33f4`) so it is not "fixed" into a derivation.
- **A1-F2** — `strip_inline_comment` doesn't track TOML single-quoted (literal)
  strings, so a `#` inside `'...'` would be mis-cut. Pre-existing and inert: the
  loader's `strip_quotes`/`parse_scalar` don't support single-quoted strings at all,
  so such a value is already unusable. Out of scope for the editions work.
- **migrate splice raw-`target` interpolation** — `target` is interpolated into the
  `Regex.replace` replacement string, where `\N` would be a backreference. Not
  reachable: `target` is allow-list-constrained to a 4-digit numeric edition. Noted.

**Refuted on verification:** the pre-pass↔compile-pass edition-mismatch hypothesis
(identical source + identical `find_root` ⇒ identical edition); `find_dep_root`
termination/escape (sound); `resolve_one` clause-ordering (correct); dep values
passing through `strip_inline_comment` (they use the separate `parse_dep_line`).

**Full suite after all fixes: 3887 passed, 0 failing** (+3 new tests; 146 immune
responses expected; Antigen shape-coverage 309/309).

## Outstanding findings (after iteration 7)

- None open as bugs. Three by-design/inert items above (A3-F3, A1-F2, the migrate
  interpolation) are recorded as rationale so a future audit doesn't re-flag them.

**Loop status:** iteration 7's fresh audit found 5 confirmed bugs — so it is **NOT
a clean audit**, and the Group A–E fixes are NEW code not yet independently audited.
Convergence (two consecutive clean audits) is **not** met (iterations 6 and 7 both
found bugs). The cron is **left in place**; the next fire (iteration 8) runs a fresh
audit over the iteration-7 changes. Do NOT merge.

Commits this cycle: `99c1202` (A1-F1), `f9cc1d1` (A1-F3), `857305f` (A3-F1),
`64e43ab` (A1-F4), `15f33f4` (A3-F2 + A3-F3 doc).

---

## Iteration 8

Fresh adversarial audit of the iteration-7 changes (`99c1202`, `f9cc1d1`,
`857305f`, `64e43ab`, `15f33f4`) via three parallel Opus subagents over the
changed slices (comment-stripper + `detect_app`; dep resolution; `parse_source` +
edition semantics), read-only. Every returned finding was verified against source
before counting. **4 confirmed bugs fixed.**

**Confirmed bugs (fixed):**

- **F1 — `deps update` MatchError on a git dep with an unknown edition**
  (`cli.ex:877`). Iteration 7 (`857305f`) made `resolve_git_dep/2` route through
  `compile_dep_files`, so it can now return
  `{:error, {:dependency_edition_error, ...}}`. `cmd_deps_update` still bound it
  with `:ok = ...`, which raises a `MatchError` — the comment right above literally
  predicted this. Now reports and aborts like `cmd_deps`. (`ff385ac`)
- **F2 — whitespace-only git URL silently resolves to `:ok`** (`project.ex:277`).
  The A1-F3 whitespace guard was added to the *path* clause but not the *git*
  clause: only literal `git = ""` was rejected, so `git = "   "` reached
  `System.cmd("git", ["clone", …, "   ", target])`, cloned nothing, found zero
  files, and "resolved" to `:ok`. Merged the blank/whitespace git clauses into one
  trim-aware clause mirroring the path clause. (`ff385ac`)
- **F3 — `parse_source` swallows unknown MANIFEST editions** (`compiler.ex:197`).
  Iteration 7 (`15f33f4`) had `parse_source` discover `project_dir` from the real
  `:file`, so `resolve/1` can now return `{:error, {:unknown_edition, _}}` from a
  typo'd manifest for a *pragma-less* source. The parser cannot re-catch a manifest
  error (the manifest isn't in the source), yet the `{:error, _} -> current()`
  branch degraded it to the default — silently hiding a real §3.1 error. Now
  propagates `{:edition_error, reason}` like the compile path; the misleading
  comment claiming the parser re-validates is corrected. (`604d101`)
- **F5 — Edition moduledoc contradicted `current/0`** (`edition.ex:7`). The
  moduledoc still asserted "`current/0` is the newest" while the `current/0`
  docstring (added `15f33f4`) documents the intentional default-vs-newest
  decoupling. Fixed the moduledoc to match (staged-rollout / Rust parity).
  (`604d101`)

**Verified NON-bugs (recorded, not fixed):**

- **`strip_inline_comment` / `detect_app` (agent 1)** — both iteration-7 changes
  traced char-by-char and branch-by-branch; behaviorally correct, no regression.
  The only issue anywhere in that slice is the pre-existing single-quoted-TOML-
  literal limitation (already recorded as A1-F2, untouched by these commits).
- **`compile_dep_files` swallows non-edition errors (agent 2, finding 3)** —
  pre-existing/by-design: it deliberately reproduces the historic `_ =`
  behaviour (a dep may ship files the consumer never exercises); iteration 7
  narrowly promoted only the edition error to fatal. Not a regression.
- **parse_source F2/F3/F4 (agent 3)** — the dep_graph behavior change is the
  intended fix; the synthetic-`:file`-label trap is not realized by any caller
  today; no stray-ancestor `Cure.toml` hazard exists in-repo (worktree `.git`
  file stops `find_root`).

**Full suite after all fixes: 3891 passed, 0 failing** (+4 new tests: 2 dep-iso,
2 parse_source; 138 immune responses expected; Antigen shape-coverage 309/309).

## Outstanding findings (after iteration 8)

- None open as bugs. The by-design/inert items above are recorded so a future
  audit doesn't re-flag them.

**Loop status:** iteration 8's fresh audit found 4 confirmed bugs — so it is **NOT
a clean audit**. Convergence (two consecutive clean audits) is **not** met
(iterations 6, 7, and 8 all found bugs). The cron is **left in place**; the next
fire (iteration 9) runs a fresh audit over the iteration-8 changes. Do NOT merge.

Commits this cycle: `ff385ac` (F1 + F2), `604d101` (F3 + F5 doc).

---

## Iteration 9

Fresh adversarial audit of the iteration-8 changes (`ff385ac`, `604d101`) via
three parallel Opus subagents (dep resolution; `parse_source` propagation;
edition-surface interactions), read-only. Every finding verified against source
before counting. **3 confirmed bugs fixed** (two of them the same defect, found
independently by two agents).

**Confirmed bugs (fixed):**

- **`cure deps update` bypasses the whitespace/empty git-URL guard**
  (`cli.ex:876` → `project.ex resolve_git_dep`). Found independently by agents 1
  and 3. Iteration 8's trim guard lives in `resolve_one/3`, but `cmd_deps_update`
  calls `resolve_git_dep/2` DIRECTLY (the only caller outside `resolve_one`), and
  `""`/`"   "` are truthy in Elixir, so a `git = "   "` dep reached `git clone`
  with a blank URL, cloned nothing, and silently resolved to `:ok` ("Lockfile
  updated") — the exact mode iteration 8 claimed to close, still live on the
  update path. Fixed at the `resolve_git_dep` boundary so BOTH commands agree.
  (`c0beb65`)
- **`resolve_git_dep/2` discarded the clone exit status** (`project.ex`, agent 3;
  pre-existing, not an iteration-8 regression but the mechanism that made the
  above silent). ANY failed clone — unreachable URL, bad tag, network error —
  left an empty dir → zero `.cure` files → `compile_dep_files([])` → `:ok`, a
  bogus green build. Now checks `System.cmd`'s status and fails loudly with
  `{:dependency_clone_failed, name, out}` (via new `ensure_clone/4` helper).
  (`c0beb65`)
- **Stale `parse_source` docstring** (`compiler.ex:175`, agent 2). The
  iteration-8 change added a `{:edition_error, _}` return but left the prose
  contract listing only `:lex_error`/`:parse_error`. Documented the new return.
  (`21f56be`)

**Verified NON-bugs (recorded, not fixed):**

- The two iteration-8 edits themselves are regression-free: the merged git clause
  is behavior-equivalent to the old two-clause form on every `parse_dep_line`
  shape (clause order unchanged, path clause still precedes git); the
  `cmd_deps_update` `case` covers the full `resolve_git_dep` return contract; no
  remaining `:ok = resolve_git_dep(...)` bind exists (no lingering MatchError).
- `parse_source` propagation causes no runtime/consumer breakage: the sole lib
  caller `dep_graph.ex:194` matches `{:error, reason}` generically; no test
  asserts the old `parse_source` pragma-error shape (the pragma tests drive
  `Parser.parse/2` directly); the formatter path already handles `:edition_error`.
- Edition tagging is coherent across all three entry points
  (`compile_*`→`:edition_error`, `parse_source`→`:edition_error`,
  `Project.load`/`Edition.resolve`→raw `:unknown_edition`, each paired with its
  own matcher); a typo'd edition in the root manifest, a path dep, AND a git dep
  are all loud. `dep_project_dir`/`find_dep_root` iteration-6 escape re-verified
  closed. Multi-edition latent review (hypothetical `@known ["2026","2027"]`)
  found no off-by-one in `all/0`/`compare/2`/`retired_keywords/2`/keyword-set
  selection. `Edition.resolve` precedence + `|| ""` nil-coalesce sound.
- `cmd_compile` swallowing a `Project.load` edition error to `project = nil`
  (agent 3, minor) is harmless: the per-file `compile_file` re-resolves the same
  typo'd manifest and aborts loudly, so the build never completes with the wrong
  stdlib. Message-quality only, not a correctness bug.

**Full suite after all fixes: 3894 passed, 0 failing** (+3 new tests; 157 immune
responses expected; Antigen shape-coverage 309/309).

## Outstanding findings (after iteration 9)

- None open as bugs. The by-design/inert items above are recorded so a future
  audit doesn't re-flag them.

**Loop status:** iteration 9's fresh audit found 3 confirmed bugs — so it is **NOT
a clean audit**. Convergence (two consecutive clean audits) is **not** met
(iterations 6–9 all found bugs). The cron is **left in place**; the next fire
(iteration 10) runs a fresh audit over the iteration-9 changes. Do NOT merge.

Commits this cycle: `c0beb65` (git-URL + clone-status), `21f56be` (docstring).

---
