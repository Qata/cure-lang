# Migration Facility + `cure migrate` — Implementation Design (Approach A)

> **STATUS: IMPLEMENTATION-READY.** Supersedes the parked design capture
> [`2026-07-09-migration-facility-design.md`](2026-07-09-migration-facility-design.md),
> which explicitly deferred the lossless-model fork to a pre-implementation
> brainstorm. That brainstorm is complete (2026-07-10); this document records
> the resolved decisions and is the source of truth for the plan.
>
> **Branch:** `feature/migration-facility`, based on `autopilot/kernel-parity-batch`.

## 1. Goal

A general, extensible **source-migration facility** for Cure: a registry of
migration rules that (a) during normal `cure build` emit deprecation
**warnings** and tolerate the legacy form in-memory, and (b) via a new
`cure migrate` command, **rewrite source files in place** to the canonical
form — **losslessly**, preserving every comment. Warn-now → error-later.

The uppercase-type-var → lowercase rule is the first *new* client; the existing
`if`/`elif` → `pickup` rewrite (today in `mix cure.rewrite`) is the first
*existing* client to fold into the registry.

## 2. Operator-decided constraints (locked, not open)

1. **Migration MUST be lossless** — no lossy-but-warned v0. Every comment
   survives a rewrite.
2. **One rule registry, two consumers.** The set of rules `cure migrate`
   applies is EXACTLY the set the compiler warns on.
3. **`--strict` promotes migration warnings to errors** (the warn-now→error-later
   knob).
4. **Approach A — whole-file canonical reprint.** `cure migrate` reprints the
   entire file in canonical form (gofmt/elm-format style), carrying comments and
   blank-lines as trivia. It is *also* the engine behind `cure fmt`. (Chosen over
   the minimal-diff/surgical-splice alternative — see §4.)
5. **Keep the hand-rolled Pratt parser.** No NimbleParsec rewrite (see §4.2).
6. **`cure migrate` refuses to run unless targets are git-tracked and the tree
   is clean** (read-only modes exempt).

## 3. Empirical grounding (measured 2026-07-10, this worktree)

The fork was decided on measured round-trip fidelity, not inference. On a
comment-heavy corpus, `lex(preserve_comments) → parse → Printer.quoted_to_string`:

| File | `#`-comment lines in → out | Output reparses? |
|---|---|---|
| `lib/std/access.cure` | 142 → **11** | yes |
| `lib/std/core.cure` | 111 → **9** | yes |
| `lib/std/iter.cure` | 108 → **4** | yes |
| `examples/cure_moneta/.../moneta.cure` | 110 → 49 | yes |
| `examples/match_showcase.cure` | 83 → 81 | **no** |

Two root causes, both confirmed by direct probe:

- **Bug 1 — the Printer is non-total over the AST.** `match_showcase` output
  line 127 was a raw `inspect`-ed tuple
  `{:pin, [line: 205, col: 7], [{:variable, …, "target"}]} -> true` — the Printer
  has **no clause for the `:pin` pattern node**, so it fell through to `inspect`,
  which does not reparse. Whole-file reprint (Approach A) requires the Printer to
  handle *every* node the parser can emit.
- **Bug 2 — comment capture is positional and partial.** The parser only turns
  `:line_comment` tokens into `{:comment, meta, text}` nodes at a few
  statement-list boundaries it explicitly scans. `access.cure` has 142 full-line
  comments, **0 trailing**, yet only 11 survived — the rest live *inside*
  constructs (type bodies, between fields, mid-clause) where no comment
  collection runs, so they are dropped. Losslessness requires trivia capture that
  is independent of AST position.

## 4. Design decision: Approach A over minimal-diff

### 4.1 Why whole-file canonical reprint (A), not surgical splice (B)

The minimal-diff alternative (recast/rust-analyzer style: keep original bytes,
reprint only changed subtrees) is lossless "for free" outside changed regions,
but it makes `cure migrate` a migrator only — never a canonical formatter. The
operator chose A: migration also canonicalizes formatting, and the same engine
powers `cure fmt`. A's cost is that the Printer must become total and the trivia
model must be complete; both are addressed below and are one-time costs that also
retire the standing Printer/`cure fmt` fidelity debt.

### 4.2 Why keep the Pratt parser (no NimbleParsec)

Measured: `parser.ex` is 4,537 non-blank lines (≈3,663 code + 874 comment) plus
a 117-line precedence table, atop a 1,393-line indentation-aware lexer. A
NimbleParsec rewrite would be a wash-to-larger on LOC and would fight this
project's goal:

- **Operator precedence** lives in a compact 117-line Pratt table; NimbleParsec
  has no precedence mechanism and would re-encode it as a longer rule tower.
- **Indentation** is solved in the lexer (indent/dedent tokens); NimbleParsec is
  context-free PEG and bad at the offside rule — the lexer stays either way.
- **Backtracking + recovery** (31 sites: record-update rewind probe,
  `synchronize_to_statement`) give good diagnostics NimbleParsec cannot match.
- **Lossless trivia** cuts against NimbleParsec's `ignore()`-the-whitespace
  idiom; the Pratt parser already visits every token positionally, which is
  exactly what trivia attachment needs.

The AST is Metastatic 3-tuples `{type, meta, children_or_value}` where `meta` is
a keyword list already carrying `line`/`col`/`subtype`. Trivia goes in `meta`
under new keys with **no tuple-shape change and no impact on any consumer that
ignores `meta`.**

## 5. Architecture

### 5.1 Pipeline

```
cure migrate:  source → lex(lossless) → parse → attach-trivia → migration-rewrite
                       → canonical Printer(trivia-aware) → git-guard → write
cure build:    source → lex(lossless) → parse → attach-trivia → migration-rewrite(warn-only)
                       → … normal elaboration/codegen …
cure fmt:      source → lex(lossless) → parse → attach-trivia
                       → canonical Printer(trivia-aware) → write
```

The migration-rewrite pass sits **between the parser and the elaborator** and
does NOT type-check. Rules needing name context consult a light declared+imported
**type-name set** built from the AST (far short of elaboration).

### 5.2 Trivia model (the core)

Modeled on Go's `go/printer`/`ast.CommentMap`: comments and blank-lines are
**trivia owned by AST nodes**, populated by a single post-parse attachment pass.

- **Lexer (lossless mode):** collect every comment and blank-run as a *positioned
  trivia item*: `{:comment, text, line, col}`, `{:doc_comment, text, line, col}`,
  `{:blank, count, line}`. (Reuses the existing `preserve_comments` lexer path;
  the new requirement is that nothing is emitted into the significant-token stream
  for the parser to special-case — trivia is collected to a side list keyed by
  position.)
- **`Cure.Compiler.Trivia` (new module):** a single pass over `(tokens, ast)`
  that attaches each trivia item to exactly one owning node as `meta[:leading]`
  (items whose source position precedes the node and are not same-line-trailing
  on a prior node) or `meta[:trailing]` (a comment on the same line, after the
  node's last token). Items after the last node land in a **file-level trailer
  bucket** on the program node. The pass is **total by construction**: it asserts
  every collected trivia item is placed exactly once (an unplaced item is a hard
  error, not a silent drop — this is the anti-Bug-2 invariant).
- **Attachment on nodes, not a line-keyed side map:** migration rules
  *restructure* subtrees (`if/elif`→`pickup`). Trivia attached to a node
  **travels with the node** through a rewrite; a pure line-keyed map would
  detach. Restructuring rules get a registry helper (`Trivia.carry/2`) to move
  attached trivia onto the surviving/replacement node.

### 5.3 Printer totality

- Make `Cure.Compiler.Printer` **total** over the AST: add the missing `:pin`
  clause and any siblings surfaced by the totality gate. No node kind may fall
  through to `inspect`.
- Teach the Printer to emit trivia: `meta[:leading]` before a node (each on its
  own line at the node's indent), `meta[:trailing]` as an end-of-line `# …`,
  and the program trailer bucket at EOF.
- **Totality gate (test):** for the whole in-repo `.cure` corpus,
  `parse → print` (a) never emits a string containing an `inspect`-shaped tuple
  literal, and (b) reparses; and `parse→print→reparse→print` is a byte-fixpoint.

### 5.4 Blank-line normalization (fully opinionated, elm-format style)

1. **Top of file:** 0 blank lines — strip all leading blanks.
2. **Bottom of file:** exactly 1 blank line — inject if absent, collapse if
   multiple. (Byte form: content ends with the terminating newline followed by a
   single empty line.)
3. **Between top-level definitions:** exactly 1 blank line — inject if missing,
   collapse if multiple.
4. **Inside a block body:** cap runs at 1; trim blank lines immediately adjacent
   to a block's open/close; otherwise preserve the author's 0-or-1.

### 5.5 Rule registry (the anti-ad-hoc ask)

A rule is a struct:

```
%Cure.Migrate.Rule{
  id:                atom(),        # the W-code, e.g. :W087
  description:       String.t(),
  phase:             :syntactic | :needs_resolution,
  detect_and_rewrite: (ast, ctx -> {:rewrite, ast} | :no_change),
  warning_template:  String.t()     # rendered with match context
}
```

- **`ctx`** carries the declared+imported type-name set for `:needs_resolution`
  rules; `:syntactic` rules ignore it.
- **Two consumers, one registry:**
  - `cure build` runs each rule in **warn-and-tolerate** mode: apply the rewrite
    in-memory (so compilation proceeds on the canonical form) and emit the
    W-warning; never touch the file.
  - `cure migrate` runs each rule in **rewrite-and-write** mode.
- **Seed rules:**
  - `if`/`elif` → `pickup` (`:syntactic`) — fold in the existing
    `cure.rewrite` logic unchanged; it already produces `{:pickup, …}` from
    `{:conditional, …}` chains with a populated `else`.
  - uppercase-type-var → lowercase (`:needs_resolution`) — detect a *free*
    (would-be-auto-generalized) uppercase identifier in a type-parameter position
    that does NOT resolve to a known type constructor; lowercase the binder
    consistently across the signature; on a `T`+`t` collision, freshen and warn —
    **never silently merge.**

### 5.6 `cure migrate` CLI + policy

- New subcommand beside `cure fmt` in `cli.ex`, mirroring `cure.rewrite`
  ergonomics: **in-place by default**, `--check` (CI; lists pending files,
  non-zero exit), `--print` (stdout, no write).
- **Warn-now → error-later:** `--strict` promotes every migration W-warning to an
  error. Per-rule maturity (a rule graduating warn→error independently of a global
  switch) is **out of scope for v1** — one global `--strict` switch; per-rule
  maturity is a documented future extension.

### 5.7 Git-safety guard

- Before any write, `cure migrate` verifies, for each target file: it is
  **git-tracked** AND has **no uncommitted changes** (clean in `git status`).
- If any target fails, abort the whole run with a message instructing the user to
  commit or stash first. `--check` and `--print` (read-only) are exempt.
- Implementation: shell out to `git` (`git ls-files --error-unmatch`,
  `git status --porcelain`) with a clear non-git-repo error.

## 6. Build order (phases)

1. **Printer totality** — add missing node clauses (`:pin`, …); land the totality
   gate. Independent, immediately valuable (fixes `cure fmt`/`cure.rewrite`
   reparse breakage).
2. **Trivia model** — lossless lexer collection + `Cure.Compiler.Trivia`
   attachment pass + trivia-aware Printer + blank-line policy; land the lossless
   round-trip gate.
3. **Rule registry** — `Cure.Migrate.Rule` + registry; port `if/elif→pickup` and
   uppercase-type-var→lowercase; wire the `cure build` warn-and-tolerate consumer.
4. **`cure migrate` CLI + policy + git guard** — subcommand, `--check`/`--print`/
   `--strict`, git-safety guard.

Each phase ends green on the full suite; phases 1–2 are prerequisites for a
faithful whole-file reprint and must not be skipped.

## 7. Testing strategy (gates)

- **Printer-totality gate** (§5.3): corpus parse→print never inspects a tuple and
  always reparses; print is a fixpoint.
- **Lossless round-trip gate** (§5.2): corpus `lex→parse→attach→print` preserves
  every comment (count, text, attachment order) and reparses. This is the
  operator's "lossless" acceptance criterion, mechanized.
- **Trivia attachment totality:** the attachment pass errors (not drops) on any
  unplaced trivia item; a unit test asserts this on a constructed input.
- **Rule tests:** each seed rule has red-green cases — legacy form in →
  canonical out, comments preserved across a *restructuring* rewrite
  (`if/elif→pickup` with comments on the branches), and the `T`+`t` collision
  freshen-and-warn case.
- **`cure migrate` CLI tests:** in-place, `--check` exit code, `--print`,
  `--strict` error promotion, and the git-guard refusal (dirty tree / untracked
  file) via a temporary git repo fixture.
- **Warn-and-tolerate parity:** a rule warns under `cure build` on exactly the
  inputs `cure migrate` rewrites (one registry, two consumers — asserted).

## 8. Out of scope (v1)

- Per-rule warn→error maturity levels (one global `--strict` for now).
- Any new migration rules beyond the two seeds.
- A full concrete-syntax-tree replacing the AST (the trivia-on-`meta` model is
  sufficient for lossless reprint; a CST is not needed and not built).
- Migrating the kernel/elaborator or the classic-pipeline rip-out (unrelated;
  tracked elsewhere).
