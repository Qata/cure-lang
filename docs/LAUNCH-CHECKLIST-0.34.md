# Cure 0.34 — Launch Checklist

**Status:** open
**Target version:** 0.34.0 (`mix.exs` currently pins `@version "0.33.1"`)

What 0.34 *is* lives in [`../ROADMAP-0.34.md`](../ROADMAP-0.34.md) — the feature
narrative for the dependent-pipeline release. This document is the complementary
list: the work that must be finished before the tag goes out. Roadmap answers
"what shipped"; this answers "what's blocking".

Items are grouped by kind, not priority. Anything marked **breaking** must land
before the tag, because it cannot land after one without a 0.35.

---

## 1. Surface changes that must land pre-tag

- [ ] **Rename the anonymous hole `??` → `?_`.** (breaking)
  - Lexer: `lib/cure/compiler/lexer.ex:734` (`lex_hole/1`). Today the `""`-name
    branch consumes a run of `?` and yields a hole named `"?"`. Note that `?_`
    *already* lexes as a hole named `_`, because `_` is an identifier byte in
    the name-consuming branch — so the new spelling parses before the change,
    which makes this a soft migration rather than a flag day.
  - Decide whether `??` becomes an error or a deprecation warning for one
    release. If deprecated, it needs a `Cure.Migrate` rule so
    `cure migrate --check` catches it.
  - Check the interaction with the predicate-name suffix (`is_empty?`,
    `lexer.ex:816`): the "trailing `?` only when the next byte can't start an
    identifier" rule is what keeps `is_empty?foo` from splitting. Confirm `?_`
    doesn't open a new ambiguity there, and add a lexer regression either way.
  - Docs to update: `LANGUAGE_SPEC.md:307`, `PROOFS.md:63`,
    `DEPENDENT_TYPES.md:109`, `TYPE_SYSTEM.md`. ~32 `??` occurrences across
    docs, `lib/`, and `test/`.
  - Confirm the auto-lemma demo spelling in
    `superpowers/specs/kernel/2026-07-18-auto-lemma-proof-search-design.md`,
    which writes a bare `?` for a proof-search hole — decide whether bare `?`
    stays valid alongside `?_`.

- [ ] Sweep for any other locked-surface spellings still in flux, so the whole
      breaking set lands in one tag. *(Fill in — I only verified the hole
      rename.)*

---

## 2. Documentation

- [x] **Write `docs/MACROS.md`.** Done — 14 sections covering the `macro`
      container and its members, rule grammar (dispatch keyword, holes,
      repetition, `is`/`open`, `where`, `contextual`), `literal`, `becomes`,
      `computed by`, `syntax family`/`accepts`/`expands with`, the `Std.Syntax`
      quoted-AST API, the self-proving obligations, scope/staging, termination
      and purity, diagnostics, and known sharp edges. Registered in `mix.exs`
      `extras` and the README doc list. Every ` ```cure ` fence in it is checked
      by `mix cure.check.docs`; one is tagged ` ```cure W000 ` because
      `lift_module` cannot emit a warning-free module. Grammar fragments — rule
      shapes, quoted-AST type excerpts, a deliberately non-parsing template —
      are ` ```text `, since they are not Cure source and there is no tag that
      opts a `cure` fence out of the gate. Diagnostic transcripts quoted in the
      doc were reproduced, not paraphrased.

      Written against the implementation rather than the specs, which corrected
      three points the design docs get wrong:
      - `explain` clauses use `=>`, not the `->` in
        `2026-07-08-macro-facility-design.md`.
      - Only `Name`, `ModuleName`, `Type`, `Parameters`, `Int`/`Float`/`Atom`/
        `Bool` and `Code` have dedicated matching behaviour in a `syntax` rule
        (`parser.ex:987-1039`). Every other hole kind — `Number`, `Expression`,
        `Statement`, `Pattern`, `Token` — falls through to the same
        `parse_expr` clause at `parser.ex:1087`, so those names are labels, not
        constraints. The richer shape vocabulary is only meaningful as a
        `syntax family` field shape.
      - Writing an `explain` block is what opts a macro into the *full*
        self-proving contract (exhaustive failure-point coverage **and** a
        mandatory worked example on every `syntax`/`computed` rule). Without it,
        examples are optional. This is the doc's main narrative and it is not
        stated in any one spec.

- [ ] **Expand `docs/PROOFS.md` to cover the new proof vocabulary.** It is 96
      lines and mentions the new constructs only in a five-bullet summary, while
      the authoritative design
      (`superpowers/specs/2026-07-21-proof-language-ergonomics-design.md`) is 786
      lines and marked *implemented*. Each of the ten features needs a worked,
      compiling example:
      `proof chain`/`because` · `have` · `rewrite using` ·
      `rewrite backwards using` (incl. `in <hypothesis>` and `at <n>`) ·
      `simplify` / `simplify using [rules]` / `simplify using <proof>` ·
      `induction` with `case C(field, ih) =>` · automatic congruence ·
      generated defining equations · dependent-pattern refinement and named
      implicit patterns · named arguments.
      Best existing exemplar to lift from:
      `lib/std/proof_linear_arithmetic_semantics.cure:45-150`.

- [ ] Document the proof diagnostics **E109–E114** and **E115** (named
      arguments) at the same level as the rest of the catalog — the design gates
      each feature on its diagnostics, so the docs should show them.

- [ ] Reconcile `docs/PROOFS.md` "Proof authoring surface" with
      `LANGUAGE_SPEC.md` §"Proof authoring" so the two don't drift.

- [ ] Finalise `CHANGELOG.md`: promote `[Unreleased]` to `[0.34.0]` with a date,
      and confirm the "Breaking changes" list in `ROADMAP-0.34.md` is fully
      mirrored there.

- [ ] Decide the fate of the root-level `AUTOPILOT-*.md` reports (10 files).
      They read as internal working notes; either fold their conclusions into
      the changelog/roadmap or move them out of the repo root before the tag.

---

## 3. Website (`site/`)

- [ ] **Finish the redesign.** Last touched by `7db54c80` ("Improve
      source-driven documentation and landing page"), which reworked
      `site/lib/cure_site_web/controllers/page_html/home.html.heex` and
      `components/layouts.ex`. *(Fill in the remaining scope — I couldn't infer
      what "done" means for the redesign from the repo alone.)*

- [ ] Make sure the source-driven stdlib docs pipeline covers the 0.34 surface.
      `stdlib_controller.ex` renders from `lib/std/*.cure` docstrings, and
      `test/cure/doc/stdlib_source_docs_test.exs` gates it — verify the new
      proof modules (`Std.Proof.LinearArithmetic`, `Std.Decision`,
      `Std.Equivalent`) render correctly.

- [ ] Landing page should reflect 0.34's actual pitch (one dependent pipeline,
      Idris parity) rather than the 0.33 framing.

- [ ] Check `llms_controller.ex` / `sitemap_controller.ex` output includes the
      new docs (`MACROS.md`, expanded `PROOFS.md`) once written.

---

## 4. Known bugs blocking advertised features

- [ ] **Generated defining equations crash the compiler when applied (E101).**
      `f.Ctor` resolves and reports a correct Pi type, but applying it panics.
      Minimal reproduction:

      ```cure
      mod Probe3
        use Std.Equivalent
        type Nat3 = Z3 | S3(Nat3)
        fn add3(x: Nat3, y: Nat3) -> Nat3 = match x
          Z3()  -> y
          S3(k) -> S3(add3(k, y))
        fn add3_succ_eq(k: Nat3, y: Nat3) -> Equivalent(Nat3, add3(S3(k), y), S3(add3(k, y))) = add3.S3(k, y)
      end
      ```

      → `INTERNAL COMPILER ERROR [E101]`, fingerprint `b0471f7fba6c`. A nested
      case (`isbst.Node(l, v, r)` over a recursive tree predicate) gives
      fingerprint `1426dd796cde`. This is item §4.8 of the proof-ergonomics
      design and acceptance criterion 5, so it can't ship broken — either fix it
      or drop the claim from the release notes.

- [ ] Audit the rest of the proof-ergonomics acceptance criteria (§11 of the
      design, 12 items) against reality — the `f.Ctor` breakage suggests the
      "implemented" status wasn't re-verified end-to-end after later merges.

- [ ] **A bad `lift_module` name surfaces as E101 at `compile`, and `check`
      passes.** `lift_module.ex:395` requires
      `^Cure\.[A-Z][A-Za-z0-9_]*(\.[A-Z][A-Za-z0-9_]*)*$`. A macro that lifts
      `Books` or `Demo.Books` instead reaches codegen and dies as
      `CODE GENERATION FAILED [E101] … invalid_module_name` — fingerprints
      `9da0ba28c6fe` and `625ce9c9d39b`. By E101's own catalog rule ("ordinary
      source errors must never use E101") this is a defect twice over: it is a
      name-convention violation with a knowable fix, and `cure check` reports
      OK on the same file. It needs a real diagnostic, raised at check time,
      naming the required prefix. Found while writing `docs/MACROS.md`; recorded
      there as a sharp edge (§13) so users aren't stranded meanwhile.

- [ ] **`<fresh …>` in a lambda parameter position crashes the parser.**
      A `becomes` template of the form `(fn(<fresh tmp>) -> <fresh tmp>)(n)`
      raises an uncaught `CaseClauseError` in
      `Cure.Compiler.Parser.parse_explicit_param/1` (`parser.ex:8703`) — a raw
      Elixir exception, not a diagnostic. Either support the position or reject
      it with a proper error; a crash in the documented hygiene escape hatch is
      a bad look for a flagship feature.

- [x] **`cure.check.docs`'s own tests never ran — the fixture had no artifact
      set.** Fixed. The fixture in `test/mix/tasks/cure.check.docs_test.exs` is
      a bare temporary directory; the task resolves `stdlib_ebin` as
      `_build/cure/ebin` relative to that root, found nothing, and
      `Cure.Compiler.Artifacts` rejected every compile with `E100 INVALID BUILD
      ARTIFACT` before any snippet was judged. All eleven tests failed for a
      reason none of them was testing. The setup now symlinks the project's own
      compiled stdlib into the fixture root; the file is green.

      (If `mix compile` aborts with `(UndefinedFunctionError) function
      Cure.Compiler.Artifacts.Writer.transact/2 is undefined` via
      `cure.compile_stdlib.ex:57`, the seven files under
      `lib/cure/compiler/artifacts*` are missing from the working tree. They
      are tracked — `git checkout HEAD -- lib/cure/compiler/artifacts.ex
      lib/cure/compiler/artifacts/` restores them.)

- [ ] **The repository-wide doc gate has a large backlog.** With the gate
      actually running, `mix cure.check.docs` reports **256 passed, 205 failed**
      across the tree. `docs/MACROS.md` and `docs/PROOFS.md` are clean; the
      failures are older documents — `docs/LANGUAGE_SPEC.md` (36),
      `site/priv/pages/language-guide.md` (31),
      `site/priv/pages/finite-state-machines.md` (24) and `docs/GLOSSARY.md`
      (19) are the worst — carrying pre-`0.34` syntax. Each one is either a
      snippet to fix or a sketch to re-fence as ` ```text `; deciding which,
      per fence, is the work. Triage before the gate can be made blocking.

---

## 5. Warning diagnostics reach parity with errors

Warnings currently render as a bare title and message — no file, no quoted
source, no carets — while errors get the full treatment (heading with path,
`at path:line:col`, quoted source lines, `^^^^` primary and `----` secondary
labels). Compare the two from a single stdlib build:

```
-- MIGRATION WARNING [W001] ----------------------------------------------------

uppercase type variable will be lowercased
```

```
-- PROOF DOES NOT JUSTIFY CHAIN STEP 1 [E110] -- /path/to/probe.cure

The evidence after `because` does not prove the equality required by step 1.

at /path/to/probe.cure:41:17
40 |         add2(S2(k), y) == S2(add2(y, k))
   >                        -----------------
41 |         because rewrite using ih
   > -------------------------------- step 1 requires this equality
   >                 ^^^^^^^^^^^^^^^^ this evidence proves a different proposition
```

- [ ] **Give warnings a primary `Label` with a real `Span`.** This is the
      actual blocker, and it is upstream of the renderer.
      `Cure.Diagnostic.Renderer.evidence_doc/3` already draws the snippet for
      *any* diagnostic that has both a `%SourceRegistry{}` and a `primary`
      `%Label{span: %Span{}}`; with no primary label it silently falls back to
      `location_doc/2`. But `Adapter.Operational.migration_warning/1`
      (`lib/cure/diagnostic/adapter/operational.ex:163`) builds its diagnostic
      with **no primary label at all** — just `payload: %{rule:, file:, line:,
      source_location: :line}`. So warnings can never draw carets, regardless of
      renderer changes. (`source_location: :line` is dead weight: that key is
      written in this one place and read nowhere in the codebase.)

- [ ] **Widen the migrate-rule contract from lines to spans.** The reason
      `migration_warning/1` only has a line is that
      `Cure.Migrate.Rule.detect_and_rewrite` returns `{:rewrite, new_ast}`,
      `{:rewrite, new_ast, lines}`, or `{:warn, lines}` — line numbers only,
      never columns or ranges. Getting carets means threading spans through that
      return shape and updating all six rules in `lib/cure/migrate/rules/`
      (`uppercase_type_var`, `if_elif_to_pickup`, `proto_to_interface`,
      `module_rename`, `removed_module`, `group_hoist`). This is the bulk of the
      work; the rendering side is close to free once spans exist.

- [ ] **Show the post-migration preview.** Cheaper than it looks: in
      warn-and-tolerate mode `cure build` *already computes* the rewritten AST
      (`{:rewrite, new_ast, …}`) and then discards it. Feed that through the
      canonical printer already backing `cure fmt` / `cure migrate --print` and
      attach it as a `Suggestion`/`TextEdit` — both structs already exist in the
      diagnostic and already flow through the terminal, JSON, and LSP
      projections, so a preview also becomes an LSP code action for free.

- [ ] **Respect `tier` in how the preview is worded.** `Rule.tier` is the
      warn/rewrite/normalize authority and must not be flattened:
      `:machine` is certified semantics-preserving (safe to phrase as "will
      become" and to offer as an auto-fix); `:review` warns only and must not be
      auto-normalized by `cure build` (phrase as advisory); `:manual` has no
      auto-migration at all, so it must say the port is by hand rather than show
      a fake preview.

- [ ] **Cover the whole warning family, not just W001.** `W000`
      (`compiler_warning`) has the same file/line-without-span shape, and `W002`
      (`configuration_warning`) / `W003` (`destructive_format_warning`) carry no
      location whatsoever. Decide per code whether a span is meaningful —
      `W002` is config-level and may legitimately have none — rather than
      forcing a span everywhere.

- [ ] Add terminal (plain + ANSI), JSON, and LSP snapshots for warnings at the
      catalog widths, matching what §7 of the proof-ergonomics design already
      requires of errors. Warnings currently have no such fixtures.

- [ ] Fix the emission point that interleaves W001 with Mix's progress output
      (`uppercase type variable will be lowercased` printed mid-build, directly
      above `74 compiled, 0 up-to-date, 0 removed`) — warnings should flush as
      whole blocks like errors do.

---

## 6. The REPL still works after everything we changed

Verified by running `mix cure.repl` against the current tree. Basic evaluation
is fine (`1 + 1` → `2`, `type Nat3 = ...` → `defined type Nat3`), but **no
multi-line definition survives the input loop**, which means none of the new
proof vocabulary is reachable from the REPL at all.

- [ ] **Teach `incomplete?/2` about indentation-structured blocks.** This is the
      blocker everything else in this section sits behind.
      `Cure.Repl.classify_input/1` (`lib/cure/repl.ex:1491`) only continues when
      a line *ends with* `do -> = | then else , (`, and
      `lone_opening_keyword?/1` (`:1513`) only fires for a line that is exactly
      one word from `@opening_keywords` (`:1511` — `match if case cond try fn do
      let mod rec type proto impl proof actor fsm`). The two AST-based
      fallbacks don't save it: `parse_indicates_continuation?/1` needs an
      EOF/dedent-rooted parse error, and `ast_is_open_block?/1` only recognises
      a *top-level* stub like a bare `match` with no arms. So this submits early:

      ```
      cure(1)> fn add3(x: Nat3, y: Nat3) -> Nat3 = match x
      -- PATTERN MATCH IS MISSING `Z3` [E118] --
      cure(2)>   Z3()  -> y
      -- I GOT STUCK WHILE PARSING THIS [E094] --
      ```

      The buffer `fn ... = match x` parses as a *complete* function, so the
      indented arms that follow are each submitted as their own top-level input.
      `;;` doesn't help — the buffer is already gone by the time you type it.
      The fix is a real indentation check (a line indented deeper than the
      submission's first line continues it), not more suffix cases.
- [ ] **Blank lines must not force-submit inside a block.** `proof chain`
      separates its steps with blank lines (see
      `lib/std/proof_linear_arithmetic_semantics.cure:45-150`), but the REPL
      treats a blank line as an unconditional submit — the documented behaviour
      in `docs/REPL.md:74`. Under the current rules a chain can never be typed
      in. Blank lines should only submit when the buffer is at indent level 0.
- [ ] **Add the new proof keywords as continuation cues** once the indentation
      rule is in: `induction`, `have`, `because`, `rewrite`, `simplify`, and the
      two-word `proof chain` (`lone_opening_keyword?/1` requires a *single*
      token, so `proof chain` doesn't match today even though `proof` alone
      does). `case C(field, ih) =>` arms need the same treatment `->` arms get.
- [ ] **Make `:holes` actually work — it is currently dead code.**
      `state.holes` is initialised to `[]` at `lib/cure/repl.ex:55` and `:742`
      and **never assigned anywhere**, so `:holes` always prints
      `(no holes recorded)` (`:760-766`). The data it wants already exists:
      `Cure.Elab.Program.hole_goals/1` (`lib/cure/elab/program.ex:1862`) returns
      `[%{function:, goal:, context:}]`, exactly the `{label, goal, ctx}` shape
      the renderer expects. Two things to bridge: the REPL compiles with
      `emit_events: false` (`:663`, `:780`, `:856`, `:1222`), and nothing
      threads the elaborated env back out of `compile_and_load/2`.
      A hole in a REPL expression currently reports `E014 HOLE NEEDS A TYPE
      ANNOTATION` because the synthesized wrapper is `fn main() =` with no
      declared result type — consider giving the wrapper an inferred or
      `Any` return so `??` reports a goal instead of an error. Interacts with
      the `?_` rename in §1.
- [ ] **REPL diagnostics quote an empty line and point the caret at nothing.**
      Every error above rendered as `at nofile:3:7` / `3 | ` with a bare caret —
      the span is in the *synthesized wrapper module* (`mod Repl.M<n>` built in
      `evaluate/2`, `:657-661`), and the REPL registers no `%SourceRegistry{}`
      for it, so `Renderer.evidence_doc/3` has coordinates but no text. Register
      the wrapper source and offset spans back to the user's input line/column,
      or the carets work from §5 will land in the REPL as blank output.
- [ ] **Check session-def inlining survives proof definitions.**
      `inline_session_defs/2` (`:686`) re-emits every prior definition as an
      indented local function of each new eval module, with the comment at
      `:648-654` explaining that cross-module `use` can't recover function
      *types* from a loaded BEAM. Confirm this still holds for `@lemma`-decorated
      theorems (does the lemma registry survive re-inlining, and does it
      register N times after N inputs?), for `@erased`/`@linear`/`@affine`
      decorators, and for generated defining equations (`f.Ctor`) — which
      currently crash the compiler outright, see §4.
- [ ] **Version banner.** The REPL prints `Cure REPL v0.33.1`; covered by the
      `mix.exs` bump in §7 but worth confirming it reads the bumped version.
- [ ] **First launch pays a silent multi-minute stdlib build.** A cold
      `mix cure.repl` took ~6 minutes here (74-module stdlib compile + 7.5 MB
      escript) behind a single `Compiling Cure standard library (74 modules)`
      line, and emits the §5 `W001` warning mid-build. Warm launch is ~9 s.
      Either show progress or pre-build in the release artifact.
- [ ] **Add eval-path test coverage.** `test/cure/repl/` has eleven files
      (completer, config, docs, highlight, history, line_editor, markdown,
      options, render, session, terminal) and **none** covers `incomplete?/2`
      against real multi-line source or the evaluate/compile path. Add cases
      for a multi-clause `fn`, an `induction` block, a blank-line-separated
      `proof chain`, and a hole reporting through `:holes`.
- [ ] Update `docs/REPL.md` once the above lands — its `;;` (`:74`) and
      `:holes` (`:95`) entries both describe behaviour that doesn't match the
      tree, and it says nothing about proof syntax.

---

## 7. Release mechanics

- [ ] Bump `@version` in `mix.exs` to `0.34.0` (also drives `source_ref:
      "v#{@version}"` for docs links).
- [ ] `cure migrate` rule coverage for every 0.34 rename, with
      `cure migrate --check` clean over `lib/std/` and `examples/`.
- [ ] Full gate pass: suite, canonical stdlib compilation, TCB/termination
      checks, Antigen, Dialyzer, `mix cure.diagnostics --coverage`.
- [ ] `mix cure.compile` clean on the downstream consumers — at minimum the
      `cure-otp` package (`lib/` + `metatheory/src`, 59 proof modules) and the
      `esp32-beam` phase dirs on generic-unix AtomVM.
- [ ] Resolve the `W001` migration warning ("uppercase type variable will be
      lowercased") currently emitted during stdlib compilation — a clean build
      shouldn't warn on its own stdlib. Distinct from §5, which is about how
      that warning *renders*; this is about the stdlib source still tripping it.
- [ ] Tag, and check `RELEASE.md` steps are still accurate.

---

## Notes

- The `?_` rename, the E101 bug, the doc gaps in §2, and every §6 REPL finding
  were verified against the tree at the time of writing — the REPL items come
  from actually running `mix cure.repl`, not from reading it. Items marked
  *(Fill in)* are placeholders where I had no evidence to draw on.
- Downstream consumers of the new proof vocabulary should not start migrating
  until §1 is settled, or they'll migrate twice.

### REPL verification — what was actually run

Evidence behind §6, recorded so the next person doesn't have to re-derive it.

**Headline: the REPL cannot accept any multi-line definition, so none of the
0.34 proof vocabulary is reachable from it at all.** Every new proof form
(`induction` + `case … =>`, `proof chain`, indented `because`) is multi-line by
construction.

Basic evaluation is healthy — `1 + 1` → `2`, `type Nat3 = Z3 | S3(Nat3)` →
`defined type Nat3`. The failure starts the moment a definition spans lines:

```
cure(1)> fn add3(x: Nat3, y: Nat3) -> Nat3 = match x
-- PATTERN MATCH IS MISSING `Z3` [E118] --------------------- repl/session
This match can receive `Z3`, but no branch handles that constructor.
cure(2)>   Z3()  -> y
-- I GOT STUCK WHILE PARSING THIS [E094] ------------------------- nofile
'->' cannot appear at this point in the construct.
cure(3)>   S3(k) -> S3(add3(k, y))
-- I GOT STUCK WHILE PARSING THIS [E094] ------------------------- nofile
```

Root-cause chain, all in `lib/cure/repl.ex`:

1. `incomplete?/2` (`:1562`) is the whole decision. It ORs four signals:
   `classify_input/1`, bracket balance, `parse_indicates_continuation?/1`,
   `ast_is_open_block?/1`.
2. `classify_input/1` (`:1491`) only continues on a line *ending with*
   `do -> = | then else , (`, or a lone `@opening_keywords` word (`:1511`:
   `match if case cond try fn do let mod rec type proto impl proof actor fsm`).
   `… = match x` ends in `x`. No match.
3. `parse_indicates_continuation?/1` (`:1569`) needs a parse error rooted at
   `:eof` / `:dedent` / `:newline`. But `fn add3(…) -> Nat3 = match x` is a
   *syntactically complete* function — it parses. No error, no continuation.
4. `ast_is_open_block?/1` (`:1601`) only recognises a **top-level** stub, e.g. a
   bare `match` with no arms. Here the top-level node is a function definition,
   so `open_ast?` never sees the empty match nested inside it. No match.

Result: submit. The indented arms that follow are each parsed as their own
top-level input, hence the `E094`s. `;;` cannot rescue this — by the time you
type it the buffer has already been submitted and cleared. Verified with an
explicit `;;`-terminated multi-line `fn`; it failed identically, and the
follow-up call then failed with `E091 UNKNOWN VALUE` because the definition was
never registered.

So the fix has to be a real indentation rule (a line indented deeper than the
submission's first line continues it), not more suffix cases in
`classify_input/1`. Adding proof keywords to `@opening_keywords` is necessary
but nowhere near sufficient — and note `proof chain` is two words while
`lone_opening_keyword?/1` (`:1513`) requires a single token, so `proof chain`
does not trigger continuation today even though bare `proof` does.

Compounding it: `proof chain` separates its steps with **blank lines** (see
`lib/std/proof_linear_arithmetic_semantics.cure:45-150`), and a blank line is an
unconditional submit — the documented behaviour at `docs/REPL.md:74`. Even after
the indentation fix, chains stay untypeable until blank-line submit is scoped to
indent level 0.

**`:holes` is dead code.** `state.holes` is initialised to `[]` at `:55` and
`:742` and is never assigned anywhere in the file, so `:holes` unconditionally
prints `(no holes recorded)` (`:760-766`). The data already exists —
`Cure.Elab.Program.hole_goals/1` (`lib/cure/elab/program.ex:1862`) returns
`[%{function:, goal:, context:}]`, which is exactly the `{label, goal, ctx}`
shape the renderer at `:766` destructures. Two gaps to bridge: the REPL compiles
with `emit_events: false` at all four call sites (`:663`, `:780`, `:856`,
`:1222`), and nothing threads the elaborated env back out of
`Cure.Compiler.compile_and_load/2`. Separately, a bare `??` errors with
`E014 HOLE NEEDS A TYPE ANNOTATION` because the synthesized wrapper is
`fn main() =` with no declared result type (`evaluate/2`, `:657-661`).

**REPL diagnostics quote an empty line and point the caret at nothing.** Every
error above rendered as `at nofile:3:7`, then `3 | ` with no source text, then a
bare `^`. The spans are coordinates in the synthesized `mod Repl.M<n>` wrapper,
and the REPL registers no `%SourceRegistry{}` for it — so
`Renderer.evidence_doc/3` has a span but no text to underline. This directly
undercuts §5: the caret work will land as blank output in the REPL unless the
wrapper source is registered and spans are offset back to the user's input
line/column.

Incidental observations from the same session:

- Cold `mix cure.repl` took **~6 minutes** (74-module stdlib compile + a 7.5 MB
  escript build) behind the single line `Compiling Cure standard library
  (74 modules)`, and emitted the §5 `W001` warning mid-build. Warm launch is
  ~9 s.
- Banner reads `Cure REPL v0.33.1` — will follow the `mix.exs` bump in §7, but
  confirm it reads the bumped value rather than a hardcoded string.
- `test/cure/repl/` holds eleven test files (completer, config, docs, highlight,
  history, line_editor, markdown, options, render, session, terminal) and none
  of them exercises `incomplete?/2` against real multi-line source or the
  evaluate/compile path — which is why this regressed unnoticed.
- `lib/cure/repl.ex` was last touched 2026-07-21 (`1b600962 fix(diagnostics):
  locate macro use mismatches`), i.e. the diagnostics work reached it but the
  proof-ergonomics work did not.
