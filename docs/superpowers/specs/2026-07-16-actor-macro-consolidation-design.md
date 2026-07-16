# Actor-macro consolidation — one templated expander, three tiers

**Status:** design approved, implementation pending.
**Scope:** `lib/std/actor.cure` first (reference implementation), then `fsm`/`supervisor`/`app`, then a deferred Tier‑3 typed layer.
**Layer:** P (parser, for the optional whole‑module `quote` step and, if 1e adopts mechanism (a), the family keyword‑alias capability) + stdlib Cure (`lib/std/*.cure`). **TCB delta: zero** — no change to `lib/cure/core/*`.

## 1. Motivation

`Std.Actor` grew three redundant expansion backends as the macro facility matured toward quasiquotation:

- **Gen A** — 16 positional `becomes lift module name` templates (`actor X state T messages M handle_cast …`), each re‑spelling all six GenServer callbacks inline just to vary one.
- **Gen B** — the `derive` shorthand (`… derive <cast_body> (call <call_body>)? computed by derive_actor`), whose expander `derive_actor` calls the thin wrappers `emit_actor`/`emit_actor_call`.
- **Gen C** — the structured surface (`macro actor` + `syntax family ActorDefinition` + `expands with derive_actor_family`).

All three funnel into one backend pair, `emit_actor_parts`/`emit_actor_call_parts`. Gen C is a strict output‑superset of Gen B: the wrappers `emit_actor`/`emit_actor_call` merely pre‑fill the same defaults (`default_actor_init`, the `ActorMessage` enum, `Raw(SOpaque)` bodies) that `derive_actor_family` computes richly from optional family fields.

Two problems follow. First, **duplication**: three surfaces, three expander entry points, ~200 lines of repeated GenServer skeletons. Second, **inelegance**: the surviving backend is hand‑assembled AST — `gen_server_module(module_name, state_type, [function("init", [parameter(...)], init_type, body), …])` and raw surgery like `Node(:match_arm, values, [block([let_binding("answered", call("Std.Otp.reply", [...])), tuple([...])])])`. `quote` appears only at the leaves. The expander reads like AST plumbing, not like the code it emits — the opposite of the Template‑Haskell / Lean ergonomics we are targeting ("as much user friendliness as possible… in line with meta‑languages people actually like using").

The goal: **one expander over one backend, written as quasiquote templates**, reached by a terse Tier‑1 shorthand and a structured Tier‑2 family, with a typed Tier‑3 layer added last.

## 2. Background: `computed by` vs `expands with`

Both reach the same runtime contract — *call an elaborator function with a record, get `Syntax` back* — which is why the three generations can be folded into one.

- **`computed by <fn>`** (`kind: :computed`, `parser.ex` ~6466) is the low‑level primitive: a positional `syntax <pattern>` whose holes are captured into an auto‑generated record; at expansion the compiler calls `<fn>(record) -> Syntax`.
- **`expands with <fn>`** (`kind: :expands_with`) is the structured surface built on top. A named `syntax family` (typed fields, `optional` markers, keyword labels, composable via `includes`) + `accepts` + `expands with <fn>` is **lowered into a `:computed` rule** by `MacroFamily.computed_rule/2` (`lib/cure/compiler/macro_family.ex`:34‑97): it generates the `<Family>Syntax` record, packs the leading holes plus a `definition` record as the elab inputs, and sets `elab: <fn>`.

`expands with` is therefore `computed by` plus a generated, typed, optional‑aware record schema and block parsing. Because `derive_actor` and `derive_actor_family` are the *same kind of thing* (elab functions for `:computed` rules) and the latter is a strict superset, every actor surface can route through `derive_actor_family` alone.

## 3. Verified feasibility: what `quote` can hold

`parse_quote` (`parser.ex`:7694) parses the inner form with the ordinary expression grammar (`parse_expr(state, 0)`). Empirically probed on this branch:

| Form | Result |
| --- | --- |
| `quote (fn init(x: Int) -> Int = x)` | **parses** — single `:function_def` |
| `quote %[:ok, initial]` | **parses** — expression body |
| `quote (mod Gen … multiple decls …)` | **fails** — `expected :rparen, got :keyword` |
| `quote` + indented multi‑declaration block | **fails** — `unexpected_token :newline` |

**Verdict:** `quote` holds exactly one form — a single expression *or* a single declaration — but not a `mod` block and not an indented declaration block.

**Implication:** the templated rewrite is available *now* at per‑declaration granularity. Each `function("handle_cast", [parameter("message", variable("Message")), parameter("state", variable("State"))], result_type, body)` becomes

```
quote (fn handle_cast(message: Message, state: State) -> Effect(Tuple(Atom, State)) = $(body))
```

which reads like the code it emits. The module wrapper (`mod … behaviour … [decls]`) still needs the thin `gen_server_module` assembler. Closing that last gap — one template for the whole module — is a self‑contained parser feature (§4, step 1c), not a blocker.

## 4. Stage 1 — Actor (Tiers 1 & 2, templated)

The reference implementation. Every step is independently green‑gated; the byte‑identical goldens are the spine that lets a backend rewrite be *proven* safe, not assumed.

### 1a — Fold to one expander
Retire the standalone bodies of `derive_actor`, `emit_actor`, `emit_actor_call`, and the `ActorSyntax` capture record. `emit_actor`/`emit_actor_call` are deleted outright (their only caller, the old `derive_actor` body, is gone). `derive_actor` is *rewritten in place* — same name, same `syntax … computed by derive_actor` target in `ActorContainers`, so that grammar rule needs no change — into a one-line adapter: it builds an `ActorDefinitionSyntax` (name→`ModuleName`, `state_type`→`state`, `cast_body`→`on_cast`, `call_body`→`on_call`, remaining optionals `None`) and delegates to `derive_actor_family`. Every surface then routes through `derive_actor_family` → `emit_actor_parts`/`emit_actor_call_parts`. This provisionally applies mechanism (b) from step 1e to the `derive` rule so 1a is independently gate‑able without first resolving 1e's open mechanism choice (§10 item 1); if 1e later adopts mechanism (a), it supersedes this adapter for `derive`/`call` too, not only the other 15 Gen A forms. Output is byte‑identical because Gen C fills the same defaults the wrappers hardcoded.
**Guard:** `GDerived` BEAM‑SHA256 golden byte‑identical + the 19 behavioral tests in `test/cure/compiler/actor_computed_test.exs` (immutable — they pin the `derive` surface).

### 1b — Templatize the backend
Rewrite `emit_actor_parts`/`emit_actor_call_parts` and the handler transforms (`actor_call_handler_arm_node` et al.) as per‑declaration `quote` templates with `$()` splices; a thin `gen_server_module` assembles the templated declarations and the variable‑length message enum. The expander now reads as literal Cure.
**Guard:** the same goldens, still byte‑identical.

### 1c — (optional infra) Whole‑module `quote`
Extend `quote` to accept an indented declaration block and a `$(decls ...)` group‑splice into a module body, collapsing the skeleton into a single template. Sequenced *after* 1b so 1b stands on its own; if this proves thorny it slips to its own follow‑up without blocking Stage 1. P‑layer only — outside the TCB.
**Guard:** goldens byte‑identical + new `quote` round‑trip tests (parse → print → reparse) covering the block and group‑splice forms.

### 1d — Body passthrough (the Gen C gap)
Add `optional body Declarations` to the `ActorDefinition` family; thread a `List(Syntax)` of extra user declarations through the emitters and `append` them into the emitted block. This gives the structured surface the arbitrary‑trailing‑declarations power only the Gen A `with`/bare‑body templates had.
**Guard:** a new behavioral test for a user‑declaration‑carrying actor; no‑body goldens unchanged.

### 1e — Terse shorthand + remove Gen A
Re‑express the remaining Gen A positional forms as delegating rules onto `derive_actor_family`, and decide whether to also fold the `derive`/`call` rule's provisional 1a adapter into the same mechanism. Two mechanisms, decided at planning time:
- **(a) preferred** — teach the family surface to accept keyword aliases (`derive` ≡ `on_cast`, `call` ≡ `on_call`) so the terse forms *are* the structured form with shorter labels, lowered straight to `derive_actor_family`. Requires a small parser capability; confirm it exists or add it.
- **(b) fallback** — keep each terse form as a thin `computed by` rule whose elab is a one‑line adapter that fills an `ActorDefinitionSyntax` and calls `derive_actor_family`. Available today; leaves a few near‑empty adapters instead of one expander.

Then migrate the 12 demos (`examples/cure_motif/cure_src/{voice,sequencer,clock}.cure`, `examples/cure_atelier/cure_src/{painter,curator}.cure`, `examples/cure_colony/cure_src/{echo,worker}.cure`, `examples/cure_forge/cure_src/{metrics,logger,queue,pool}.cure`, `vicure/test_syntax.cure`) to the surviving surface and delete the 16 `becomes` templates.
**Guard:** a temporary parity test per terse form (byte‑identical to its old template) + each migrated demo's own Mix test suite (e.g. `mix test` in `examples/cure_motif/`, `examples/cure_atelier/`, `examples/cure_colony/`, `examples/cure_forge/`) + full suite. (`phase35/run-on-unix.sh` is a generic‑unix AtomVM harness in the separate `esp32-beam` repo, not part of `cure-lang` — not applicable here.)

## 5. Stage 2 — fsm / supervisor / app

Replay 1a–1e per sibling against its own golden (`GFsmDerived`, `GSup`, `GApp` in `actor_quote_golden_test.exs`), one file at a time, each independently gated:

- **`fsm`** mirrors actor — it has a Gen B `derive_fsm` + `emit_fsm`/`emit_fsm_parts` and a `FsmSyntax` record to fold, plus `syntax family FsmDefinition` + `derive_fsm_family`.
- **`supervisor`** / **`app`** are lighter — `syntax family …Definition` + `derive_…_family` + `…Containers` templates, no separate Gen B layer.

If 1c landed in Stage 1, all four collapse to whole‑module single templates here. These are near‑mechanical replays of the proven actor pattern.

## 6. Stage 3 — Tier 3: typed, Lean‑`MetaM`‑style macros (deferred)

An elaborator‑integrated macro that sees inferred types and datatype structure, added last. It removes the one irreducibly‑uncouth remainder of Stages 1–2: syntax **analysis**. Quasiquotation makes *synthesis* (producing output) elegant, but it does nothing for *analysis* (inspecting the user's syntax). The reply‑type derivation `derive_reply_contract` / `infer_reply_type` / `reply_expr_type` walks the user's `call` body and sniffs literal subtypes (`:integer → Int`, `:float → Float`, `:symbol → Atom`, `:boolean → Bool`) to *guess* the reply type — a hack that is irreducibly procedural at Tier 2. A typed macro asks the elaborator for the *inferred* type instead.

Tier 3 is also the principled home for deriving and the OTP‑metatheory pid‑index / `ReplyOf(req)` work (see `docs/research/process-types/`). It gets its own brainstorm → spec → plan when we reach it; recorded here as direction, not detail.

## 7. Roadmap context: the Lean‑style three tiers

The end state realizes the Lean‑4 macro architecture:

| Tier | Lean analog | Cure realization |
| --- | --- | --- |
| 1 — declarative shorthand | `macro` / `macro_rules` | terse positional forms delegating to the Tier‑2 expander (family keyword‑aliases or thin `computed by` adapters, per 1e — not the retired `becomes lift module name` skeletons) |
| 2 — procedural expander | `elab` / `elab_rules` | `syntax family` + quote‑based `expands with` expander over one backend |
| 3 — typed metaprogramming | `MetaM` / elaborator reflection | typed access to inferred types + datatype structure (Stage 3) |

Stages 1–2 build tiers 1–2; Stage 3 adds tier 3.

## 8. Testing and guards

- **Byte‑identical goldens** (`actor_quote_golden_test.exs`: `GDerived`, `GStructuredCall`, `GLifecycle`, `GFsmDerived`, `GSup`, `GApp`) are the anti‑regression spine. Any backend edit keeps them byte‑identical, or is consciously re‑blessed with justification.
- **Behavioral tests** (`actor_computed_test.exs`, immutable) pin the `derive` surface across the fold.
- **New tests** cover body passthrough (1d), init‑mode precedence (`initial` wins over `init`, already handled by `derive_actor_init`), and the whole‑module `quote` forms (1c).
- Red‑green throughout; scoped `mix test <file>` during iteration, one full suite alone at each stage gate.

## 9. Constraints

- No change to `lib/cure/core/*` (TCB). The one parser step (1c) is P‑layer.
- Ghost‑writer commits (`--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no co‑sign); explicit‑pathspec staging only.
- Author stdlib in `lib/std/`, never `priv/std/` (generated bundle).
- One `mix` build at a time.

## 10. Open decisions carried to planning

1. **Terse delegation mechanism (1e):** keyword‑alias in the family (preferred) vs thin per‑form adapter (fallback) — decided by whether the family surface can express alternate keyword spellings cheaply.
2. **Whole‑module `quote` (1c):** include in Stage 1 after 1b, or defer to its own follow‑up if the parser extension proves thorny. Neither choice blocks 1a/1b/1d/1e.
