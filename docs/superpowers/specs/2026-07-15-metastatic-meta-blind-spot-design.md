# Metastatic's meta-slot blind spot — design

**Date:** 2026-07-15
**Status:** design for review (no implementation)
**Related:** the six irregular-tuple shapes (separate, smaller gap — see §3); `lib/cure/meta_ast/conformance.ex` (the detector built for component (1)); the migrator→MetaAST rework (downstream consumer).

## 1. Summary

Metastatic's generic AST traversal descends only the **children** slot of a
canonical `{type, meta, children}` node. It never walks the **meta** slot. Cure's
surface AST stores a large fraction of its most important subtrees *in meta* —
every parameter's type, every function's parameter list and return type, every
match arm's pattern, and more. Those subtrees are invisible to every consumer
built on stock Metastatic traversal (RAG index, MCP, the migrator, any future
tool). Empirically that is **~2,600 hidden nodes across the 48-module stdlib**.

This is distinct from — and much larger than — the six irregular tuple *shapes*
(§3). A node can be perfectly shape-conformant and still hide its entire type
structure in meta; `param` and `function_def` both do exactly that.

The question this spec answers: **can we fix our side rather than change the
Metastatic dependency, and is an Elixir source rewriter the right mechanism?**
Short answer: yes to the first; the rewriter earns its keep *only* for the
full representation refactor (Option C), and even there its leverage is at the
construction sites, not the read sites. Cheaper adapter options (A, B) resolve
every consumer we can currently name without any rewrite. The real decision is
whether we pay to eliminate a standing walker-drift trap or accept adapter
discipline forever.

## 2. The blind spot — mechanism and evidence

### 2.1 Mechanism

`Metastatic.AST.do_traverse/4` (`deps/metastatic/lib/metastatic/ast.ex:730`)
matches `{type, meta, children} when is_atom(type) and is_list(meta)`, applies
the pre hook, recurses **only via `traverse_children` on the third slot**,
reconstructs `{type, meta, new_children}`, then applies the post hook. The meta
slot is copied through untouched — never walked. `prewalk/2,3`, `postwalk/2,3`,
and `traverse/4` all delegate here (`ast.ex:800, 824, 842`), so **every**
Metastatic walker shares the blind spot. There is no per-walker escape.

### 2.2 The two representative nodes (confirmed against the live parser)

```
function_def  = {:function_def, meta, [body_expr]}
    meta keys:   [:return_type, :name, :params, :visibility, :arity, :line, :col]
    :return_type → a {:variable,…} NODE
    :params      → a LIST of {:param,…} NODES
    children     → [body] only

param         = {:param, [type: {:variable,…}], "x"}
    meta keys:   [:type]
    :type        → a NODE
    children     → the name string "x" (a leaf)
```

Both are **structurally canonical 3-tuples** — atom tag, keyword meta, third
slot. Stock Metastatic descends `function_def`'s body and `param`'s name string,
and stops. It never sees the parameter list, the parameter types, the return
type. The entire signature/type layer of every function is dark.

### 2.3 Scan of the stdlib (48 modules)

Meta keys whose value hides a canonical node, by `(parent_tag, key)` and count
(`scratchpad/metascan2.exs` — a total-descent walk that records each meta value
containing a node):

| parent · key | count |
|---|---|
| `param :type` | 999 |
| `function_def :params` | 535 |
| `function_def :return_type` | 526 |
| `match_arm :pattern` | 366 |
| `container :decorator` | 54 |
| `lambda :params` | 31 |
| `implementation :for_type` | 18 |
| `indexed_type :indices` / `:params` / `:decorator` | 11 |
| `function_call :callee` | 9 |
| `function_def :constraints` | 7 |
| **total** | **~2,600** |

This is not a corner case. It is the signature, type-annotation, and
pattern-matching surface of essentially every definition Cure has.

## 3. Relationship to the six irregular shapes (a separate, smaller gap)

The detector in `lib/cure/meta_ast/conformance.ex` flags **shape**
non-conformance: atom-headed tuples that are not canonical 3-tuples and that
hide a node. There are six such shapes, ~66 occurrences in stdlib:
`named_implicit_pat` (4-tuple), `named_dom` (`{tag, name, inner}`), `arrow_chain`
(2-tuple), `gadt_ctor` (canonical but children slot holds a bare arrow_chain),
`:group` (2-tuple), `:builtin` (2-tuple).

These are **orthogonal** to the blind spot:

- Fixing the six shapes (normalize to 3-tuples) makes them *reachable* once
  they sit in a children slot — but does nothing for the 2,600 nodes that are
  reachable-in-principle yet parked in meta.
- Fixing the blind spot (meta→children, or a meta-aware walker) does nothing for
  a malformed 2-tuple.

Both must be addressed for full conformance, but they are independent work. The
detector already covers the shape gap (component (1)); this spec is about the
meta gap.

## 4. Why the compiler's safety net does not cover the meta fix

For the six shapes, flipping a construction site produces Elixir
unreachable-clause warnings and pattern-match failures at every stale consumer —
the compiler hands you the worklist. **The meta fix has no such net.** A reader
does `Keyword.get(meta, :type)` or `meta[:type]`; after the type moves to a
child, that call returns `nil` — a valid value, no warning, no crash at the read
site. The breakage surfaces later and elsewhere (a `nil` where a node was
expected), or not at all until a specific path runs. These meta keys are read
throughout `lib/cure/**` — via `Keyword.get`, `Keyword.fetch!`, and pattern
destructuring under many local names (`meta`, `p_meta`, …), so there is no single
grep that enumerates them and no compile-time list to work down — and many of the
reads sit on the elaborator hot path.

This asymmetry is the whole reason a source rewriter is worth discussing: the
change is mechanical and repetitive, and the compiler will not find the sites
for you. It is also why the conformance detector matters as a **green gate** — a
detector extended to also flag "canonical node hidden in meta" gives the mass
change a red→green signal that the compiler alone cannot.

## 5. Fix options

Two axes: **our side vs. Metastatic side**, and **adapter vs. representation
change**. The user's stated preference is our-side; this section foregrounds A/B/C
and treats D as contrast.

### Option A — Cure-side meta-aware traversal (adapter, internal consumers)

Add `Cure.MetaAST.prewalk/postwalk/traverse` that descend meta *values* as well
as children (the detector's `walk_meta_values/3` already prototypes exactly this
descent). Internal tools — the migrator above all — call the Cure wrapper instead
of `Metastatic.AST.prewalk`.

- **Cost:** one module, no representation change, no elaborator risk, no rewriter.
- **Serves:** every internal Cure tool that we control.
- **Does not serve:** external raw-Metastatic consumers (RAG/MCP indexing that
  calls stock Metastatic on exported AST).
- **Caveat:** correctness now depends on every author remembering to use the
  Cure wrapper. Anyone who reaches for stock `Metastatic.prewalk` silently gets
  the blind spot back. This is the standing walker-drift trap (§6).

### Option B — boundary canonicalization (adapter, external consumers)

At the one choke point where Cure exports AST to Metastatic consumers (the
RAG/MCP upsert / serialization boundary), run a generic structural transform
`Cure.MetaAST.to_conformant/1` that lifts every meta value containing a node
into the children slot under a wrapper node (e.g. `param`'s `:type` becomes a
child `{:param_type, meta, [type_node]}`; keys carrying only primitives stay in
meta). Internal representation is untouched.

- **Cost:** one transform function (a rewriting cousin of the detector's walk),
  no internal changes, no rewriter.
- **Serves:** external raw-Metastatic consumers — they receive a tree stock
  traversal fully descends.
- **Does not serve:** anything that round-trips the *internal* form (the migrator
  reprints internal AST; it needs A, or an inverse of B).
- **Caveat:** the exported form differs from the internal form. Two shapes to
  keep straight; the printer must not be fed the canonicalized form.

A + B together resolve every consumer we can currently name, for the price of two
functions and zero representation change.

### Option C — representation refactor: move subtrees meta→children (the principled fix)

Change the parser (and any other constructor) so type/param/pattern subtrees are
built into the **children** slot from the start, and migrate every reader. After
this, the internal AST simply *is* conformant: stock Metastatic, the Cure
wrapper, external consumers, and any future tool all work uniformly, with no
adapter and no discipline to remember.

This is where an **Elixir source rewriter earns its keep** — and only here.
Details in §6. In short:

- **Construction sites** (parser, a handful of builders) are few, localized, and
  deterministic — a Sourceror-based rewrite transforms them safely.
- **Read sites** (~55) are the hard part: a purely syntactic rewriter cannot
  always know that a given `meta[:type]` belongs to a `param` (it lacks the
  runtime node type), so it cannot blindly rewrite them. Read-site migration is
  therefore rewriter-*assisted* (transform the unambiguous patterns) plus
  grep-guided manual work, with the **behavioral test suite** catching stale
  readers (nil regressions) and the **extended detector** confirming the shape
  end-state.

- **Cost:** largest blast radius; touches the elaborator hot path (K-adjacent
  risk); silent-read hazard mitigated only by test coverage + detector.
- **Benefit:** eliminates the walker-drift trap permanently. No adapter, no
  discipline, one representation.
- **Sequencing:** do it **incrementally, one node type at a time**, gated by the
  extended detector, each step compiler+test-verified. `param :type` (999) is
  the highest-value first target; `function_def :params`/`:return_type` next.
  Big-bang is not required and not advised.

### Option D — Metastatic descends meta values (contrast; not our side)

Add an opt-in flag to `Metastatic.AST.traverse` to walk meta values. Smallest
possible change in lines, fixes all consumers at once — but it changes the shared
dependency, and it changes traversal semantics for *every* Metastatic user, not
just Cure. Listed for completeness; out of scope given the our-side preference,
though worth a conversation with the Metastatic owner if the trap in §6 is judged
unacceptable and C is judged too expensive.

### Rejected — per-key registry

A table of "these meta keys hold nodes, descend them." Rejected: it is the
walker-drift pattern the project treats as critical (a new meta key that holds a
node is silently skipped until someone updates the table; nothing fails closed).
Every option above is **structural** — it keys on "the value contains a node,"
never on a hard-coded key list — and so is drift-proof by construction.

## 6. The Elixir source rewriter, examined

The user's intuition — "a source rewriter would earn its keep if we fix our
side" — is correct, with one important scoping.

**Where it clearly helps (construction).** Moving `{:param, [type: t], name}` →
`{:param, meta, [name, t]}` (or a wrapper child) at the parser build sites is a
mechanical, semantics-preserving AST edit. Sourceror can do this reliably: match
the construction pattern, restructure the tuple, preserve formatting.

**Where it is limited (reads).** A read site is `Keyword.get(meta, :type)` /
`meta[:type]` / a pattern `{:param, meta, name}` followed by `meta[:type]`. A
syntactic rewriter sees the variable `meta`; it does not know the runtime node is
a `param`. It can transform the *pattern-matched* cases (where the node tag is
visible in the same clause) but not the general `meta[:type]` reached through a
helper. So read-site migration is: rewriter for the unambiguous cases, manual for
the rest, with two nets — the behavioral suite (a stale reader yields `nil` →
some test fails) and the extended detector (shape end-state is provably
conformant).

**Why the detector is the linchpin.** Extend `Cure.MetaAST.Conformance` with a
second predicate: *no canonical node appears inside any meta value*. Today that
tripwire is red (2,600 hits); it goes green only when C is complete for the node
types in scope. This is the red→green gate the compiler cannot provide for a
silent-read change. Combined with the incremental sequencing, each node type's
migration is: rewrite construction → migrate reads → detector confirms that
node's meta is node-free → full suite green → commit.

**Honest verdict on the rewriter.** It is a genuine force multiplier for
construction and for the regular read patterns, and the detector makes the whole
operation verifiable. It is *not* a push-button codemod that flips the
representation unattended — the read layer needs human judgment and test coverage.
If we choose C, build the rewriter; if we choose A+B, the rewriter has nothing to
do.

## 7. Recommendation

1. **Now, to unblock consumers:** ship **A + B**. Two structural functions, no
   representation change, no rewriter, no elaborator risk. This makes the
   migrator (via A) and any external index (via B) see the full AST immediately.
   Lowest-risk, and it honors "if it's just semantics, prefer the lower-risk
   option."

2. **File C as the principled end-state**, to be executed **incrementally,
   rewriter-assisted, detector-gated**, starting with `param :type`. Its
   justification is not the named consumers (A+B already serve them) — it is
   **eliminating the standing walker-drift trap**: with A+B, any future code that
   reaches for stock `Metastatic.prewalk` silently mishandles the signature layer
   forever, and nothing warns. Given how seriously this project treats
   walker-drift (fail-closed walkers, structural detection, the core-walker-drift
   audit), that trap is a real liability, not mere aesthetics. C removes it.

3. **The decision to actually do C** is the one genuine fork, and it is the
   owner's: pay a large, elaborator-touching, incrementally-staged refactor to
   remove the trap, versus accept permanent adapter discipline. This spec does
   not pre-decide it; A+B are valuable and shippable regardless.

## 8. Open questions

- **Consumer inventory.** Exactly which tools consume Cure AST through stock
  Metastatic today (RAG index? MCP? anything else)? This determines whether B is
  even needed now, and how urgent the trap in §6 is. A+B are sized to the answer.
- **Wrapper vs. positional for C.** When a subtree moves to children, does it
  become a positional child or a wrapper node (`{:param_type, meta, [t]}`)?
  Wrapper preserves the key's name and keeps children self-describing; positional
  is leaner but order-dependent. (Recommend wrapper — self-describing, matches how
  B would lift it, keeps A and C convergent.)
- **B's inverse.** Does any consumer need to round-trip B's output back to
  internal form? If yes, B needs a documented inverse; if no (consumers are
  read-only indexes), it does not.
- **Detector extension scope.** Should the meta-hidden-node tripwire live in the
  same `Cure.MetaAST.Conformance` module (a second violation class) or a sibling?
  (Recommend same module, distinct `kind:` on each violation — one detector, two
  gates.)

## 9. Scope / non-goals

- **In scope:** the meta-slot blind spot, the our-side fix options, and the
  rewriter's role. The detector already built for component (1).
- **Out of scope here:** the six-shape normalization (its own follow-up); the
  migrator→MetaAST rework (downstream; consumes whichever fix lands); any change
  to the Metastatic dependency (Option D, noted only for contrast).
- **Non-goal:** a big-bang representation flip. C, if chosen, is incremental and
  gated.
