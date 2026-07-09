# String & Char as Dependent Value-Surface Types (charlist representation) — Design

**Status:** approved design (operator: "we'll do A"), spec written under autopilot.
**Program:** value-surface parity (#23) — bring String/Char into the dependent
pipeline (`lib/cure/elab/*` + `lib/cure/core/*` + `emit.ex`) so the classic
pipeline (`lib/cure/compiler/*` + `lib/cure/types/*`) can be deleted (#18).
**Layer:** K (one aligned kernel primitive) + E (elaboration) + C (emit/erase).
**Verification:** cure-porting differential oracle + Antigen (for the TCB slice).

---

## 1. Goal

`String` and `Char` become ordinary dependent-pipeline values:

- **`Char`** — a primitive base type, an inhabitant is a Unicode **code point**
  (`0 ≤ c ≤ 0x10FFFF`). Erases to a bare BEAM integer.
- **`String = List(Char)`** — a type-level *definition*, not a new primitive.
  A `String` value is a native cons list of code-point integers — i.e. an
  Erlang **charlist** `[97, 98, 99]`. String literals and interpolations
  elaborate to that list.
- **`Atom`** — explicitly **out of scope** for this wave (see §7). It is a
  separate minimal opaque base type; deferred.

The payoff: `String` stops being a would-be kernel base type. It is *dissolved*
into the already-working `List` machinery, so the "add a String primitive to the
TCB" ask disappears. The only kernel addition is `Char`, which is
Agda/Idris-faithful (both have a primitive `Char`) and mechanically parallel to
the existing `Int`/`Float` primitives.

## 2. Why this shape (alternatives considered & rejected)

### 2.1 `Char = Bounded(0x110000)` — REJECTED
`Std.Bounded` (`lib/std/bounded.cure`) is a **unary Peano** Fin:
`First : Bounded(S(m))`, `Next : Bounded(m) -> Bounded(S(m))`. Representing code
point 97 would require 97 nested `Next` constructors — absurd as a runtime
carrier and non-erasable to a machine integer. `Bounded` is a length-index proof
type for `Vector`, not a codepoint carrier. Dead on arrival.

### 2.2 `Char` erases to `Int`, nominal only in the elaborator (kernel `Char = Int`) — REJECTED
Zero-TCB, but `Char` and `Int` become kernel-indistinguishable: `f(c: Char)`
would silently accept an `Int`, and `String = List(Char) = List(Int)` conflates
strings with integer lists. Loses the type distinction the whole exercise is for.

### 2.3 `Char` as a primitive base type — CHOSEN
Agda: `{-# BUILTIN CHAR Char #-}` (primitive, distinct from `Nat`, with
`primCharToNat`/`primNatToChar`). Idris: primitive `Char`. Lean: a validated
`UInt32` structure. Two of three real languages make `Char` a *primitive*, so a
`{:char_type}`/`{:char_lit}` kernel pair is **alignment-faithful** and covered by
the TCB blanket approval — while still requiring the full Antigen + suite gate
(it is a TCB change; treat it as HARD-STOP-reviewed, but the *direction* is
pre-approved because it matches Agda/Idris). It mirrors the existing
`{:int_type}`/`{:int_lit}` clauses one-for-one, so the diff is mechanical.

### 2.4 `String` primitive with `toList`/`fromList` (the Agda/Idris shape) — NOT CHOSEN (operator override)
Agda/Idris make `String` a **primitive** (a packed representation) with
`primStringToList : String → List Char` and `primStringFromList` — String is
*not* literally `List Char`. That is the binary-backed "Option B" from the design
conversation. The operator explicitly chose **Option A**: `String` *is*
`List(Char)`, represented as a charlist. This is a **deliberate, recorded
divergence** from Agda/Idris, taken because (a) it makes the
`String = List(Char)` equation literally true rather than a conversion, (b) it
needs the least machinery — no String primitive, no packed-string ops surface —
and (c) `@builtin`/`@extern` at the binary boundary preserves a later migration
to a packed representation *behind the unchanged `List(Char)` type*, if embedded
perf ever demands it. The alignment default is overridden by an explicit operator
decision; recorded here so review does not "correct" it back to a primitive.

### 2.5 Grapheme clusters (`Character` à la Swift) — DEFERRED
AtomVM ships **no** grapheme segmentation (`string.erl` is codepoint/charlist
based: `to_upper`/`to_lower`/`split`/`trim`/`find`/`length`/`jaro`, no
`next_grapheme`). A Swift-style `GraphemeCluster` would be a pure-Cure derived
library over `List(Char)` doing its own Unicode boundary tables — real work with
zero native help. Correctly a *later, derived* type; not this wave.

## 3. Runtime & AtomVM substrate (verified in the tree)

Confirmed native in `/Users/ch/Develop/esp32-beam/AtomVM`:
- **UTF-8 bitstring codegen is native** (`bitstring.c`: `bs_utf8_size`,
  `bitstring_utf8_encode`, `bitstring_match_utf8`). `<<C/utf8>>` build **and**
  `<<C/utf8, Rest/binary>>` match run on-device. This is what lets the
  charlist↔binary bridge be plain Erlang, no custom NIF.
- **`unicode:characters_to_binary/1,2,3`** and **`characters_to_list/1,2`** are
  real native NIFs (`nifs.c:6850,6911`) — charlist↔UTF-8-binary both directions.
- Atoms are UTF-8 (`unicode_utf8_decode`, `unicode_is_valid_codepoint` in the
  atom path). (Relevant to the deferred Atom work, not this wave.)
- `binary` module: `at/2, part/3, split, match, replace, copy, encode/decode_hex`.
- `string` module: codepoint-based, Latin-1 `to_upper/to_lower`, `split, trim,
  find, length, jaro`.

Consequence: a `String` value = an Erlang charlist works everywhere charlists
work (`~ts` formatting, `unicode:characters_to_binary`), and a binary is produced
on demand by one native NIF call at the interop boundary.

## 4. Components

### 4.1 Kernel: the `Char` primitive (TCB — HARD-STOP-reviewed, Agda/Idris-aligned)
Mirror the existing `Int` base-type machinery in `lib/cure/core/term.ex`:
- **Terms:** add `{:char_type}` (the type) and `{:char_lit, cp}` (a literal
  code point, `cp` a non-negative integer `≤ 0x10FFFF`), parallel to
  `{:int_type}`/`{:int_lit, n}`.
- Clauses to add, each mirroring the `int_*` neighbour verbatim:
  - `term?/1` (near :61-64)
  - `shift/*` (near :86-89) — a closed literal/type, shift is identity
  - `subst/*` (near :149-152) — identity
  - `to_external/1` (near :215-218)
  - `from_external/1` (near :249-252)
- **Conversion (`conv.ex`)**: `{:char_lit, a}` conv `{:char_lit, b}` ⇔ `a == b`;
  `{:char_type}` conv `{:char_type}`. Mirror the `int_lit`/`int_type` cases.
- **Normalisation (`normalise.ex`)**: `char_lit`/`char_type` are already normal
  (no reduction), mirror `int_lit`.
- **No new eliminator, no arithmetic in the kernel.** `Char` is inert: it is
  introduced by literals and consumed only by equality (via `==`, §4.4) and by
  the `@builtin`/`@extern` bridge. Codepoint↔Int conversion lives in the
  elaborator/std as `@extern` (mirrors Agda's `primCharToNat`), NOT as kernel
  reduction — keeps the TCB minimal.

**Antigen obligation (mandatory for the TCB slice):** a new antibody proving the
`Char` clauses (a) terminate and (b) equate no distinct normal forms
(`{:char_lit, a} ≡ {:char_lit, b}` iff `a == b`) — the same soundness contract
the `Int` literal clauses satisfy. Plus the full Antigen suite and full test
suite, run once, alone (never concurrent).

### 4.2 Elaboration: char literals
`lib/cure/elab/elaborator.ex` literal handler (~:448-456, and the second
infer-mode copy ~:4907). The lexer already emits a `:char` token whose value is
the decoded code-point integer (`lexer.ex:886-909`), and the parser already
produces a `:char` literal node (`parser.ex:236-237`). Add:
- `:char when is_integer(value) -> {:ok, {:char_lit, value}, {:vchar_type}}`
  (mirror the `:integer` clause at :452), where `{:vchar_type}` is the value form
  of `{:char_type}` (add the value-form constructor alongside `{:vint_type}`).

### 4.3 Elaboration: `Char` and `String` as named types
- `Char` resolves to `{:char_type}`. Add to the primitive-type resolver
  (`declarations.ex:1113-1115`, `primitive_type("Int") -> {:int_type}`): a
  `primitive_type("Char") -> {:char_type}` clause. `Char` needs **no** std
  `type` declaration (it is a primitive, like `Int`).
- `String` is a **type alias** for `List(Char)`. It is *not* a primitive and not
  a new inductive. Introduce it as a resolved alias so a signature written
  `String` elaborates identically to `List(Char)`. Preferred locus: a std
  `type String = List(Char)` alias if the surface supports type aliases;
  otherwise an elaborator-level alias in the name resolver that expands `String`
  → `List(Char)` before kind-checking. (Plan step: confirm whether Cure already
  has surface type aliases; if yes use the surface form in `lib/std/string.cure`,
  if no add the resolver expansion. Do not invent a new alias mechanism if one
  exists.)

### 4.4 Elaboration: string literals & interpolation → charlist
- A bare string literal reaches the dependent pipeline as the lexer/parser
  string form. Elaborate `"abc"` to the **`List(Char)` cons spine**
  `Cons('a', Cons('b', Cons('c', Nil)))` at the Core level — i.e. reuse the
  existing `:list` elaboration (already routed through `elaborate_expr_checked`,
  Wave 4) with `{:char_lit, cp}` elements. Concretely: desugar the string
  literal node into the same Core the list literal `['a','b','c']` produces, so
  there is **one** list-elaboration path, not a bespoke string path.
- **Interpolation** (`{:string_interpolation, _, parts}`, `parser.ex:494`):
  desugar to `List` concatenation (`++`) of the parts, where a literal part is a
  charlist and an interpolated expression part is rendered to a `String`
  (`List(Char)`) via the `Show`/`to_string` path. For this wave, restrict
  interpolated parts to expressions already of type `String`; general
  `Show`-based rendering is a follow-up (typeclasses, #21). A string with no
  interpolation is the pure-literal case above.
- Equality: `s1 == s2` on `String` is `List(Char)` equality — already provided by
  the list machinery / the `==` dispatch, no new codepoint-eq primitive beyond
  `char_lit` conversion (§4.1).

### 4.5 Emit & erase (`lib/cure/elab/emit.ex`, `erase.ex`)
- `{:char_lit, cp}` → the BEAM integer literal `{:integer, @line, cp}` (mirror the
  `int_lit` lowering at emit.ex:210-211). A `Char` is a bare integer at runtime.
- `String` needs **no** dedicated emit: it is `List(Char)`, and `List` already
  lowers to native cons cells (builtin-inductive-foundation). So `"abc"` lowers
  to `[97,98,99]` — a genuine Erlang charlist.
- Erasure: `Char` erases like `Int` (a bare integer; relevant, present). Add the
  parallel erase clause if erase enumerates base types.

### 4.6 The `String ↔ Binary` boundary bridge (`@builtin`/`@extern`)
Two std functions, the *only* place a binary appears:
- `to_binary(s: String) -> Binary` — `@extern(:unicode, :characters_to_binary, 1)`
  (native NIF; charlist → UTF-8 binary).
- `from_binary(b: Binary) -> String` —
  `@extern(:unicode, :characters_to_list, 1)` (native NIF; UTF-8 binary →
  charlist). (`Binary` is the existing binary type; unchanged by this wave.)
These let `Std.String` keep delegating heavy Unicode ops to native `:string`/
`:binary` NIFs by converting at the boundary, without a String primitive.

### 4.7 `Std.String` migration (`lib/std/string.cure`)
Current file is binary-backed (`@extern :erlang.byte_size` for `length`, etc.).
Because disposition is **binary per module**, `Std.String` flips to KEEP only
when *every* decl elaborates. Migration policy:
- **Structural ops → native `List` ops.** `length` = `List.length` (now a
  **code-point count**, strictly more correct than the current byte-count wart
  the file's own doc apologises for). `is_empty` = `List.is_empty`/`== ""`.
  `concat`/`++` = `List.append`. Reverse, etc. — `List` functions.
- **Unicode/heavy ops → bridge to native NIFs.** `upcase`/`downcase`/`trim`/
  `split` etc.: convert `String`→`Binary` via §4.6, call the native
  `:string`/`:binary` NIF (which want binaries), convert result back. Keep these
  as thin wrappers; do **not** reimplement Unicode tables in Cure.
- **Numeric parsers** (`to_int`/`from_int`/`to_float`…): these bridge to binary
  and call the existing BIFs; from_int etc. produce a charlist via `from_binary`.
- **Scope guard:** if the full-file migration is too large to land in one wave,
  the wave's ratchet may instead be demonstrated by a **new small module**
  (`lib/std/string_demo.cure` or a test module) that `use`s the foundation and
  KEEPs, with the legacy `Std.String` full migration split into an explicit
  follow-up. The ratchet (value-surface KEEP count) must move by ≥1 either way.

## 5. Data flow

```
"abc"  --lex-->  :string token
       --parse-> :string_interpolation / string-literal node
       --elab--> Core Cons({:char_lit,97}, Cons(98, Cons(99, Nil)))   : List(Char)  (= String)
       --emit--> [97,98,99]   (Erlang charlist)
'a'    --lex-->  :char token (value 97)
       --parse-> {:char, _, 97}
       --elab--> {:char_lit, 97} : Char
       --emit--> 97
String --resolve--> List(Char)     (alias, §4.3)
String --to_binary--> unicode:characters_to_binary --> <<"abc"/utf8>>   (boundary only)
```

## 6. Error handling
- **Invalid code point in a `char_lit`** (surrogate `0xD800..0xDFFF`, or
  `> 0x10FFFF`): the *type* `Char` over-approximates (it admits the full
  `0..0x10FFFF` integer range including surrogates — there is no refinement type,
  those were dropped). Validity is a **boundary invariant**: the native
  `bitstring_utf8_encode`/`characters_to_binary` reject invalid code points at
  the `to_binary` boundary (returns error / raises), so an invalid `Char` cannot
  silently become a valid UTF-8 binary. Record this as a known, deliberate gap:
  a surrogate-excluding `Char` needs a refinement or a bespoke validated type,
  deferred. The lexer already rejects malformed char literals
  (`:unterminated_char`).
- **Interpolating a non-`String` expression** (this wave): a type error at
  elaboration (expected `String`), until `Show`-based rendering lands (#21).
- **`from_binary` on invalid UTF-8**: propagates the native NIF's error tuple /
  exception unchanged (matching the current BIF-raise convention documented in
  `string.cure`).

## 7. Scope / non-goals
- **`Atom`** — deferred. A minimal opaque base type (UTF-8 sentinel), not
  `List(Char)`. Separate follow-up wave; do not build here.
- **`Show`/`to_string` general rendering** in interpolation — deferred to
  typeclasses (#21). This wave restricts interpolation to `String` parts.
- **Grapheme clusters / `Character`** — deferred derived library (§2.5).
- **Surrogate-excluding refined `Char`** — deferred (no refinement types).
- **Migrating a packed/binary `String` representation** — explicitly not now;
  `@builtin` keeps it available later behind the unchanged `List(Char)` type.
- **No kernel arithmetic/eliminator for `Char`** — inert primitive only.

## 8. Testing

Strict red-green throughout; cure-porting differential oracle is the arbiter.

- **Kernel (TCB) — Antigen first.** New antibody: `char_lit` conversion soundness
  (equates iff equal code points) + termination of the new `term.ex`/`conv.ex`/
  `normalise.ex` clauses. Full Antigen suite + full `mix test`, once, alone.
- **Oracle probes** (paired `.cure`/`.idr`, `mix cure.oracle`):
  - a `Char` literal and a `Char`-typed function signature — `same` as Idris
    (Idris has primitive `Char`).
  - a `String` literal bound and pattern-matched as a list
    (`case unpack s of [] => … | c :: cs => …`) — note the *expected* divergence
    where Idris's `String` is primitive (needs `unpack`); mark the fixture
    relation honestly (`cure_stricter`/`idris_only` with the written reason that
    Cure's `String` *is* `List Char` by the operator's Option-A choice, §2.4).
    Do **not** silently label the divergence a bug.
- **Elaboration unit tests** (dependent pipeline only — ignore `compiler/*`,
  `types/*`):
  - `'a'` elaborates to `{:char_lit, 97}` of type `Char`.
  - `"abc"` elaborates to the `List(Char)` cons spine and **emits** `[97,98,99]`
    (assert the emitted Erlang abstract form / a run through the dependent
    pipeline, not the classic codegen).
  - `String` in a signature resolves to `List(Char)`.
  - `to_binary("abc")` runs and yields `<<"abc">>`; `from_binary(<<"abc">>)`
    yields `"abc"` — round-trip on generic-unix AtomVM (per CLAUDE.md, validate
    on host before any claim).
- **Ratchet:** value-surface KEEP count moves by ≥1 (either legacy `Std.String`
  flips, or a new demo module KEEPs — §4.7 scope guard). Record the before/after
  count. No prior-KEEP regression; oracle replay green before commit.

## 9. Sequencing & risk
- The `Char` kernel slice is the only TCB touch: mechanical (mirror `Int`),
  Agda/Idris-aligned, blanket-approved in *direction* but gated by the full
  Antigen + suite run. Land it first, green, before the elaboration/emit slices.
- Everything else is E/C layer, low risk, reusing the `:list` path (Wave 4) and
  the native-cons `List` emit already in place.
- Ghost-writer commits (`--author="Made In Heaven <madeinheaven@madeinheaven.com>"`,
  no co-sign), explicit-pathspec staging only, one build at a time. Stay on the
  existing `autopilot/kernel-parity-batch` worktree (operator preference — no new
  worktree per sub-feature).
