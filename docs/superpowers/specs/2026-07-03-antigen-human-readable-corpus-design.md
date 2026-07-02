# Antigen human-readable corpus — design

**Status:** approved (design gate). Autopilot run on `autopilot/antigen-tier-b` (stays on this worktree per operator preference).

## 1. Motivation

Banked Antigen corpus records (`test/antigen/seeds.sexp`, runtime antibody files) are
today opaque: each term is `id::Base64(Serialize.encode(term))`, the `note` is
Base64, and a mutant's `fault` provenance map is buried inside the Base64
`scaffold`. The operator wants to **open the file and read/debug the terms by
hand**. This spec makes the load-bearing, human-facing parts of a record
readable on disk while preserving exact round-trip replay.

Scope (locked at the design gate): **terms (all Term pieces) + note + mutant
fault provenance** become readable. General (non-fault) scaffold content and the
dedup `key` stay Base64. Variables stay **positional de Bruijn** — no name
recovery.

## 2. On-disk format

A record is unchanged in shape: one line, tab-separated `field=value` pairs, led
by the `antigen-record` marker. Three fields change form:

### 2.1 `pieces` — tagged s-expressions

Today: `id::Base64(Serialize.encode(t))`, pieces joined by `;;`.
New: `id::(sexpr)` where `(sexpr)` is the tagged s-expression of the Term
(§3). Example (a conversion reject carrier, one line):

```
pieces=term::(ctor vcons (app (app (global plus) (ctor S (ctor Z))) (ctor Z)) (ctor Z) (ctor vnil))
```

The `;;` piece separator and `::` id/term separator are retained; neither
appears inside an s-expression (names are atoms; structure is parens/spaces).

### 2.2 `note` — plaintext

Today: `Base64(note)` or `-` for nil. New: the note verbatim, with a minimal
escaping so it cannot break the tab-separated / newline-terminated record:
percent-encode `%`→`%25`, tab→`%09`, newline→`%0A`. `nil` still encodes as the
bare sentinel `-`; a genuine note equal to `"-"` is escaped to `%2D` so it never
collides with the sentinel (§6.1).

### 2.3 `fault` — readable provenance field (mutants only)

Today: the fault map rides inside the Base64 `scaffold`. New: a dedicated
`fault=` field holding a readable assoc-list s-expression, and the fault is
**removed from the Base64 scaffold**. The fault map is flat with atom / integer
/ `nil` / list-of-atom values, e.g.:

```
fault=((kind head_swap) (witness head) (expected_head Nat) (injected_head Vec) (scope nil) (depth 3) (wrap_path (app_arg case_branch)))
```

Non-mutant records have **no** `fault=` field.

### 2.4 Unchanged fields

`kind`, `assay`, `label`, `seed` (already plaintext), `key` (stays Base64 — it
is a dedup identity, not human-facing), and the **non-fault** `scaffold`
(stays Base64 `term_to_binary`, per scope).

## 3. `Antigen.SExpr` — the term codec

New module `lib/antigen/sexpr.ex`. Pure, dependency-free (no backend, no
generator). Two public functions:

- `encode(Cure.Core.Term.t()) :: String.t()`
- `decode(String.t()) :: {:ok, Cure.Core.Term.t()} | {:error, term()}`

**Round-trip contract:** for every well-formed Core term `t`,
`decode(encode(t)) == {:ok, t}`. This is the load-bearing invariant (§7 test 1).

### 3.1 Grammar (tagged, one former per parenthesized node)

Leaves inside a node are either **integers** (de Bruijn index / universe level /
int literal) or **atom names** (constructor / global / data / primitive-op /
branch-constructor names). Every former keeps an explicit head tag so decode is
**menu-independent** and unambiguous:

| Former (Core tuple) | s-expression |
|---|---|
| `{:var, k}` | `(var k)` |
| `{:type, l}` | `(type l)` |
| `{:global, n}` | `(global n)` |
| `{:ctor, n, args}` | `(ctor n arg…)` |
| `{:data, n, params, indices}` | `(data n (param…) (index…))` |
| `{:app, f, a}` | `(app f a)` |
| `{:lam, dom, body}` | `(lam dom body)` |
| `{:pi, dom, cod}` | `(pi dom cod)` |
| `{:sigma, a, b}` | `(sigma a b)` |
| `{:pair, a, b}` | `(pair a b)` |
| `{:fst, p}` / `{:snd, p}` | `(fst p)` / `(snd p)` |
| `{:case, s, m, brs}` | `(case s m ((cname arity body)…))` |
| `{:eq, ty, a, b}` | `(eq ty a b)` |
| `{:refl, a}` | `(refl a)` |
| `{:rewrite, p, m, b}` | `(rewrite p m b)` |
| `{:prim, op, args}` | `(prim op (arg…))` |
| primitive literals | `(int_type)`, `(int_lit n)`, `(bool_type)`, `(bool_lit true\|false)`, `(float_type)`, `(float_lit f)` |

> The exact former set is **defined by `Cure.Core.Term`**, not by this table —
> Stage 2 (plan) must enumerate the live formers from the source of truth
> (`lib/cure/core/term.ex` and/or `Term.term?/1`'s accepted shapes) and cover
> **every** one, so an unlisted former is a plan bug, not a silent
> passthrough. `encode/1` MUST raise on an unrecognized shape (never emit a
> lossy or ambiguous form); `decode/1` MUST return `{:error, _}` on an
> unrecognized head (never mint a wrong term). Round-trip coverage (§7 test 1)
> enumerates the full former set from that source.

### 3.2 Printer

Recursive descent over the tuple. Names printed with `Atom.to_string/1`.
Integers printed decimally. Nested nodes separated by single spaces. No
pretty-print line-wrapping — a piece is one line (the record is one line).

### 3.3 Parser

Tokenizer → recursive-descent reader.

- **Tokens:** `(`, `)`, and atoms (maximal runs of non-paren, non-whitespace
  chars). Whitespace between tokens is insignificant.
- **Atom classification at a leaf:** an all-digits (optionally leading `-`)
  token is an integer; `true`/`false` inside a `bool_lit` are booleans;
  a float token (contains `.`) inside `float_lit` is a float; otherwise it is a
  **name**, interned with `String.to_existing_atom/1`.
- **Atom safety:** names use `String.to_existing_atom/1` — a name not already
  interned yields `{:error, {:unknown_atom, s}}` (rescued from the raised
  `ArgumentError`), never minting. This is safe: every name a v1 corpus can
  contain is a menu constructor/global/data/op name already interned via
  `Challenge.@known_atoms` (the corpus decode path already force-interns them —
  see `Corpus.decode_record`). Decode MUST force `Challenge.__known_atoms__()`
  before parsing, exactly as `decode_record` does today.
- **Errors:** unbalanced parens, unexpected EOF, a head tag not in §3.1, or an
  arity mismatch (e.g. `(app f)` with one child) → `{:error, reason}`. Never
  raise out of `decode/1`; wrap in `{:error, _}`.

### 3.4 Fault codec

The fault assoc-list (§2.3) reuses the same tokenizer. `encode_fault(map) ::
String.t()` emits `((key val)…)` with a **fixed key order** (sorted by key atom,
so output is deterministic). Values: atom → name, integer → digits, `nil` →
`nil`, list-of-atom → `(a b c)`. `decode_fault(str) :: {:ok, map} | {:error, _}`
inverts it; keys and atom values via `String.to_existing_atom/1`; `nil`→`nil`;
a parenthesized group → list. Fault keys (`kind`, `witness`, `expected_head`,
`injected_head`, `scope`, `depth`, `wrap_path`, plus the deep/conv fields
`wrap_path`/`carrier`/`reduction`/…) are all in `@known_atoms` already.

> **Value-type ambiguity note:** `nil` as an atom value vs. a name literally
> spelled `nil` — the fault schema never uses a name `nil` except as the
> genuine `nil` sentinel (`scope: nil`), so decoding the bare token `nil` to
> Elixir `nil` is correct for this schema. Documented as a fault-schema
> assumption, not a general s-expression rule.

## 4. `Antigen.Corpus` changes

All format changes live here (plus the new module); **`Challenge` is
untouched** — see §5.

### 4.1 Encode (`encode_record/2`)

- **pieces:** `"#{id}::#{SExpr.encode(t)}"` instead of the Base64 form.
- **note:** `enc_note(c.note)` — `nil`→`"-"`, else percent-escaped plaintext.
- **fault:** pop `"fault"` out of the scaffold map before Base64; if present,
  emit a `fault=#{SExpr.encode_fault(fault)}` field and Base64 only the
  remaining scaffold. Field order: `…scaffold=…\tfault=…\tkey=…\tpieces=…`
  (fault present only when the popped value is non-nil).
- **key:** unchanged (Base64).

### 4.2 Decode (`decode_record/1`) — dual-read

- **pieces (per piece):** if the body after `::` starts with `(` →
  `SExpr.decode`; else legacy `Serialize.decode(Base.decode64!(body))`.
  (Unambiguous: Base64's alphabet `A–Za–z0–9+/=` never starts with `(`.)
- **note:** if the value looks percent-escaped/plaintext, `dec_note`; a legacy
  Base64 note decodes to itself as text — acceptable (note is cosmetic, and the
  migrated file has no legacy notes). Concretely: new reader always treats
  `note=` as escaped-plaintext (`dec_note`); a legacy record read before
  migration shows its note as the raw Base64 string (harmless, non-load-bearing).
- **fault:** if a `fault=` field is present, `SExpr.decode_fault` → merge into
  the reconstructed scaffold map as `scaffold["fault"]`; else the fault is read
  from the (legacy) Base64 scaffold as today. Either way `from_pieces` sees
  `scaffold["fault"]` and is unchanged.
- Force `Challenge.__known_atoms__()` first (already done today).

### 4.3 `dedup_key/2` unchanged

`dedup_key(_, :antibody)` uses `Serialize.encode(t)` (binary) — **independent of
display format**. So dedup identity, `seen?`, and the `key=` field are all
stable across the format change: a migrated seed has the **same** dedup key as
before. This is what makes migration lossless (§7 test 5).

## 5. `Antigen.Challenge` — no change

Because the fault is relocated at the Corpus layer (pop-on-encode /
merge-into-scaffold-on-decode), `Challenge.to_pieces/1` and
`Challenge.from_pieces/7` need **no modification** — `to_pieces(:mutant_term)`
still emits `scaffold["fault"]`, and `Corpus.encode_record` pops it out for the
readable field; `from_pieces(:mutant_term)` still reads `scaffold["fault"]`,
which `decode_record` has merged back. Keeping `Challenge` untouched minimizes
blast radius and keeps the per-kind reconstruction logic in one place.

## 6. Migration

A one-time migration rewrites the committed `test/antigen/seeds.sexp` from the
old Base64 form to the new readable form.

- **Mechanism:** stream the existing file through `Corpus.decode_record`
  (reads legacy Base64), then re-serialize each challenge through the new
  `Corpus.encode_record` (writes readable), preserving the **exact** stored
  dedup key (decode the legacy `key=` field and pass it verbatim to
  `encode_record/2`, so `key=` is byte-identical). Write to a temp file, then
  atomically replace.
- **Delivered as:** a small `Mix.Tasks.Antigen.Migrate` task (or a checked-in
  one-shot script under `test/support/`), run once during Stage 4, and the
  migrated `seeds.sexp` is committed. The task is idempotent (re-running on an
  already-migrated file is a no-op-equivalent: decode reads s-expr, re-encode
  writes the same s-expr).
- **Safety:** because §4.3 guarantees dedup-key stability, the migrated file has
  the same record identities in the same order; the static replay meta-tests
  (`mutation_meta`, `conversion`, `corpus_replay`) must stay green unchanged.

### 6.1 Edge case — note `"-"`

A genuine note equal to `"-"` would otherwise be indistinguishable from the nil
sentinel. Rule: the bare token `-` is reserved for nil; `enc_note` escapes a
real note of exactly `"-"` to `%2D`. Decode: `-` → nil; anything else →
percent-unescape. Costs one extra escape rule. (The v1 corpus notes are all
human sentences, so this path is defensive, not currently exercised by real
data — but it keeps the codec total.)

## 7. Testing (TDD, per Stage 4)

1. **SExpr round-trip (load-bearing):** enumerate **every** Core former from the
   source of truth; assert `decode(encode(t)) == {:ok, t}` for each, plus a
   deep nested composite (a `case` with binder branches, a `pi`, a `data` with
   indices, a `plus`-headed `Vec` index). RED first (module absent).
2. **SExpr atom-safety:** `decode("(global no_such_name_xyz)")` →
   `{:error, {:unknown_atom, _}}`, and the atom is **not** minted
   (`assert_raise ArgumentError, fn -> String.to_existing_atom("no_such_name_xyz") end`
   still raises afterwards). Malformed input (`"(app f"`, `"()"`, `"(bogus 1)"`)
   → `{:error, _}`, never raises.
3. **Corpus record round-trip (new format):** `encode_record |> decode_record ==
   {:ok, challenge}` for a `typed_term`, a `mutant_term` (asserts the
   `fault=` field is present and the fault map survives), and a non-term kind
   (`family`/positivity — pieces round-trip, no `fault=`).
4. **Dual-read legacy:** a **hand-written legacy record** (Base64 pieces +
   fault-in-scaffold, Base64 note) still `decode_record`s to the correct
   challenge, incl. the fault. Guards backward compatibility.
5. **Migration lossless:** run the migration on a fixture built from N banked
   challenges; assert (a) every migrated record decodes, (b) the multiset of
   dedup keys is identical pre/post, (c) the decoded challenges equal the
   originals, (d) re-running migration is idempotent (byte-identical output).
6. **Readability smoke:** encode a `mutant_term`; assert the line contains a
   plaintext `note=` (not Base64), a `pieces=…(ctor …)` s-expr, and a readable
   `fault=((kind …)…)`, and that **none** of the `note`/`pieces`/`fault` field
   values match a "looks-like-Base64" pattern.
7. **Full suite once** (Stage 5): all green, including the existing
   `architecture_test` quarantine (SExpr is outside `generators/`/`assays/`, so
   no `StreamData` literal concern) and the static replay meta-tests against the
   migrated `seeds.sexp`.

## 8. Files

- **Create:** `lib/antigen/sexpr.ex`, `test/antigen/sexpr_test.exs`.
- **Modify:** `lib/antigen/corpus.ex` (pieces/note/fault encode+decode, dual-read),
  `test/antigen/corpus_test.exs` (or the existing corpus test file — Stage 2
  locates it) for record-level tests.
- **Migrate + commit:** `test/antigen/seeds.sexp`.
- **Migration harness:** `lib/mix/tasks/antigen.migrate.ex` **or**
  `test/support/seeds_migrate.exs` (Stage 2 picks; a Mix task is preferred so
  it is rerunnable and discoverable).
- **Untouched:** `lib/antigen/challenge.ex`, `lib/cure/core/serialize.ex`
  (Serialize still backs dedup keys), all generators/assays.

## 9. Non-goals (YAGNI)

- Recovering variable **names** — positional de Bruijn stays; documented in the
  `SExpr` moduledoc.
- Making the non-fault **scaffold** or the dedup **key** readable.
- A **surface-syntax** parser (this is a Core-term codec, not Cure source).
- Changing the `Serialize` **binary** format — it still backs dedup keys and the
  legacy read path.
- A pretty-printer / multi-line layout — one piece, one line.
- ChoiceSeq / shrinking (separate, already shipped/shelved).

## 10. Risks

- **Missed former:** if a Core former is absent from the printer, `encode`
  raises at generation/bank time. Mitigation: §7 test 1 enumerates the former
  set from the source of truth; a missed former fails the round-trip test in
  RED, not in production.
- **Atom minting via the parser:** mitigated by `String.to_existing_atom` +
  the forced `__known_atoms__()` intern (§3.3), tested in §7 test 2.
- **Migration divergence:** mitigated by dedup-key stability (§4.3) + §7 test 5
  asserting key-multiset equality and idempotency.
- **Delimiter collision:** an s-expr containing `;;`/`::`/tab would corrupt a
  record. It cannot: names are atoms (no such chars), structure is parens and
  single spaces. Asserted implicitly by round-trip through `decode_record`
  (which splits on those delimiters) in §7 test 3.
