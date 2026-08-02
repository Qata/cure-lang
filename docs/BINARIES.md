# Binaries

Reference guide for Cure's binary literal and pattern syntax.
Introduced in v0.20.0 (segment AST, codegen, printer) and completed
in v0.21.0 (type-checker bindings, exhaustiveness via `E031`).

## Syntax

A binary literal is written between `<<` and `>>`, with segments
separated by commas. Every segment has the shape:

```
value [:: specifier_chain]
```

The specifier chain is a hyphen-joined list of specifiers (mirroring
Elixir's grammar):

- **Type**: `integer`, `float`, `bits`, `bitstring`, `bytes`, `binary`,
  `utf8`, `utf16`, `utf32`.
- **Signedness**: `signed`, `unsigned`.
- **Endianness**: `big`, `little`, `native`.
- **Size**: `size(expr)`. A bare integer specifier is shorthand for
  `size(<integer>)`.
- **Unit**: `unit(n)`.

Defaults mirror Erlang: `integer-unsigned-big-size(8)-unit(1)`; the
`utf8`, `utf16`, and `utf32` types carry their own implicit size.

## Examples

```cure
fn first_byte(buf: Binary) -> Int =
  match buf
    <<b, _rest::binary>> -> b
    <<>> -> 0
    _ -> 0
```

## Pattern positions

Binary patterns work in every destructuring position:

1. `match` arms.
2. Multi-clause function heads: `fn parse(buf: Bitstring) -> Int | <<a, _rest::binary>> -> a | <<>> -> 0`.
3. `let` bindings: `let <<tag, body::binary>> = buf`.

Comprehension generators with a binary source (`for <<b <- buf>>`)
are reserved for a future release.

## Type-checker semantics

The dependent elaborator assigns every binary segment's inner variable the
type implied by the segment specifier:

| Specifier type        | Bound variable type |
| --------------------- | ------------------- |
| `integer` (default)   | `Int`               |
| `float`               | `Float`             |
| `utf8` / `utf16` / `utf32` | `Char` (code point) |
| `binary` / `bytes` / `bitstring` / `bits` | `Bitstring` |

Where the checker can prove a byte-size refinement on the
scrutinee, it propagates the narrowing through the segments. The
v0.21.0 propagation is conservative: a trailing `rest::binary` binds
to plain `Bitstring`. Future releases will emit
`byte_size(rest) == byte_size(scrutinee) - sum_of_preceding_sizes`
once the SMT translator gains the corresponding arithmetic.

## Exhaustiveness

The dependent coverage checker runs
whenever the scrutinee of a `match` is a `Bitstring` (or a
`Bitstring` refinement). It reports `E031` when a set of arms does
not cover every inhabitant:

- A top-level wildcard (variable binding) covers everything.
- A binary pattern whose last segment is an open-ended tail
  (`::binary`, `::bits`, `::bitstring`, `::bytes` with no `:size`)
  covers every non-empty suffix.
- The empty binary `<<>>` covers the zero-byte case.

A set of arms is exhaustive if at least one arm is a wildcard, or
if both the empty and open-tail cases are covered. Otherwise the
compiler prints a concrete witness such as `"<<>>"` or
`"<<_, _rest::binary>>"`.

## Codegen

Binary patterns lower directly to Erlang's `:bin_element` form.
Construction uses the same AST shape as patterns, so
`<<x::utf8, rest::binary>>` emits a matching binary with the
correct size/type/unit/sign/endian tuples.

See also: `docs/PATTERNS.md` for the broader destructuring
reference and `docs/LANGUAGE_SPEC.md` for the full grammar.
