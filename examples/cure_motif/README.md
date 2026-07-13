# cure_motif

A dependent-data example with transparent Cure process modules.

The project combines length-indexed values, ordinary ADTs, and the four
standard-library macro surfaces. Its process declarations are intentionally
small floors while the domain code remains pure Cure.

## Quick start

```bash
cd examples/cure_motif
mix deps.get
mix test
```

## Transparent process declarations

The source files use standard-library syntax directly:

```cure
fsm Cure.Envelope with 0
  fn initial_state() -> Atom = :silent

actor Cure.Voice with 0

sup Cure.Motif.Orchestra

app Cure.CureMotif
```

Each form expands recursively to a checked `lift module`. `beam_ops` and the
typed `Std.Otp` aliases provide the process algebra; the compiler only sees
ordinary parsed Cure declarations and a generic lifted-module request.

## Domain focus

`motif.cure` contains the MIDI-domain aliases, ADTs, and pure rendering
functions. `Std.Vector` supplies the length-indexed family used by the domain
tests. The Elixir piano-roll renderer and application harness are conventional
interop code around the generated modules.

## Current boundary

The transparent floor does not silently recreate the retired transition,
lifecycle, or decorator parser. Add those capabilities as Cure macros over the
checked transition and BEAM algebra when the corresponding source vocabulary is
needed.
