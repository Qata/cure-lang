# Cure proof probes — committed scratch

Exploratory `.cure` proofs, **committed** so they survive a reboot (never `/tmp`). This is the
staging area between an idea and a shipped `lib/std/otp_*.cure` module: prove it here against the
elaborator (and, once it holds, the Idris oracle), then promote it to `lib/std/` with an oracle
pair + test.

Distinct from the sibling `../scaffolds/` folder, which holds *holed* (`?name`) design sketches
that intentionally do not codegen. Probes here are meant to elaborate cleanly (or to pin a
known rejection, noted in a comment).

## Running a probe

```
mix run --no-start docs/research/process-types/probes/check.exs docs/research/process-types/probes/<file>.cure
```

`check.exs` elaborates the file via `Cure.Elab.Program.elaborate/1` and prints `ACCEPT` or
`REJECT <reason>`. A probe whose header comment says `# EXPECT: reject …` documents a deliberate
negative.

## Promotion checklist (probe → shipped)

1. Probe elaborates clean here.
2. Mirror the core lemmas into an Idris oracle pair under `test/oracle/otp/`; `mix cure.oracle otp`
   shows `rel=same`.
3. Write the module into `lib/std/otp_<name>.cure` (`@group(:concurrency)`), add a
   `test/cure/stdlib/otp_<name>_test.exs`.
4. Leave the probe here (history value) or delete if fully subsumed by the shipped module.
