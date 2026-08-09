# Compiler performance baselines

These measurements cover complete checks through the canonical module pipeline.
They are diagnostic baselines, not CI timeouts: compare like-for-like hardware
and investigate a repeatable result outside the tolerant band before treating
it as a regression.

## Reproduce

```sh
MIX_ENV=test mix cure.bench.interfaces --warm-iterations 3
```

The cold sample starts without a checked-interface cache. Each warm sample runs
the identical source universe against the cache published by the preceding run.
The report includes exact rebuilt-module lists, top-level phase timings, SCC
component timings, and the slowest declaration/stage timings. The CLI prints
the top 20 entries in each ranking by default; use `--top N` to change that
without discarding the complete timing lists retained by the benchmark API. A
warm sample is cache evidence only when `rebuilt=0`.

Pass an explicit list of files only when it is a dependency-complete compilation
universe. A lone module that imports another source is intentionally rejected by
the canonical graph unless its dependency interface is supplied by the caller.

## 2026-08-09 canonical-pipeline baseline

Environment: Apple M1 Pro, macOS arm64, Erlang/OTP 29, Elixir 1.20.1.

| Measurement | Baseline | Investigation band |
|---|---:|---:|
| all 75 sources, cold total | 54.629 s | 27–110 s |
| cold manifest | 0.376 s | 0.2–0.8 s |
| cold expansion | 6.649 s | 3–14 s |
| cold module checking | 47.536 s | 24–96 s |
| all 75 sources, warm total | 3.211 s | 1.5–7 s |
| warm expansion | 2.642 s | 1.2–5.5 s |
| warm module checking | 0.244 s | 0.1–0.6 s |

The cold run rebuilt all 75 modules; the warm run rebuilt none. The dominant
cold component was `Std.Actor` at 36.121 s, followed by `Std.Bool` at 3.886 s,
`Std.Regex` at 1.661 s, and `Std.Fsm` at 0.671 s. The legal
`Std.Char`/`Std.Literal`/`Std.String` cycle is reported as one SCC component.

`Std.Actor` is therefore the first candidate for measured decomposition. A
split should preserve an acyclic module boundary and must be benchmarked again;
source line count alone is not sufficient justification.

For comparison, before shape-directed zonking and canonical-name interning, the
same cold check measured 93.402 s with `Std.Actor` at 71.349 s. Those numbers are
diagnostic evidence from the same machine, not a second supported baseline.

## 2026-08-10 declaration-stage profile

On the same machine, a cold run after adding declaration-stage timing measured
41.193 s overall, with `Std.Actor` accounting for 33.110 s. A no-rebuild warm
sample measured 1.351 s. The dominant declarations and their typed-elaboration
times were:

| Declaration | Typed elaboration |
|---|---:|
| `emit_actor_dep_call_parts` | 7.590 s |
| `derive_behavior_family` | 7.455 s |
| `emit_actor_call_parts` | 6.913 s |
| `emit_actor_parts_poly` | 3.322 s |
| `emit_actor_parts_aliased_raw` | 2.679 s |
| `emit_actor_parts_aliased` | 2.525 s |

The parsed `Std.Actor` body contains hundreds, not millions, of authored calls;
profiling therefore identifies repeated typed elaboration as the remaining
cost, rather than parsing, expansion size, interface publication, or totality
certification. This profile is the baseline for the next elaborator change.

## Focused test startup

Test VMs publish through the shared `_build/cure/test/ebin` root. Publication
itself is lock-serialized and each generation beneath that root is immutable and
content-addressed, so separate Mix VMs safely reuse the same checked interfaces
instead of rebuilding into PID-specific directories.

After one cold publication, the command

```sh
MIX_ENV=test mix test test/cure/diagnostic/host_test.exs:229
```

reported `0 compiled, 75 up-to-date`; the full command completed in
approximately 11 seconds and the selected test itself in 0.4 seconds. Before
the shared publication root, every focused invocation rebuilt all 75 modules
and spent roughly 54 seconds in the canonical stdlib check. The cross-process
isolation regression runs two OS VMs against one publication root and verifies
that both resolve the same complete immutable generation.
