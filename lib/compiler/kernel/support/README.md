# Kernel Support

This folder contains small data-structure helpers needed by the kernel.

Use the simplest Cure implementation that preserves the contracts expected by
the Lean-shaped core. These files are support code, not language design.

## References

- Lean list/name helpers: `../reference/lean4/src/util/`
- Lean kernel containers and maps: usages in
  `../reference/lean4/src/kernel/*.h`
- Idris utility style may be consulted for ergonomic list/result helpers:
  `../reference/idris2/src/Core/`

Keep these modules small and deterministic. They should not introduce
elaboration behavior or trusted typing rules.

