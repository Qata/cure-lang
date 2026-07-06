# Compiler

This tree is the bootstrapped Cure compiler implementation.

Reference paths below are written relative to the repository root
(`cure-lang/`). The read-only reference checkout lives at `../reference`.

## Copy Boundary

- Copy Lean 4 for the trusted kernel core and declaration admission.
- Copy Idris 2 for surface-language elaboration, erasure, code generation, and
  programmer-facing behavior.
- Use Agda as a cross-check for dependent pattern matching, coverage,
  positivity, and termination algorithms.

Do not mix these layers casually. If a file is part of the trusted kernel
representation or validation, start from Lean.

## Primary References

- Lean kernel core: `../reference/lean4/src/kernel/`
- Lean environment/declarations: `../reference/lean4/src/kernel/declaration.{h,cpp}`,
  `../reference/lean4/src/kernel/environment.{h,cpp}`
- Lean expression/level core: `../reference/lean4/src/kernel/expr.{h,cpp}`,
  `../reference/lean4/src/kernel/level.{h,cpp}`
- Idris programming-language pipeline: `../reference/idris2/src/Core/`,
  `../reference/idris2/src/TTImp/`, `../reference/idris2/src/Compiler/`
- Agda dependent-pattern machinery: `../reference/agda/src/full/Agda/TypeChecking/`

