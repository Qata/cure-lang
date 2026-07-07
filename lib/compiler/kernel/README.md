# Kernel

This directory is the trusted kernel boundary for the bootstrapped compiler.

Migration note: this Cure-written Lean-shaped kernel is now reference/prototype
code. Production dependent-module checking should route through
`Cure.Kernel.Backend` and, once translation coverage exists, the Lean bridge.
Keep fixes here limited to existing regression/reference tests unless the
migration plan is explicitly revised.

The kernel should be Lean-shaped unless a file README says otherwise. Lean is
the primary reference because its kernel is intentionally small and centered on
checking closed declarations before they enter the environment.

## Copy From Lean

- Expressions: `../reference/lean4/src/kernel/expr.h`,
  `../reference/lean4/src/kernel/expr.cpp`
- Universe levels: `../reference/lean4/src/kernel/level.h`,
  `../reference/lean4/src/kernel/level.cpp`
- Declarations: `../reference/lean4/src/kernel/declaration.h`,
  `../reference/lean4/src/kernel/declaration.cpp`
- Environments: `../reference/lean4/src/kernel/environment.h`,
  `../reference/lean4/src/kernel/environment.cpp`
- Type checking and definitional equality:
  `../reference/lean4/src/kernel/type_checker.h`,
  `../reference/lean4/src/kernel/type_checker.cpp`
- Instantiation and abstraction:
  `../reference/lean4/src/kernel/instantiate.{h,cpp}`,
  `../reference/lean4/src/kernel/abstract.{h,cpp}`
- Local contexts: `../reference/lean4/src/kernel/local_ctx.{h,cpp}`
- Inductives: `../reference/lean4/src/kernel/inductive.{h,cpp}`

## Cross-Checks

- Idris core terms and binders:
  `../reference/idris2/src/Core/TT.idr`,
  `../reference/idris2/src/Core/TT/Term.idr`,
  `../reference/idris2/src/Core/TT/Binder.idr`
- Agda internal syntax:
  `../reference/agda/src/full/Agda/Syntax/Internal.hs`
