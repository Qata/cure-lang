# Lean Kernel Core

This folder mirrors Lean 4 kernel syntax and trusted kernel data. Do not add
Agda-only or Idris-only syntax here.

## Source Files

- `name.cure`: `reference/lean4/src/Init/Meta/Defs.lean`,
  `reference/lean4/src/Init/Data/ToString/Name.lean`
- `level.cure`: `reference/lean4/src/kernel/level.h`
- `literal.cure`, `expr.cure`: `reference/lean4/src/kernel/expr.h`
- `syntax.cure`: `reference/lean4/src/Init/Prelude.lean`
  (`SourceInfo`, `Syntax.Preresolved`, `Syntax`),
  `reference/lean4/src/Lean/Data/KVMap.lean`
- `local_context.cure`: `reference/lean4/src/kernel/local_ctx.h`
- `declaration.cure`: `reference/lean4/src/kernel/declaration.h`
- `environment.cure`: `reference/lean4/src/kernel/environment.h`,
  `reference/lean4/src/Lean/Environment.lean`
- `exception.cure`: `reference/lean4/src/kernel/kernel_exception.h`,
  `reference/lean4/src/Lean/Environment.lean`
- `type_checker.cure`: `reference/lean4/src/kernel/type_checker.h`,
  `reference/lean4/src/Lean/Environment.lean`

## Boundary

Lean kernel core consists of names, universe levels, expressions, local
contexts, declarations, constant information, environments, exceptions, and
type-checker operations. Pattern matching coverage, elaboration constraints,
surface syntax, erasure, and code generation belong outside this folder.
