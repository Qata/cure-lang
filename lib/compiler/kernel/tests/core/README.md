# Core Tests

Tests in this folder target `compiler/kernel/core`.

Use Lean as the expected shape:

- levels: `../reference/lean4/src/kernel/level.{h,cpp}`
- expressions: `../reference/lean4/src/kernel/expr.{h,cpp}`
- local contexts: `../reference/lean4/src/kernel/local_ctx.{h,cpp}`
- declarations: `../reference/lean4/src/kernel/declaration.{h,cpp}`
- environments: `../reference/lean4/src/kernel/environment.{h,cpp}`
- validation/type checking: `../reference/lean4/src/kernel/type_checker.{h,cpp}`

Do not write tests that depend on Agda-only internal syntax for core terms.
Agda belongs in inductive/pattern/coverage cross-check tests.

