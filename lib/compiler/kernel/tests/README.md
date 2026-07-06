# Kernel Tests

Kernel tests should pin behavior against the chosen reference boundary.

## Test Policy

- Core data-shape tests should assert Lean-shaped constructors and invariants.
- Elaboration tests should assert Idris-style user-facing behavior lowers into
  the Lean-shaped core.
- Inductive, coverage, and positivity tests should include Agda cross-check
  cases where the algorithmic behavior is subtle.

## References

- Lean kernel tests/examples: inspect usages around
  `../reference/lean4/src/kernel/`
- Idris regression-style examples:
  `../reference/idris2/src/TTImp/`, `../reference/idris2/src/Core/`
- Agda coverage/positivity cases:
  `../reference/agda/src/full/Agda/TypeChecking/Coverage*`,
  `../reference/agda/src/full/Agda/TypeChecking/Positivity*`

