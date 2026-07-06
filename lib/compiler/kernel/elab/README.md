# Elaboration

This folder is outside the trusted kernel. Copy Idris 2 first.

Elaboration turns programmer-facing Cure syntax into the Lean-shaped kernel
core. It may use metas, constraints, implicit insertion, and hole reporting,
but the final result must be validated by `kernel/core/validate.cure`.

## Authoritative Idris Files

- Elaboration driver: `../reference/idris2/src/TTImp/Elab.idr`
- Surface syntax: `../reference/idris2/src/TTImp/TTImp.idr`
- Declaration processing: `../reference/idris2/src/TTImp/ProcessDecls.idr`,
  `../reference/idris2/src/TTImp/ProcessDef.idr`,
  `../reference/idris2/src/TTImp/ProcessData.idr`,
  `../reference/idris2/src/TTImp/ProcessType.idr`
- Core unification: `../reference/idris2/src/Core/Unify.idr`,
  `../reference/idris2/src/Core/UnifyState.idr`
- Holes and interactive goals: `../reference/idris2/src/TTImp/Elab/Hole.idr`
  if present in the snapshot; otherwise use surrounding `TTImp/Elab*` files.
- Erasure guidance: `../reference/idris2/src/Core/LinearCheck.idr`,
  `../reference/idris2/src/Compiler/CompileExpr.idr`

## Agda Cross-Checks

- Dependent LHS/unification:
  `../reference/agda/src/full/Agda/TypeChecking/Rules/LHS.hs`,
  `../reference/agda/src/full/Agda/TypeChecking/Rules/LHS/Unify.hs`
- Metavariables:
  `../reference/agda/src/full/Agda/TypeChecking/MetaVars.hs`
- Constraints:
  `../reference/agda/src/full/Agda/TypeChecking/Constraints.hs`

