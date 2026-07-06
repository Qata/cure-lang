# Inductives

This folder handles inductive declarations, positivity, coverage, and recursor
generation.

Final declaration shape and kernel admission should follow Lean. Dependent
pattern and coverage algorithms should be checked against Agda. Programming
ergonomics and generated code behavior should be checked against Idris.

## Lean References

- Kernel inductive declarations:
  `../reference/lean4/src/kernel/inductive.h`,
  `../reference/lean4/src/kernel/inductive.cpp`
- Declaration payloads:
  `../reference/lean4/src/kernel/declaration.h`,
  `../reference/lean4/src/kernel/declaration.cpp`
- Type checker admission:
  `../reference/lean4/src/kernel/type_checker.cpp`

## Agda References

- Positivity: `../reference/agda/src/full/Agda/TypeChecking/Positivity.hs`,
  `../reference/agda/src/full/Agda/TypeChecking/Positivity/Occurrence.hs`
- Coverage: `../reference/agda/src/full/Agda/TypeChecking/Coverage.hs`,
  `../reference/agda/src/full/Agda/TypeChecking/Coverage/SplitClause.hs`,
  `../reference/agda/src/full/Agda/TypeChecking/Coverage/SplitTree.hs`
- Datatypes: `../reference/agda/src/full/Agda/TypeChecking/Datatypes.hs`

## Idris References

- Data processing: `../reference/idris2/src/TTImp/ProcessData.idr`
- Totality and termination:
  `../reference/idris2/src/Core/Termination.idr`

