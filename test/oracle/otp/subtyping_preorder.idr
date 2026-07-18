%default total

data Tag = TA | TB | TC
data Branches = BNil | BCons Tag Branches

data InB : Tag -> Branches -> Type where
  InHead : InB x (BCons x rest)
  InTail : InB x rest -> InB x (BCons y rest)

data Covers : Branches -> Branches -> Type where
  CovNil  : Covers big BNil
  CovCons : InB x big -> Covers big rest -> Covers big (BCons x rest)

covers_weaken : (y : Tag) -> Covers big small -> Covers (BCons y big) small
covers_weaken y CovNil = CovNil
covers_weaken y (CovCons inx w2) = CovCons (InTail inx) (covers_weaken y w2)

covers_refl : (bs : Branches) -> Covers bs bs
covers_refl BNil = CovNil
covers_refl (BCons x rest) = CovCons InHead (covers_weaken x (covers_refl rest))

covers_mem : Covers big small -> InB x small -> InB x big
covers_mem (CovCons inx cov2) InHead = inx
covers_mem (CovCons inx cov2) (InTail in2) = covers_mem cov2 in2

covers_trans : Covers a b -> Covers b c -> Covers a c
covers_trans ab CovNil = CovNil
covers_trans ab (CovCons inx bc2) = CovCons (covers_mem ab inx) (covers_trans ab bc2)
