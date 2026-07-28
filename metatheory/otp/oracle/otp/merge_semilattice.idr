%default total

data Tag = TA | TB | TC
data Branches = BNil | BCons Tag Branches

data InB : Tag -> Branches -> Type where
  InHead : InB x (BCons x rest)
  InTail : InB x rest -> InB x (BCons y rest)

data Covers : Branches -> Branches -> Type where
  CovNil  : Covers big BNil
  CovCons : InB x big -> Covers big rest -> Covers big (BCons x rest)

bappend : Branches -> Branches -> Branches
bappend BNil t = t
bappend (BCons x rest) t = BCons x (bappend rest t)

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

covers_glb : Covers z s -> Covers z t -> Covers z (bappend s t)
covers_glb CovNil ct = ct
covers_glb (CovCons inx cs2) ct = CovCons inx (covers_glb cs2 ct)

merge_lower_l : (s : Branches) -> (t : Branches) -> Covers (bappend s t) s
merge_lower_l BNil t = CovNil
merge_lower_l (BCons x rest) t = CovCons InHead (covers_weaken x (merge_lower_l rest t))

merge_lower_r : (s : Branches) -> (t : Branches) -> Covers (bappend s t) t
merge_lower_r BNil t = covers_refl t
merge_lower_r (BCons x rest) t = covers_weaken x (merge_lower_r rest t)

data Equiv : Branches -> Branches -> Type where
  MkEquiv : Covers a b -> Covers b a -> Equiv a b

merge_comm : (s : Branches) -> (t : Branches) -> Equiv (bappend s t) (bappend t s)
merge_comm s t = MkEquiv (covers_glb (merge_lower_r s t) (merge_lower_l s t)) (covers_glb (merge_lower_r t s) (merge_lower_l t s))

merge_idem : (s : Branches) -> Equiv (bappend s s) s
merge_idem s = MkEquiv (merge_lower_l s s) (covers_glb (covers_refl s) (covers_refl s))

merge_assoc : (s : Branches) -> (t : Branches) -> (u : Branches) -> Equiv (bappend (bappend s t) u) (bappend s (bappend t u))
merge_assoc s t u = MkEquiv
  (covers_glb
    (covers_trans (merge_lower_l (bappend s t) u) (merge_lower_l s t))
    (covers_glb (covers_trans (merge_lower_l (bappend s t) u) (merge_lower_r s t)) (merge_lower_r (bappend s t) u)))
  (covers_glb
    (covers_glb (merge_lower_l s (bappend t u)) (covers_trans (merge_lower_r s (bappend t u)) (merge_lower_l t u)))
    (covers_trans (merge_lower_r s (bappend t u)) (merge_lower_r t u)))
