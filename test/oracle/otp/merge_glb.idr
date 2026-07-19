%default total

data Tag = TA | TB | TC
data Branches = BNil | BCons Tag Branches
data Local = LB Branches

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

data Sub : Local -> Local -> Type where
  SubB : Covers s t -> Sub (LB s) (LB t)

merge : Local -> Local -> Local
merge (LB s) (LB t) = LB (bappend s t)

merge_lower_l : (s : Branches) -> (t : Branches) -> Covers (bappend s t) s
merge_lower_l BNil t = CovNil
merge_lower_l (BCons x rest) t = CovCons InHead (covers_weaken x (merge_lower_l rest t))

merge_lower_r : (s : Branches) -> (t : Branches) -> Covers (bappend s t) t
merge_lower_r BNil t = covers_refl t
merge_lower_r (BCons x rest) t = covers_weaken x (merge_lower_r rest t)

merge_sub_l : (s : Branches) -> (t : Branches) -> Sub (merge (LB s) (LB t)) (LB s)
merge_sub_l s t = SubB (merge_lower_l s t)

merge_sub_r : (s : Branches) -> (t : Branches) -> Sub (merge (LB s) (LB t)) (LB t)
merge_sub_r s t = SubB (merge_lower_r s t)

covers_glb : Covers z s -> Covers z t -> Covers z (bappend s t)
covers_glb CovNil ct = ct
covers_glb (CovCons inx cs2) ct = CovCons inx (covers_glb cs2 ct)

merge_greatest : Sub (LB z) (LB s) -> Sub (LB z) (LB t) -> Sub (LB z) (merge (LB s) (LB t))
merge_greatest (SubB cs) (SubB ct) = SubB (covers_glb cs ct)
