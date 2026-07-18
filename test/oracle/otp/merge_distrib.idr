%default total

data Tag = TA | TB | TC
data OBit = OF | OT
data Branches = BNil | BCons Tag Branches

teq : Tag -> Tag -> OBit
teq TA TA = OT
teq TA TB = OF
teq TA TC = OF
teq TB TA = OF
teq TB TB = OT
teq TB TC = OF
teq TC TA = OF
teq TC TB = OF
teq TC TC = OT

teq_refl : (a : Tag) -> teq a a = OT
teq_refl TA = Refl
teq_refl TB = Refl
teq_refl TC = Refl

ot_ne_of : OT = OF -> Void
ot_ne_of Refl impossible

data InB : Tag -> Branches -> Type where
  InHead : (x2 : Tag) -> (rest : Branches) -> InB x2 (BCons x2 rest)
  InTail : (y : Tag) -> (rest : Branches) -> InB x2 rest -> InB x2 (BCons y rest)

noInBNil : InB x BNil -> Void
noInBNil (InHead _ _) impossible
noInBNil (InTail _ _ _) impossible

data NotIn : Tag -> Branches -> Type where
  NINil  : NotIn x BNil
  NICons : (y2 : Tag) -> (rest2 : Branches) -> teq x y2 = OF -> NotIn x rest2 -> NotIn x (BCons y2 rest2)

notin_absurd : NotIn x bs -> InB x bs -> Void
notin_absurd (NICons x2 rest tof nx2) (InHead x2 rest) = ot_ne_of (trans (sym (teq_refl x2)) tof)
notin_absurd (NICons z r tof nx2) (InTail z r m2) = notin_absurd nx2 m2

data MemDec : Tag -> Branches -> Type where
  MYes : InB x t -> MemDec x t
  MNo  : NotIn x t -> MemDec x t

mem_dec : (x : Tag) -> (t : Branches) -> MemDec x t
mem_dec x BNil = MNo NINil
mem_dec TA (BCons TA rest) = MYes (InHead TA rest)
mem_dec TA (BCons TB rest) = case mem_dec TA rest of
  MYes pf => MYes (InTail TB rest pf)
  MNo nx => MNo (NICons TB rest Refl nx)
mem_dec TA (BCons TC rest) = case mem_dec TA rest of
  MYes pf => MYes (InTail TC rest pf)
  MNo nx => MNo (NICons TC rest Refl nx)
mem_dec TB (BCons TA rest) = case mem_dec TB rest of
  MYes pf => MYes (InTail TA rest pf)
  MNo nx => MNo (NICons TA rest Refl nx)
mem_dec TB (BCons TB rest) = MYes (InHead TB rest)
mem_dec TB (BCons TC rest) = case mem_dec TB rest of
  MYes pf => MYes (InTail TC rest pf)
  MNo nx => MNo (NICons TC rest Refl nx)
mem_dec TC (BCons TA rest) = case mem_dec TC rest of
  MYes pf => MYes (InTail TA rest pf)
  MNo nx => MNo (NICons TA rest Refl nx)
mem_dec TC (BCons TB rest) = case mem_dec TC rest of
  MYes pf => MYes (InTail TB rest pf)
  MNo nx => MNo (NICons TB rest Refl nx)
mem_dec TC (BCons TC rest) = MYes (InHead TC rest)

mutual
  inter_pick : (x : Tag) -> (t : Branches) -> (rest : Branches) -> MemDec x t -> Branches
  inter_pick x t rest (MYes pf) = BCons x (inter rest t)
  inter_pick x t rest (MNo nx) = inter rest t

  inter : Branches -> Branches -> Branches
  inter BNil t = BNil
  inter (BCons x rest) t = inter_pick x t rest (mem_dec x t)

bappend : Branches -> Branches -> Branches
bappend BNil t = t
bappend (BCons x rest) t = BCons x (bappend rest t)

data Covers : Branches -> Branches -> Type where
  CovNil  : Covers big BNil
  CovCons : InB x big -> Covers big rest -> Covers big (BCons x rest)

covers_weaken : (big : Branches) -> (y : Tag) -> Covers big small -> Covers (BCons y big) small
covers_weaken big y CovNil = CovNil
covers_weaken big y (CovCons inx w2) = CovCons (InTail y big inx) (covers_weaken big y w2)

covers_refl : (bs : Branches) -> Covers bs bs
covers_refl BNil = CovNil
covers_refl (BCons x rest) = CovCons (InHead x rest) (covers_weaken rest x (covers_refl rest))

covers_mem : Covers big small -> InB x small -> InB x big
covers_mem (CovCons inx cov2) (InHead x2 r2) = inx
covers_mem (CovCons inx cov2) (InTail z r m2) = covers_mem cov2 m2

covers_trans : Covers a b -> Covers b c -> Covers a c
covers_trans ab CovNil = CovNil
covers_trans ab (CovCons inx bc2) = CovCons (covers_mem ab inx) (covers_trans ab bc2)

covers_glb : Covers z s -> Covers z t -> Covers z (bappend s t)
covers_glb CovNil ct = ct
covers_glb (CovCons inx cs2) ct = CovCons inx (covers_glb cs2 ct)

merge_lower_l : (s : Branches) -> (t : Branches) -> Covers (bappend s t) s
merge_lower_l BNil t = CovNil
merge_lower_l (BCons x rest) t = CovCons (InHead x (bappend rest t)) (covers_weaken (bappend rest t) x (merge_lower_l rest t))

merge_lower_r : (s : Branches) -> (t : Branches) -> Covers (bappend s t) t
merge_lower_r BNil t = covers_refl t
merge_lower_r (BCons x rest) t = covers_weaken (bappend rest t) x (merge_lower_r rest t)

in_inter : (s : Branches) -> (t : Branches) -> InB x s -> InB x t -> InB x (inter s t)
in_inter BNil t inXs inXt = void (noInBNil inXs)
in_inter (BCons y rest) t inXs inXt with (mem_dec y t)
  in_inter (BCons y rest) t inXs inXt | MYes pf = case inXs of
    InHead x2 r2 => InHead x2 (inter rest t)
    InTail z r m2 => InTail y (inter rest t) (in_inter rest t m2 inXt)
  in_inter (BCons y rest) t inXs inXt | MNo nx = case inXs of
    InHead x2 r2 => void (notin_absurd nx inXt)
    InTail z r m2 => in_inter rest t m2 inXt

inter_mono_r : (s : Branches) -> (t1 : Branches) -> (t2 : Branches) -> Covers t2 t1 -> Covers (inter s t2) (inter s t1)
inter_mono_r BNil t1 t2 sub = CovNil
inter_mono_r (BCons x rest) t1 t2 sub with (mem_dec x t1)
  inter_mono_r (BCons x rest) t1 t2 sub | MYes pf1 with (mem_dec x t2)
    inter_mono_r (BCons x rest) t1 t2 sub | MYes pf1 | MYes pf2 = CovCons (InHead x (inter rest t2)) (covers_weaken (inter rest t2) x (inter_mono_r rest t1 t2 sub))
    inter_mono_r (BCons x rest) t1 t2 sub | MYes pf1 | MNo nx2 = void (notin_absurd nx2 (covers_mem sub pf1))
  inter_mono_r (BCons x rest) t1 t2 sub | MNo nx1 with (mem_dec x t2)
    inter_mono_r (BCons x rest) t1 t2 sub | MNo nx1 | MYes pf2 = covers_weaken (inter rest t2) x (inter_mono_r rest t1 t2 sub)
    inter_mono_r (BCons x rest) t1 t2 sub | MNo nx1 | MNo nx2 = inter_mono_r rest t1 t2 sub

inter_mono_l : (s1 : Branches) -> (s2 : Branches) -> (t : Branches) -> Covers s2 s1 -> Covers (inter s2 t) (inter s1 t)
inter_mono_l BNil s2 t sub = CovNil
inter_mono_l (BCons x rest) s2 t (CovCons inXs2 sub2) with (mem_dec x t)
  inter_mono_l (BCons x rest) s2 t (CovCons inXs2 sub2) | MYes pf = CovCons (in_inter s2 t inXs2 pf) (inter_mono_l rest s2 t sub2)
  inter_mono_l (BCons x rest) s2 t (CovCons inXs2 sub2) | MNo nx = inter_mono_l rest s2 t sub2

union_mono : (a1 : Branches) -> (a2 : Branches) -> (b1 : Branches) -> (b2 : Branches) -> Covers a2 a1 -> Covers b2 b1 -> Covers (bappend a2 b2) (bappend a1 b1)
union_mono a1 a2 b1 b2 subA subB = covers_glb (covers_trans (merge_lower_l a2 b2) subA) (covers_trans (merge_lower_r a2 b2) subB)

data MemOr : Tag -> Branches -> Branches -> Type where
  OrL : InB x a -> MemOr x a b
  OrR : InB x b -> MemOr x a b

in_union_l : (a : Branches) -> (b : Branches) -> InB x a -> InB x (bappend a b)
in_union_l (BCons x2 rest) b (InHead x2 rest) = InHead x2 (bappend rest b)
in_union_l (BCons y rest) b (InTail y rest m2) = InTail y (bappend rest b) (in_union_l rest b m2)

in_union_r : (a : Branches) -> (b : Branches) -> InB x b -> InB x (bappend a b)
in_union_r BNil b m = m
in_union_r (BCons y rest) b m = InTail y (bappend rest b) (in_union_r rest b m)

in_union_split : (a : Branches) -> (b : Branches) -> InB x (bappend a b) -> MemOr x a b
in_union_split BNil b m = OrR m
in_union_split (BCons y rest) b (InHead y _) = OrL (InHead y rest)
in_union_split (BCons y rest) b (InTail y _ m2) = case in_union_split rest b m2 of
  OrL pf => OrL (InTail y rest pf)
  OrR pf => OrR pf

covers_inter_l : (s : Branches) -> (t : Branches) -> Covers s (inter s t)
covers_inter_l BNil t = CovNil
covers_inter_l (BCons x rest) t with (mem_dec x t)
  covers_inter_l (BCons x rest) t | MYes pf = CovCons (InHead x rest) (covers_weaken rest x (covers_inter_l rest t))
  covers_inter_l (BCons x rest) t | MNo nx = covers_weaken rest x (covers_inter_l rest t)

covers_inter_r : (s : Branches) -> (t : Branches) -> Covers t (inter s t)
covers_inter_r BNil t = CovNil
covers_inter_r (BCons x rest) t with (mem_dec x t)
  covers_inter_r (BCons x rest) t | MYes pf = CovCons pf (covers_inter_r rest t)
  covers_inter_r (BCons x rest) t | MNo nx = covers_inter_r rest t

build_back : (s : Branches) -> (t : Branches) -> (u : Branches) -> Covers s c -> Covers (bappend t u) c -> Covers (bappend (inter s t) (inter s u)) c
build_back s t u CovNil cov_tuC = CovNil
build_back s t u (CovCons inYs cov_sC2) (CovCons inYtu cov_tuC2) = case in_union_split t u inYtu of
  OrL pf => CovCons (in_union_l (inter s t) (inter s u) (in_inter s t inYs pf)) (build_back s t u cov_sC2 cov_tuC2)
  OrR pf => CovCons (in_union_r (inter s t) (inter s u) (in_inter s u inYs pf)) (build_back s t u cov_sC2 cov_tuC2)

distrib_back : (s : Branches) -> (t : Branches) -> (u : Branches) -> Covers (bappend (inter s t) (inter s u)) (inter s (bappend t u))
distrib_back s t u = build_back s t u (covers_inter_l s (bappend t u)) (covers_inter_r s (bappend t u))

distrib_fwd : (s : Branches) -> (t : Branches) -> (u : Branches) -> Covers (inter s (bappend t u)) (bappend (inter s t) (inter s u))
distrib_fwd s t u = covers_glb (inter_mono_r s t (bappend t u) (merge_lower_l t u)) (inter_mono_r s u (bappend t u) (merge_lower_r t u))

data Equiv : Branches -> Branches -> Type where
  MkEquiv : Covers a b -> Covers b a -> Equiv a b

distrib : (s : Branches) -> (t : Branches) -> (u : Branches) -> Equiv (inter s (bappend t u)) (bappend (inter s t) (inter s u))
distrib s t u = MkEquiv (distrib_fwd s t u) (distrib_back s t u)
