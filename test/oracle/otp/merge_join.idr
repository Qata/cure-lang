%default total

data Tag = TA | TB | TC
data OBit = OF | OT
data Branches = BNil | BCons Tag Branches
data Local = LB Branches

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

data Covers : Branches -> Branches -> Type where
  CovNil  : Covers big BNil
  CovCons : InB x big -> Covers big rest -> Covers big (BCons x rest)

covers_weaken : (big : Branches) -> (y : Tag) -> Covers big small -> Covers (BCons y big) small
covers_weaken big y CovNil = CovNil
covers_weaken big y (CovCons inx w2) = CovCons (InTail y big inx) (covers_weaken big y w2)

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

in_inter : (s : Branches) -> (t : Branches) -> InB y s -> InB y t -> InB y (inter s t)
in_inter BNil t inYs inYt = void (noInBNil inYs)
in_inter (BCons x rest) t inYs inYt with (mem_dec x t)
  in_inter (BCons x rest) t inYs inYt | MYes pf = case inYs of
    InHead y2 r2 => InHead y2 (inter rest t)
    InTail z r m2 => InTail x (inter rest t) (in_inter rest t m2 inYt)
  in_inter (BCons x rest) t inYs inYt | MNo nx = case inYs of
    InHead y2 r2 => void (notin_absurd nx inYt)
    InTail z r m2 => in_inter rest t m2 inYt

data Sub : Local -> Local -> Type where
  SubB : Covers s t -> Sub (LB s) (LB t)

join : Local -> Local -> Local
join (LB s) (LB t) = LB (inter s t)

join_upper_l : (s : Branches) -> (t : Branches) -> Sub (LB s) (join (LB s) (LB t))
join_upper_l s t = SubB (covers_inter_l s t)

join_upper_r : (s : Branches) -> (t : Branches) -> Sub (LB t) (join (LB s) (LB t))
join_upper_r s t = SubB (covers_inter_r s t)

covers_join_least : (s : Branches) -> (t : Branches) -> Covers s u -> Covers t u -> Covers (inter s t) u
covers_join_least s t CovNil ctu = CovNil
covers_join_least s t (CovCons inYs csu2) (CovCons inYt ctu2) = CovCons (in_inter s t inYs inYt) (covers_join_least s t csu2 ctu2)

join_least : (s : Branches) -> (t : Branches) -> Sub (LB s) (LB u) -> Sub (LB t) (LB u) -> Sub (join (LB s) (LB t)) (LB u)
join_least s t (SubB csu) (SubB ctu) = SubB (covers_join_least s t csu ctu)
