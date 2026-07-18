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

covers_glb : Covers z s -> Covers z t -> Covers z (bappend s t)
covers_glb CovNil ct = ct
covers_glb (CovCons inx cs2) ct = CovCons inx (covers_glb cs2 ct)

merge_lower_l : (s : Branches) -> (t : Branches) -> Covers (bappend s t) s
merge_lower_l BNil t = CovNil
merge_lower_l (BCons x rest) t = CovCons (InHead x (bappend rest t)) (covers_weaken (bappend rest t) x (merge_lower_l rest t))

covers_inter_l : (s : Branches) -> (t : Branches) -> Covers s (inter s t)
covers_inter_l BNil t = CovNil
covers_inter_l (BCons x rest) t with (mem_dec x t)
  covers_inter_l (BCons x rest) t | MYes pf = CovCons (InHead x rest) (covers_weaken rest x (covers_inter_l rest t))
  covers_inter_l (BCons x rest) t | MNo nx = covers_weaken rest x (covers_inter_l rest t)

inter_super : (s : Branches) -> (u : Branches) -> Covers u s -> Covers (inter s u) s
inter_super BNil u sus = CovNil
inter_super (BCons x rest) u (CovCons inXu sus2) with (mem_dec x u)
  inter_super (BCons x rest) u (CovCons inXu sus2) | MYes pf = CovCons (InHead x (inter rest u)) (covers_weaken (inter rest u) x (inter_super rest u sus2))
  inter_super (BCons x rest) u (CovCons inXu sus2) | MNo nx = void (notin_absurd nx inXu)

data Equiv : Branches -> Branches -> Type where
  MkEquiv : Covers a b -> Covers b a -> Equiv a b

absorb_meet : (s : Branches) -> (t : Branches) -> Equiv (inter s (bappend s t)) s
absorb_meet s t = MkEquiv (inter_super s (bappend s t) (merge_lower_l s t)) (covers_inter_l s (bappend s t))

absorb_join : (s : Branches) -> (t : Branches) -> Equiv (bappend s (inter s t)) s
absorb_join s t = MkEquiv (merge_lower_l s (inter s t)) (covers_glb (covers_refl s) (covers_inter_l s t))
