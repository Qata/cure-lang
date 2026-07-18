%default total

data Tag = TA | TB | TC
data Branches = BNil | BCons Tag Branches
data Local = LB Branches

data InB : Tag -> Branches -> Type where
  InHead : (x2 : Tag) -> (rest : Branches) -> InB x2 (BCons x2 rest)
  InTail : (y : Tag) -> (rest : Branches) -> InB x2 rest -> InB x2 (BCons y rest)

data MemDec : Tag -> Branches -> Type where
  MYes : InB x t -> MemDec x t
  MNo  : MemDec x t

mem_dec : (x : Tag) -> (t : Branches) -> MemDec x t
mem_dec x BNil = MNo
mem_dec TA (BCons TA rest) = MYes (InHead TA rest)
mem_dec TA (BCons TB rest) = case mem_dec TA rest of
  MYes pf => MYes (InTail TB rest pf)
  MNo => MNo
mem_dec TA (BCons TC rest) = case mem_dec TA rest of
  MYes pf => MYes (InTail TC rest pf)
  MNo => MNo
mem_dec TB (BCons TA rest) = case mem_dec TB rest of
  MYes pf => MYes (InTail TA rest pf)
  MNo => MNo
mem_dec TB (BCons TB rest) = MYes (InHead TB rest)
mem_dec TB (BCons TC rest) = case mem_dec TB rest of
  MYes pf => MYes (InTail TC rest pf)
  MNo => MNo
mem_dec TC (BCons TA rest) = case mem_dec TC rest of
  MYes pf => MYes (InTail TA rest pf)
  MNo => MNo
mem_dec TC (BCons TB rest) = case mem_dec TC rest of
  MYes pf => MYes (InTail TB rest pf)
  MNo => MNo
mem_dec TC (BCons TC rest) = MYes (InHead TC rest)

mutual
  inter_pick : (x : Tag) -> (t : Branches) -> (rest : Branches) -> MemDec x t -> Branches
  inter_pick x t rest (MYes pf) = BCons x (inter rest t)
  inter_pick x t rest MNo = inter rest t

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
  covers_inter_l (BCons x rest) t | MNo = covers_weaken rest x (covers_inter_l rest t)

covers_inter_r : (s : Branches) -> (t : Branches) -> Covers t (inter s t)
covers_inter_r BNil t = CovNil
covers_inter_r (BCons x rest) t with (mem_dec x t)
  covers_inter_r (BCons x rest) t | MYes pf = CovCons pf (covers_inter_r rest t)
  covers_inter_r (BCons x rest) t | MNo = covers_inter_r rest t

data Sub : Local -> Local -> Type where
  SubB : Covers s t -> Sub (LB s) (LB t)

join : Local -> Local -> Local
join (LB s) (LB t) = LB (inter s t)

join_upper_l : (s : Branches) -> (t : Branches) -> Sub (LB s) (join (LB s) (LB t))
join_upper_l s t = SubB (covers_inter_l s t)

join_upper_r : (s : Branches) -> (t : Branches) -> Sub (LB t) (join (LB s) (LB t))
join_upper_r s t = SubB (covers_inter_r s t)
