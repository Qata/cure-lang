%default total

data Tag = TA | TB | TC

mutual
  data Local = LEnd | LRecv Tag Local | LBra Branches
  data Branches = BNil | BCons Tag Local Branches

data Lookup : Branches -> Tag -> Local -> Type where
  LookHere : Lookup (BCons t k rest) t k
  LookThere : Lookup rest t k -> Lookup (BCons t2 k2 rest) t k

lookup_weaken : (t2 : Tag) -> (k2 : Local) -> Lookup bs t k -> Lookup (BCons t2 k2 bs) t k
lookup_weaken t2 k2 lk = LookThere lk

mutual
  data Sub : Local -> Local -> Type where
    SubEnd : Sub LEnd LEnd
    SubRecv : (t : Tag) -> Sub k1 k2 -> Sub (LRecv t k1) (LRecv t k2)
    SubBra : BraSub bs1 bs2 -> Sub (LBra bs1) (LBra bs2)
  data BraSub : Branches -> Branches -> Type where
    BraSubNil : BraSub bsSub BNil
    BraSubCons : (t : Tag) -> Lookup bsSub t kSub -> Sub kSub kSup -> BraSub bsSub rest -> BraSub bsSub (BCons t kSup rest)

brasub_weaken : (t2 : Tag) -> (k2 : Local) -> BraSub bsSub bsSup -> BraSub (BCons t2 k2 bsSub) bsSup
brasub_weaken t2 k2 BraSubNil = BraSubNil
brasub_weaken t2 k2 (BraSubCons t lk sb rst) = BraSubCons t (lookup_weaken t2 k2 lk) sb (brasub_weaken t2 k2 rst)

mutual
  sub_refl : (l : Local) -> Sub l l
  sub_refl LEnd = SubEnd
  sub_refl (LRecv t k) = SubRecv t (sub_refl k)
  sub_refl (LBra bs) = SubBra (brasub_refl bs)
  brasub_refl : (bs : Branches) -> BraSub bs bs
  brasub_refl BNil = BraSubNil
  brasub_refl (BCons t k rest) = BraSubCons t LookHere (sub_refl k) (brasub_weaken t k (brasub_refl rest))

width_example : Sub (LBra (BCons TA LEnd (BCons TB LEnd BNil))) (LBra (BCons TA LEnd BNil))
width_example = SubBra (BraSubCons TA LookHere SubEnd BraSubNil)

data LookSub : Branches -> Tag -> Local -> Type where
  MkLookSub : Lookup a t kSub -> Sub kSub kSup -> LookSub a t kSup

brasub_lookup : BraSub a b -> Lookup b t kb -> LookSub a t kb
brasub_lookup (BraSubCons t2 lk_a sb rst) LookHere = MkLookSub lk_a sb
brasub_lookup (BraSubCons t2 lk_a sb rst) (LookThere lk2) = brasub_lookup rst lk2

mutual
  sub_trans : Sub a b -> Sub b c -> Sub a c
  sub_trans SubEnd SubEnd = SubEnd
  sub_trans (SubRecv t p) (SubRecv t q) = SubRecv t (sub_trans p q)
  sub_trans (SubBra ab) (SubBra bc) = SubBra (brasub_trans ab bc)
  brasub_trans : BraSub a b -> BraSub b c -> BraSub a c
  brasub_trans ab BraSubNil = BraSubNil
  brasub_trans ab (BraSubCons t lk_bc sub_bc rest_bc) = case brasub_lookup ab lk_bc of
    MkLookSub lk_ac sub_ab => BraSubCons t lk_ac (sub_trans sub_ab sub_bc) (brasub_trans ab rest_bc)

data LStep : Local -> Local -> Type where
  LStRecv : LStep (LRecv t k) k
  LStBra : Lookup bs t k -> LStep (LBra bs) k

data StepTo : Local -> Local -> Type where
  MkStepTo : LStep a t -> Sub t b2 -> StepTo a b2

sub_step_l : Sub a b -> LStep b b2 -> StepTo a b2
sub_step_l (SubRecv t p) LStRecv = MkStepTo LStRecv p
sub_step_l (SubBra bsub) (LStBra lk) = case brasub_lookup bsub lk of
  MkLookSub lk_a sub_a => MkStepTo (LStBra lk_a) sub_a
