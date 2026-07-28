%default total

data Tag = TA | TB | TC

mutual
  data Local = LEnd | LSend Tag Local | LSel Branches
  data Branches = BNil | BCons Tag Local Branches

data Lookup : Branches -> Tag -> Local -> Type where
  LookHere : Lookup (BCons t k rest) t k
  LookThere : Lookup rest t k -> Lookup (BCons t2 k2 rest) t k

lookup_weaken : (t2 : Tag) -> (k2 : Local) -> Lookup bs t k -> Lookup (BCons t2 k2 bs) t k
lookup_weaken t2 k2 lk = LookThere lk

mutual
  data Sub : Local -> Local -> Type where
    SubEnd : Sub LEnd LEnd
    SubSend : (t : Tag) -> Sub k1 k2 -> Sub (LSend t k1) (LSend t k2)
    SubSel : SelSub bs1 bs2 -> Sub (LSel bs1) (LSel bs2)
  data SelSub : Branches -> Branches -> Type where
    SelSubNil : SelSub BNil bsSup
    SelSubCons : (t : Tag) -> Lookup bsSup t kSup -> Sub kSub kSup -> SelSub rest bsSup -> SelSub (BCons t kSub rest) bsSup

selsub_weaken : (t2 : Tag) -> (k2 : Local) -> SelSub bsSub bsSup -> SelSub bsSub (BCons t2 k2 bsSup)
selsub_weaken t2 k2 SelSubNil = SelSubNil
selsub_weaken t2 k2 (SelSubCons t lk sb rst) = SelSubCons t (lookup_weaken t2 k2 lk) sb (selsub_weaken t2 k2 rst)

mutual
  sub_refl : (l : Local) -> Sub l l
  sub_refl LEnd = SubEnd
  sub_refl (LSend t k) = SubSend t (sub_refl k)
  sub_refl (LSel bs) = SubSel (selsub_refl bs)
  selsub_refl : (bs : Branches) -> SelSub bs bs
  selsub_refl BNil = SelSubNil
  selsub_refl (BCons t k rest) = SelSubCons t LookHere (sub_refl k) (selsub_weaken t k (selsub_refl rest))

data LookSubUp : Branches -> Tag -> Local -> Type where
  MkLookSubUp : Lookup c t kSup -> Sub kSub kSup -> LookSubUp c t kSub

selsub_lookup : SelSub b c -> Lookup b t kb -> LookSubUp c t kb
selsub_lookup (SelSubCons t2 lk_c sb rst) LookHere = MkLookSubUp lk_c sb
selsub_lookup (SelSubCons t2 lk_c sb rst) (LookThere lk2) = selsub_lookup rst lk2

mutual
  sub_trans : Sub a b -> Sub b c -> Sub a c
  sub_trans SubEnd SubEnd = SubEnd
  sub_trans (SubSend t p) (SubSend t q) = SubSend t (sub_trans p q)
  sub_trans (SubSel ab) (SubSel bc) = SubSel (selsub_trans ab bc)
  selsub_trans : SelSub a b -> SelSub b c -> SelSub a c
  selsub_trans SelSubNil bc = SelSubNil
  selsub_trans (SelSubCons t lk_ab sub_ab rest_ab) bc = case selsub_lookup bc lk_ab of
    MkLookSubUp lk_ac sub_bc => SelSubCons t lk_ac (sub_trans sub_ab sub_bc) (selsub_trans rest_ab bc)

narrowing_example : Sub (LSel (BCons TA LEnd BNil)) (LSel (BCons TA LEnd (BCons TB LEnd BNil)))
narrowing_example = SubSel (SelSubCons TA LookHere SubEnd SelSubNil)

data LStep : Local -> Local -> Type where
  LStSend : LStep (LSend t k) k
  LStSel : Lookup bs t k -> LStep (LSel bs) k

data StepUp : Local -> Local -> Type where
  MkStepUp : LStep b b2 -> Sub a2 b2 -> StepUp b a2

sub_step_internal : Sub a b -> LStep a a2 -> StepUp b a2
sub_step_internal (SubSend t p) LStSend = MkStepUp LStSend p
sub_step_internal (SubSel ss) (LStSel lk) = case selsub_lookup ss lk of
  MkLookSubUp lk_sup sub2 => MkStepUp (LStSel lk_sup) sub2
