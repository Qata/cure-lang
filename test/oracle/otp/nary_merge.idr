%default total

data TB2 = F | T
data Tag = TA | TB | TC

tNeF : T = F -> Void
tNeF Refl impossible

tag_eq : Tag -> Tag -> TB2
tag_eq TA TA = T
tag_eq TA TB = F
tag_eq TA TC = F
tag_eq TB TA = F
tag_eq TB TB = T
tag_eq TB TC = F
tag_eq TC TA = F
tag_eq TC TB = F
tag_eq TC TC = T

mutual
  data Local = LEnd | LRecv Tag Local | LBra Branches | LErr
  data Branches = BNil | BCons Tag Local Branches

union_branches : Branches -> Branches -> Branches
union_branches BNil bs2 = bs2
union_branches (BCons t k rest) bs2 = BCons t k (union_branches rest bs2)

is_err : Local -> TB2
is_err LEnd = F
is_err (LRecv t k) = F
is_err (LBra bs) = F
is_err LErr = T

merge : Local -> Local -> Local
merge LEnd LEnd = LEnd
merge LEnd (LRecv t2 k2) = LErr
merge LEnd (LBra bs2) = LErr
merge LEnd LErr = LErr
merge (LRecv t1 k1) LEnd = LErr
merge (LRecv t1 k1) (LRecv t2 k2) = case tag_eq t1 t2 of
  T => LRecv t1 (merge k1 k2)
  F => LBra (BCons t1 k1 (BCons t2 k2 BNil))
merge (LRecv t1 k1) (LBra bs2) = LErr
merge (LRecv t1 k1) LErr = LErr
merge (LBra bs1) LEnd = LErr
merge (LBra bs1) (LRecv t2 k2) = LErr
merge (LBra bs1) (LBra bs2) = LBra (union_branches bs1 bs2)
merge (LBra bs1) LErr = LErr
merge LErr y = LErr

data Mergeable : Local -> Local -> Type where
  MgEnd : Mergeable LEnd LEnd
  MgRecvEq : (t : Tag) -> Mergeable k1 k2 -> Mergeable (LRecv t k1) (LRecv t k2)
  MgRecvNe : (a : Tag) -> (b : Tag) -> tag_eq a b = F -> Mergeable (LRecv a k1) (LRecv b k2)
  MgBra : Mergeable (LBra bs1) (LBra bs2)

merge_ok : Mergeable x y -> is_err (merge x y) = F
merge_ok MgEnd = Refl
merge_ok (MgRecvEq TA m) = Refl
merge_ok (MgRecvEq TB m) = Refl
merge_ok (MgRecvEq TC m) = Refl
merge_ok (MgRecvNe TA TA pne) = void (tNeF pne)
merge_ok (MgRecvNe TA TB pne) = Refl
merge_ok (MgRecvNe TA TC pne) = Refl
merge_ok (MgRecvNe TB TA pne) = Refl
merge_ok (MgRecvNe TB TB pne) = void (tNeF pne)
merge_ok (MgRecvNe TB TC pne) = Refl
merge_ok (MgRecvNe TC TA pne) = Refl
merge_ok (MgRecvNe TC TB pne) = Refl
merge_ok (MgRecvNe TC TC pne) = void (tNeF pne)
merge_ok MgBra = Refl
