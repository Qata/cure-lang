%default total

data TB2 = F | T
data Tag = TA | TB | TC

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

mutual
  merge : Local -> Local -> Local
  merge LEnd LEnd = LEnd
  merge LEnd (LRecv t2 k2) = LErr
  merge LEnd (LBra bs2) = LErr
  merge LEnd LErr = LErr
  merge (LRecv t1 k1) LEnd = LErr
  merge (LRecv t1 k1) (LRecv t2 k2) = case tag_eq t1 t2 of
    T => LRecv t1 (merge k1 k2)
    F => LErr
  merge (LRecv t1 k1) (LBra bs2) = LErr
  merge (LRecv t1 k1) LErr = LErr
  merge (LBra bs1) LEnd = LErr
  merge (LBra bs1) (LRecv t2 k2) = LErr
  merge (LBra bs1) (LBra bs2) = LBra (merge_bra bs1 bs2)
  merge (LBra bs1) LErr = LErr
  merge LErr y = LErr

  merge_bra : Branches -> Branches -> Branches
  merge_bra BNil bs2 = BNil
  merge_bra (BCons t1 k1 r1) BNil = BNil
  merge_bra (BCons t1 k1 r1) (BCons t2 k2 r2) = case tag_eq t1 t2 of
    T => BCons t1 (merge k1 k2) (merge_bra r1 r2)
    F => BNil

mutual
  merge_idem : (l : Local) -> merge l l = l
  merge_idem LEnd = Refl
  merge_idem (LRecv TA k) = cong (LRecv TA) (merge_idem k)
  merge_idem (LRecv TB k) = cong (LRecv TB) (merge_idem k)
  merge_idem (LRecv TC k) = cong (LRecv TC) (merge_idem k)
  merge_idem (LBra bs) = cong LBra (merge_bra_idem bs)
  merge_idem LErr = Refl
  merge_bra_idem : (bs : Branches) -> merge_bra bs bs = bs
  merge_bra_idem BNil = Refl
  merge_bra_idem (BCons TA k rest) = rewrite merge_idem k in rewrite merge_bra_idem rest in Refl
  merge_bra_idem (BCons TB k rest) = rewrite merge_idem k in rewrite merge_bra_idem rest in Refl
  merge_bra_idem (BCons TC k rest) = rewrite merge_idem k in rewrite merge_bra_idem rest in Refl
