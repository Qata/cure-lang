%default total

data Tag = TA | TB | TC
mutual
  data Local = LEnd | LSend Tag Local | LRecv Tag Local | LSel Branches | LBra Branches
  data Branches = BNil | BCons Tag Local Branches

mutual
  dual : Local -> Local
  dual LEnd = LEnd
  dual (LSend t k) = LRecv t (dual k)
  dual (LRecv t k) = LSend t (dual k)
  dual (LSel bs) = LBra (dual_branches bs)
  dual (LBra bs) = LSel (dual_branches bs)
  dual_branches : Branches -> Branches
  dual_branches BNil = BNil
  dual_branches (BCons t l rest) = BCons t (dual l) (dual_branches rest)

mutual
  dual_involution : (l : Local) -> dual (dual l) = l
  dual_involution LEnd = Refl
  dual_involution (LSend t k) = cong (LSend t) (dual_involution k)
  dual_involution (LRecv t k) = cong (LRecv t) (dual_involution k)
  dual_involution (LSel bs) = cong LSel (dual_branches_involution bs)
  dual_involution (LBra bs) = cong LBra (dual_branches_involution bs)
  dual_branches_involution : (bs : Branches) -> dual_branches (dual_branches bs) = bs
  dual_branches_involution BNil = Refl
  dual_branches_involution (BCons t l rest) = rewrite dual_involution l in rewrite dual_branches_involution rest in Refl
