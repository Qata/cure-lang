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

tNeF : T = F -> Void
tNeF Refl impossible

data Local = LEnd | LSend Tag Local | LRecv Tag Local | LSel Tag Local Tag Local | LBra Tag Local Tag Local | LRec Local | LVar | LErr

merge : Local -> Local -> Local
merge LEnd LEnd = LEnd
merge (LSend t1 k1) (LSend t2 k2) = case tag_eq t1 t2 of
  T => LSend t1 (merge k1 k2)
  F => LErr
merge (LRecv t1 k1) (LRecv t2 k2) = case tag_eq t1 t2 of
  T => LRecv t1 (merge k1 k2)
  F => LBra t1 k1 t2 k2
merge (LSel a1 pa1 b1 pb1) (LSel a2 pa2 b2 pb2) = case tag_eq a1 a2 of
  T => case tag_eq b1 b2 of
    T => LSel a1 (merge pa1 pa2) b1 (merge pb1 pb2)
    F => LErr
  F => LErr
merge (LBra a1 pa1 b1 pb1) (LBra a2 pa2 b2 pb2) = case tag_eq a1 a2 of
  T => case tag_eq b1 b2 of
    T => LBra a1 (merge pa1 pa2) b1 (merge pb1 pb2)
    F => LErr
  F => LErr
merge (LRec p1) (LRec p2) = LRec (merge p1 p2)
merge LVar LVar = LVar
merge _ _ = LErr

lsubst : Local -> Local -> Local
lsubst LEnd s = LEnd
lsubst (LSend t k) s = LSend t (lsubst k s)
lsubst (LRecv t k) s = LRecv t (lsubst k s)
lsubst (LSel a pa b pb) s = LSel a (lsubst pa s) b (lsubst pb s)
lsubst (LBra a pa b pb) s = LBra a (lsubst pa s) b (lsubst pb s)
lsubst (LRec body) s = LRec body
lsubst LVar s = s
lsubst LErr s = LErr

merge_idem : (l : Local) -> merge l l = l
merge_idem LEnd = Refl
merge_idem (LSend TA k) = cong (LSend TA) (merge_idem k)
merge_idem (LSend TB k) = cong (LSend TB) (merge_idem k)
merge_idem (LSend TC k) = cong (LSend TC) (merge_idem k)
merge_idem (LRecv TA k) = cong (LRecv TA) (merge_idem k)
merge_idem (LRecv TB k) = cong (LRecv TB) (merge_idem k)
merge_idem (LRecv TC k) = cong (LRecv TC) (merge_idem k)
merge_idem (LSel TA bA TA bB) = rewrite merge_idem bA in rewrite merge_idem bB in Refl
merge_idem (LSel TA bA TB bB) = rewrite merge_idem bA in rewrite merge_idem bB in Refl
merge_idem (LSel TA bA TC bB) = rewrite merge_idem bA in rewrite merge_idem bB in Refl
merge_idem (LSel TB bA TA bB) = rewrite merge_idem bA in rewrite merge_idem bB in Refl
merge_idem (LSel TB bA TB bB) = rewrite merge_idem bA in rewrite merge_idem bB in Refl
merge_idem (LSel TB bA TC bB) = rewrite merge_idem bA in rewrite merge_idem bB in Refl
merge_idem (LSel TC bA TA bB) = rewrite merge_idem bA in rewrite merge_idem bB in Refl
merge_idem (LSel TC bA TB bB) = rewrite merge_idem bA in rewrite merge_idem bB in Refl
merge_idem (LSel TC bA TC bB) = rewrite merge_idem bA in rewrite merge_idem bB in Refl
merge_idem (LBra TA bA TA bB) = rewrite merge_idem bA in rewrite merge_idem bB in Refl
merge_idem (LBra TA bA TB bB) = rewrite merge_idem bA in rewrite merge_idem bB in Refl
merge_idem (LBra TA bA TC bB) = rewrite merge_idem bA in rewrite merge_idem bB in Refl
merge_idem (LBra TB bA TA bB) = rewrite merge_idem bA in rewrite merge_idem bB in Refl
merge_idem (LBra TB bA TB bB) = rewrite merge_idem bA in rewrite merge_idem bB in Refl
merge_idem (LBra TB bA TC bB) = rewrite merge_idem bA in rewrite merge_idem bB in Refl
merge_idem (LBra TC bA TA bB) = rewrite merge_idem bA in rewrite merge_idem bB in Refl
merge_idem (LBra TC bA TB bB) = rewrite merge_idem bA in rewrite merge_idem bB in Refl
merge_idem (LBra TC bA TC bB) = rewrite merge_idem bA in rewrite merge_idem bB in Refl
merge_idem (LRec p) = cong LRec (merge_idem p)
merge_idem LVar = Refl
merge_idem LErr = Refl

data Mergeable : Local -> Local -> Type where
  MgEnd    : Mergeable LEnd LEnd
  MgSend   : (t : Tag) -> Mergeable k1 k2 -> Mergeable (LSend t k1) (LSend t k2)
  MgRecvEq : (t : Tag) -> Mergeable k1 k2 -> Mergeable (LRecv t k1) (LRecv t k2)
  MgRecvNe : (a : Tag) -> (b : Tag) -> (xk : Local) -> (yk : Local) -> tag_eq a b = F -> Mergeable (LRecv a xk) (LRecv b yk)
  MgSel    : (a : Tag) -> (b : Tag) -> Mergeable pa1 pa2 -> Mergeable pb1 pb2 -> Mergeable (LSel a pa1 b pb1) (LSel a pa2 b pb2)
  MgBra    : (a : Tag) -> (b : Tag) -> Mergeable pa1 pa2 -> Mergeable pb1 pb2 -> Mergeable (LBra a pa1 b pb1) (LBra a pa2 b pb2)
  MgVar    : Mergeable LVar LVar
  MgRec    : (p1 : Local) -> (p2 : Local) -> Mergeable p1 p2 -> Mergeable (LRec p1) (LRec p2)

merge_lsubst_commute : Mergeable x y -> (s : Local) -> merge (lsubst x s) (lsubst y s) = lsubst (merge x y) s
merge_lsubst_commute MgEnd s = Refl
merge_lsubst_commute (MgSend TA m2) s = cong (LSend TA) (merge_lsubst_commute m2 s)
merge_lsubst_commute (MgSend TB m2) s = cong (LSend TB) (merge_lsubst_commute m2 s)
merge_lsubst_commute (MgSend TC m2) s = cong (LSend TC) (merge_lsubst_commute m2 s)
merge_lsubst_commute (MgRecvEq TA m2) s = cong (LRecv TA) (merge_lsubst_commute m2 s)
merge_lsubst_commute (MgRecvEq TB m2) s = cong (LRecv TB) (merge_lsubst_commute m2 s)
merge_lsubst_commute (MgRecvEq TC m2) s = cong (LRecv TC) (merge_lsubst_commute m2 s)
merge_lsubst_commute (MgRecvNe TA TA xk yk pne) s = void (tNeF pne)
merge_lsubst_commute (MgRecvNe TA TB xk yk pne) s = Refl
merge_lsubst_commute (MgRecvNe TA TC xk yk pne) s = Refl
merge_lsubst_commute (MgRecvNe TB TA xk yk pne) s = Refl
merge_lsubst_commute (MgRecvNe TB TB xk yk pne) s = void (tNeF pne)
merge_lsubst_commute (MgRecvNe TB TC xk yk pne) s = Refl
merge_lsubst_commute (MgRecvNe TC TA xk yk pne) s = Refl
merge_lsubst_commute (MgRecvNe TC TB xk yk pne) s = Refl
merge_lsubst_commute (MgRecvNe TC TC xk yk pne) s = void (tNeF pne)
merge_lsubst_commute (MgSel TA TA mA mB) s = rewrite merge_lsubst_commute mA s in rewrite merge_lsubst_commute mB s in Refl
merge_lsubst_commute (MgSel TA TB mA mB) s = rewrite merge_lsubst_commute mA s in rewrite merge_lsubst_commute mB s in Refl
merge_lsubst_commute (MgSel TA TC mA mB) s = rewrite merge_lsubst_commute mA s in rewrite merge_lsubst_commute mB s in Refl
merge_lsubst_commute (MgSel TB TA mA mB) s = rewrite merge_lsubst_commute mA s in rewrite merge_lsubst_commute mB s in Refl
merge_lsubst_commute (MgSel TB TB mA mB) s = rewrite merge_lsubst_commute mA s in rewrite merge_lsubst_commute mB s in Refl
merge_lsubst_commute (MgSel TB TC mA mB) s = rewrite merge_lsubst_commute mA s in rewrite merge_lsubst_commute mB s in Refl
merge_lsubst_commute (MgSel TC TA mA mB) s = rewrite merge_lsubst_commute mA s in rewrite merge_lsubst_commute mB s in Refl
merge_lsubst_commute (MgSel TC TB mA mB) s = rewrite merge_lsubst_commute mA s in rewrite merge_lsubst_commute mB s in Refl
merge_lsubst_commute (MgSel TC TC mA mB) s = rewrite merge_lsubst_commute mA s in rewrite merge_lsubst_commute mB s in Refl
merge_lsubst_commute (MgBra TA TA mA mB) s = rewrite merge_lsubst_commute mA s in rewrite merge_lsubst_commute mB s in Refl
merge_lsubst_commute (MgBra TA TB mA mB) s = rewrite merge_lsubst_commute mA s in rewrite merge_lsubst_commute mB s in Refl
merge_lsubst_commute (MgBra TA TC mA mB) s = rewrite merge_lsubst_commute mA s in rewrite merge_lsubst_commute mB s in Refl
merge_lsubst_commute (MgBra TB TA mA mB) s = rewrite merge_lsubst_commute mA s in rewrite merge_lsubst_commute mB s in Refl
merge_lsubst_commute (MgBra TB TB mA mB) s = rewrite merge_lsubst_commute mA s in rewrite merge_lsubst_commute mB s in Refl
merge_lsubst_commute (MgBra TB TC mA mB) s = rewrite merge_lsubst_commute mA s in rewrite merge_lsubst_commute mB s in Refl
merge_lsubst_commute (MgBra TC TA mA mB) s = rewrite merge_lsubst_commute mA s in rewrite merge_lsubst_commute mB s in Refl
merge_lsubst_commute (MgBra TC TB mA mB) s = rewrite merge_lsubst_commute mA s in rewrite merge_lsubst_commute mB s in Refl
merge_lsubst_commute (MgBra TC TC mA mB) s = rewrite merge_lsubst_commute mA s in rewrite merge_lsubst_commute mB s in Refl
merge_lsubst_commute MgVar s = merge_idem s
merge_lsubst_commute (MgRec p1 p2 mp) s = Refl
