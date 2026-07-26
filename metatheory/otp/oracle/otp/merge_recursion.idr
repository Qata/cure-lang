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

data Role = RA | RB | RC

role_eq : Role -> Role -> TB2
role_eq RA RA = T
role_eq RA RB = F
role_eq RA RC = F
role_eq RB RA = F
role_eq RB RB = T
role_eq RB RC = F
role_eq RC RA = F
role_eq RC RB = F
role_eq RC RC = T

data Global = GEnd | GMsg Role Role Tag Global | GCho Role Role Tag Global Tag Global | GRec Global | GVar

project : Global -> Role -> Local
project GEnd r = LEnd
project (GMsg from to t k) r = case role_eq from r of
  T => LSend t (project k r)
  F => case role_eq to r of
    T => LRecv t (project k r)
    F => project k r
project (GCho from to tL gL tR gR) r = case role_eq from r of
  T => LSel tL (project gL r) tR (project gR r)
  F => case role_eq to r of
    T => LBra tL (project gL r) tR (project gR r)
    F => merge (project gL r) (project gR r)
project (GRec body) r = LRec (project body r)
project GVar r = LVar

gsubst : Global -> Global -> Global
gsubst GEnd s = GEnd
gsubst (GMsg from to t k) s = GMsg from to t (gsubst k s)
gsubst (GCho from to tL gL tR gR) s = GCho from to tL (gsubst gL s) tR (gsubst gR s)
gsubst (GRec body) s = GRec body
gsubst GVar s = s

lsend_cong : (t : Tag) -> a = b -> LSend t a = LSend t b
lsend_cong t e = cong (LSend t) e
lrecv_cong : (t : Tag) -> a = b -> LRecv t a = LRecv t b
lrecv_cong t e = cong (LRecv t) e
lsel_cong : (a : Tag) -> pa1 = pa2 -> (b : Tag) -> pb1 = pb2 -> LSel a pa1 b pb1 = LSel a pa2 b pb2
lsel_cong a ea b eb = rewrite ea in rewrite eb in Refl
lbra_cong : (a : Tag) -> pa1 = pa2 -> (b : Tag) -> pb1 = pb2 -> LBra a pa1 b pb1 = LBra a pa2 b pb2
lbra_cong a ea b eb = rewrite ea in rewrite eb in Refl

eqv_trans : a = b -> b = c -> a = c
eqv_trans e1 e2 = trans e1 e2
merge_cong : a = a2 -> b = b2 -> merge a b = merge a2 b2
merge_cong ea eb = rewrite ea in rewrite eb in Refl

data WF : Global -> Type where
  WFEnd : WF GEnd
  WFAB  : (t : Tag) -> WF k -> WF (GMsg RA RB t k)
  WFBA  : (t : Tag) -> WF k -> WF (GMsg RB RA t k)
  WFBC  : (t : Tag) -> WF k -> WF (GMsg RB RC t k)
  WFAC  : (t : Tag) -> WF k -> WF (GMsg RA RC t k)
  WFCho : (tL : Tag) -> WF gL -> (tR : Tag) -> WF gR -> Mergeable (project gL RC) (project gR RC) -> WF (GCho RA RB tL gL tR gR)
  WFRec : (body : Global) -> WF body -> WF (GRec body)
  WFVar : WF GVar

project_subst_hom : (s : Global) -> (r : Role) -> WF g -> project (gsubst g s) r = lsubst (project g r) (project s r)
project_subst_hom s r WFEnd = Refl
project_subst_hom s RA (WFAB t w2) = lsend_cong t (project_subst_hom s RA w2)
project_subst_hom s RB (WFAB t w2) = lrecv_cong t (project_subst_hom s RB w2)
project_subst_hom s RC (WFAB t w2) = project_subst_hom s RC w2
project_subst_hom s RA (WFBA t w2) = lrecv_cong t (project_subst_hom s RA w2)
project_subst_hom s RB (WFBA t w2) = lsend_cong t (project_subst_hom s RB w2)
project_subst_hom s RC (WFBA t w2) = project_subst_hom s RC w2
project_subst_hom s RA (WFBC t w2) = project_subst_hom s RA w2
project_subst_hom s RB (WFBC t w2) = lsend_cong t (project_subst_hom s RB w2)
project_subst_hom s RC (WFBC t w2) = lrecv_cong t (project_subst_hom s RC w2)
project_subst_hom s RA (WFAC t w2) = lsend_cong t (project_subst_hom s RA w2)
project_subst_hom s RB (WFAC t w2) = project_subst_hom s RB w2
project_subst_hom s RC (WFAC t w2) = lrecv_cong t (project_subst_hom s RC w2)
project_subst_hom s RA (WFCho tL wL tR wR mg) = lsel_cong tL (project_subst_hom s RA wL) tR (project_subst_hom s RA wR)
project_subst_hom s RB (WFCho tL wL tR wR mg) = lbra_cong tL (project_subst_hom s RB wL) tR (project_subst_hom s RB wR)
project_subst_hom s RC (WFCho tL wL tR wR mg) = eqv_trans (merge_cong (project_subst_hom s RC wL) (project_subst_hom s RC wR)) (merge_lsubst_commute mg (project s RC))
project_subst_hom s r (WFRec body w2) = Refl
project_subst_hom s r WFVar = Refl

unfold_commute : (body : Global) -> (r : Role) -> WF body -> project (gsubst body (GRec body)) r = lsubst (project body r) (LRec (project body r))
unfold_commute body r w = project_subst_hom (GRec body) r w
