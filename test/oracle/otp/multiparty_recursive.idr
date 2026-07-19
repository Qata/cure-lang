%default total

data TB2 = F | T
data Tag = TA | TB | TC
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

data Global = GEnd | GMsg Role Role Tag Global | GRec Global | GVar
data Local = LEnd | LSend Tag Local | LRecv Tag Local | LRec Local | LVar

project : Global -> Role -> Local
project GEnd r = LEnd
project (GMsg from to t k) r = case role_eq from r of
  T => LSend t (project k r)
  F => case role_eq to r of
    T => LRecv t (project k r)
    F => project k r
project (GRec body) r = LRec (project body r)
project GVar r = LVar

gsubst : Global -> Global -> Global
gsubst GEnd s = GEnd
gsubst (GMsg from to t k) s = GMsg from to t (gsubst k s)
gsubst (GRec body) s = GRec body
gsubst GVar s = s

lsubst : Local -> Local -> Local
lsubst LEnd s = LEnd
lsubst (LSend t k) s = LSend t (lsubst k s)
lsubst (LRecv t k) s = LRecv t (lsubst k s)
lsubst (LRec body) s = LRec body
lsubst LVar s = s

lsend_cong : (t : Tag) -> a = b -> LSend t a = LSend t b
lsend_cong t e = cong (\z => LSend t z) e
lrecv_cong : (t : Tag) -> a = b -> LRecv t a = LRecv t b
lrecv_cong t e = cong (\z => LRecv t z) e

project_subst_hom : (g : Global) -> (s : Global) -> (r : Role) -> project (gsubst g s) r = lsubst (project g r) (project s r)
project_subst_hom GEnd s r = Refl
project_subst_hom GVar s r = Refl
project_subst_hom (GRec body) s r = Refl
project_subst_hom (GMsg RA RA t k) s RA = lsend_cong t (project_subst_hom k s RA)
project_subst_hom (GMsg RA RA t k) s RB = project_subst_hom k s RB
project_subst_hom (GMsg RA RA t k) s RC = project_subst_hom k s RC
project_subst_hom (GMsg RA RB t k) s RA = lsend_cong t (project_subst_hom k s RA)
project_subst_hom (GMsg RA RB t k) s RB = lrecv_cong t (project_subst_hom k s RB)
project_subst_hom (GMsg RA RB t k) s RC = project_subst_hom k s RC
project_subst_hom (GMsg RA RC t k) s RA = lsend_cong t (project_subst_hom k s RA)
project_subst_hom (GMsg RA RC t k) s RB = project_subst_hom k s RB
project_subst_hom (GMsg RA RC t k) s RC = lrecv_cong t (project_subst_hom k s RC)
project_subst_hom (GMsg RB RA t k) s RA = lrecv_cong t (project_subst_hom k s RA)
project_subst_hom (GMsg RB RA t k) s RB = lsend_cong t (project_subst_hom k s RB)
project_subst_hom (GMsg RB RA t k) s RC = project_subst_hom k s RC
project_subst_hom (GMsg RB RB t k) s RA = project_subst_hom k s RA
project_subst_hom (GMsg RB RB t k) s RB = lsend_cong t (project_subst_hom k s RB)
project_subst_hom (GMsg RB RB t k) s RC = project_subst_hom k s RC
project_subst_hom (GMsg RB RC t k) s RA = project_subst_hom k s RA
project_subst_hom (GMsg RB RC t k) s RB = lsend_cong t (project_subst_hom k s RB)
project_subst_hom (GMsg RB RC t k) s RC = lrecv_cong t (project_subst_hom k s RC)
project_subst_hom (GMsg RC RA t k) s RA = lrecv_cong t (project_subst_hom k s RA)
project_subst_hom (GMsg RC RA t k) s RB = project_subst_hom k s RB
project_subst_hom (GMsg RC RA t k) s RC = lsend_cong t (project_subst_hom k s RC)
project_subst_hom (GMsg RC RB t k) s RA = project_subst_hom k s RA
project_subst_hom (GMsg RC RB t k) s RB = lrecv_cong t (project_subst_hom k s RB)
project_subst_hom (GMsg RC RB t k) s RC = lsend_cong t (project_subst_hom k s RC)
project_subst_hom (GMsg RC RC t k) s RA = project_subst_hom k s RA
project_subst_hom (GMsg RC RC t k) s RB = project_subst_hom k s RB
project_subst_hom (GMsg RC RC t k) s RC = lsend_cong t (project_subst_hom k s RC)

unfold_commute : (body : Global) -> (r : Role) -> project (gsubst body (GRec body)) r = lsubst (project body r) (LRec (project body r))
unfold_commute body r = project_subst_hom body (GRec body) r

lrec_cong : a = b -> LRec a = LRec b
lrec_cong e = cong (\z => LRec z) e

dual : Local -> Local
dual LEnd = LEnd
dual (LSend t k) = LRecv t (dual k)
dual (LRecv t k) = LSend t (dual k)
dual (LRec body) = LRec (dual body)
dual LVar = LVar

dual_involution : (l : Local) -> dual (dual l) = l
dual_involution LEnd = Refl
dual_involution (LSend t k) = lsend_cong t (dual_involution k)
dual_involution (LRecv t k) = lrecv_cong t (dual_involution k)
dual_involution (LRec body) = lrec_cong (dual_involution body)
dual_involution LVar = Refl

dual_subst_hom : (l : Local) -> (s : Local) -> dual (lsubst l s) = lsubst (dual l) (dual s)
dual_subst_hom LEnd s = Refl
dual_subst_hom (LSend t k) s = lrecv_cong t (dual_subst_hom k s)
dual_subst_hom (LRecv t k) s = lsend_cong t (dual_subst_hom k s)
dual_subst_hom (LRec body) s = Refl
dual_subst_hom LVar s = Refl

dual_unfold_commute : (body : Local) -> dual (lsubst body (LRec body)) = lsubst (dual body) (LRec (dual body))
dual_unfold_commute body = dual_subst_hom body (LRec body)

data Coherent : Global -> Type where
  CoEnd : Coherent GEnd
  CoAB : (t : Tag) -> Coherent k -> Coherent (GMsg RA RB t k)
  CoBA : (t : Tag) -> Coherent k -> Coherent (GMsg RB RA t k)
  CoRec : Coherent body -> Coherent (GRec body)
  CoVar : Coherent GVar

projection_duality : Coherent g -> project g RA = dual (project g RB)
projection_duality CoEnd = Refl
projection_duality (CoAB t w2) = lsend_cong t (projection_duality w2)
projection_duality (CoBA t w2) = lrecv_cong t (projection_duality w2)
projection_duality (CoRec w2) = lrec_cong (projection_duality w2)
projection_duality CoVar = Refl
