%default total

data Tag = TA | TB | TC
data TB2 = F | T

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

data Local = LEnd | LSend Tag Local | LRecv Tag Local | LSel Tag Local Tag Local | LBra Tag Local Tag Local | LErr

dual : Local -> Local
dual LEnd = LEnd
dual (LSend t k) = LRecv t (dual k)
dual (LRecv t k) = LSend t (dual k)
dual (LSel a la b lb) = LBra a (dual la) b (dual lb)
dual (LBra a la b lb) = LSel a (dual la) b (dual lb)
dual LErr = LErr

merge : Local -> Local -> Local
merge LEnd LEnd = LEnd
merge LEnd (LSend ty ky) = LErr
merge LEnd (LRecv ty ky) = LErr
merge LEnd (LSel ay py by qy) = LErr
merge LEnd (LBra ay py by qy) = LErr
merge LEnd LErr = LErr
merge (LSend tx kx) LEnd = LErr
merge (LSend tx kx) (LSend ty ky) = case tag_eq tx ty of
  T => LSend tx (merge kx ky)
  F => LErr
merge (LSend tx kx) (LRecv ty ky) = LErr
merge (LSend tx kx) (LSel ay py by qy) = LErr
merge (LSend tx kx) (LBra ay py by qy) = LErr
merge (LSend tx kx) LErr = LErr
merge (LRecv tx kx) LEnd = LErr
merge (LRecv tx kx) (LSend ty ky) = LErr
merge (LRecv tx kx) (LRecv ty ky) = case tag_eq tx ty of
  T => LRecv tx (merge kx ky)
  F => LBra tx kx ty ky
merge (LRecv tx kx) (LSel ay py by qy) = LErr
merge (LRecv tx kx) (LBra ay py by qy) = LErr
merge (LRecv tx kx) LErr = LErr
merge (LSel ax px bx qx) LEnd = LErr
merge (LSel ax px bx qx) (LSend ty ky) = LErr
merge (LSel ax px bx qx) (LRecv ty ky) = LErr
merge (LSel ax px bx qx) (LSel ay py by qy) = case tag_eq ax ay of
  T => case tag_eq bx by of
    T => LSel ax (merge px py) bx (merge qx qy)
    F => LErr
  F => LErr
merge (LSel ax px bx qx) (LBra ay py by qy) = LErr
merge (LSel ax px bx qx) LErr = LErr
merge (LBra ax px bx qx) LEnd = LErr
merge (LBra ax px bx qx) (LSend ty ky) = LErr
merge (LBra ax px bx qx) (LRecv ty ky) = LErr
merge (LBra ax px bx qx) (LSel ay py by qy) = LErr
merge (LBra ax px bx qx) (LBra ay py by qy) = case tag_eq ax ay of
  T => case tag_eq bx by of
    T => LBra ax (merge px py) bx (merge qx qy)
    F => LErr
  F => LErr
merge (LBra ax px bx qx) LErr = LErr
merge LErr LEnd = LErr
merge LErr (LSend ty ky) = LErr
merge LErr (LRecv ty ky) = LErr
merge LErr (LSel ay py by qy) = LErr
merge LErr (LBra ay py by qy) = LErr
merge LErr LErr = LErr

merge_idem : (l : Local) -> merge l l = l
merge_idem LEnd = Refl
merge_idem (LSend TA k) = rewrite merge_idem k in Refl
merge_idem (LSend TB k) = rewrite merge_idem k in Refl
merge_idem (LSend TC k) = rewrite merge_idem k in Refl
merge_idem (LRecv TA k) = rewrite merge_idem k in Refl
merge_idem (LRecv TB k) = rewrite merge_idem k in Refl
merge_idem (LRecv TC k) = rewrite merge_idem k in Refl
merge_idem (LSel TA la TA lb) = rewrite merge_idem la in rewrite merge_idem lb in Refl
merge_idem (LSel TA la TB lb) = rewrite merge_idem la in rewrite merge_idem lb in Refl
merge_idem (LSel TA la TC lb) = rewrite merge_idem la in rewrite merge_idem lb in Refl
merge_idem (LSel TB la TA lb) = rewrite merge_idem la in rewrite merge_idem lb in Refl
merge_idem (LSel TB la TB lb) = rewrite merge_idem la in rewrite merge_idem lb in Refl
merge_idem (LSel TB la TC lb) = rewrite merge_idem la in rewrite merge_idem lb in Refl
merge_idem (LSel TC la TA lb) = rewrite merge_idem la in rewrite merge_idem lb in Refl
merge_idem (LSel TC la TB lb) = rewrite merge_idem la in rewrite merge_idem lb in Refl
merge_idem (LSel TC la TC lb) = rewrite merge_idem la in rewrite merge_idem lb in Refl
merge_idem (LBra TA la TA lb) = rewrite merge_idem la in rewrite merge_idem lb in Refl
merge_idem (LBra TA la TB lb) = rewrite merge_idem la in rewrite merge_idem lb in Refl
merge_idem (LBra TA la TC lb) = rewrite merge_idem la in rewrite merge_idem lb in Refl
merge_idem (LBra TB la TA lb) = rewrite merge_idem la in rewrite merge_idem lb in Refl
merge_idem (LBra TB la TB lb) = rewrite merge_idem la in rewrite merge_idem lb in Refl
merge_idem (LBra TB la TC lb) = rewrite merge_idem la in rewrite merge_idem lb in Refl
merge_idem (LBra TC la TA lb) = rewrite merge_idem la in rewrite merge_idem lb in Refl
merge_idem (LBra TC la TB lb) = rewrite merge_idem la in rewrite merge_idem lb in Refl
merge_idem (LBra TC la TC lb) = rewrite merge_idem la in rewrite merge_idem lb in Refl
merge_idem LErr = Refl

lsend_cong : (t : Tag) -> a = b -> LSend t a = LSend t b
lsend_cong t e = cong (\z => LSend t z) e
lrecv_cong : (t : Tag) -> a = b -> LRecv t a = LRecv t b
lrecv_cong t e = cong (\z => LRecv t z) e
lsel_cong : (a : Tag) -> pa1 = pa2 -> (b : Tag) -> pb1 = pb2 -> LSel a pa1 b pb1 = LSel a pa2 b pb2
lsel_cong a eA b eB = trans (cong (\z => LSel a z b pb1) eA) (cong (\z => LSel a pa2 b z) eB)

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

data Global = GEnd | GMsg Role Role Tag Global | GCho Role Role Tag Global Tag Global

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

data Coherent : Global -> Type where
  CoEnd : Coherent GEnd
  CoAB : (t : Tag) -> Coherent k -> Coherent (GMsg RA RB t k)
  CoBA : (t : Tag) -> Coherent k -> Coherent (GMsg RB RA t k)
  CoCho : (tL : Tag) -> Coherent gL -> (tR : Tag) -> Coherent gR -> Coherent (GCho RA RB tL gL tR gR)

choice_duality : Coherent g -> project g RA = dual (project g RB)
choice_duality CoEnd = Refl
choice_duality (CoAB t w2) = lsend_cong t (choice_duality w2)
choice_duality (CoBA t w2) = lrecv_cong t (choice_duality w2)
choice_duality (CoCho tL wL tR wR) = lsel_cong tL (choice_duality wL) tR (choice_duality wR)
