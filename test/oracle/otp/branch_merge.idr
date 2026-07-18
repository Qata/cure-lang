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

is_err : Local -> TB2
is_err LEnd = F
is_err (LSend t k) = F
is_err (LRecv t k) = F
is_err (LSel a la b lb) = F
is_err (LBra a la b lb) = F
is_err LErr = T

data Mergeable : Local -> Local -> Type where
  MgEnd : Mergeable LEnd LEnd
  MgSend : (t : Tag) -> Mergeable k1 k2 -> Mergeable (LSend t k1) (LSend t k2)
  MgRecvEq : (t : Tag) -> Mergeable k1 k2 -> Mergeable (LRecv t k1) (LRecv t k2)
  MgRecvNe : (a : Tag) -> (b : Tag) -> tag_eq a b = F -> Mergeable (LRecv a k1) (LRecv b k2)
  MgSel : (a : Tag) -> (b : Tag) -> Mergeable pa1 pa2 -> Mergeable pb1 pb2 -> Mergeable (LSel a pa1 b pb1) (LSel a pa2 b pb2)
  MgBra : (a : Tag) -> (b : Tag) -> Mergeable pa1 pa2 -> Mergeable pb1 pb2 -> Mergeable (LBra a pa1 b pb1) (LBra a pa2 b pb2)

tNeF : T = F -> Void
tNeF Refl impossible

merge_ok : Mergeable x y -> is_err (merge x y) = F
merge_ok MgEnd = Refl
merge_ok (MgSend TA w2) = Refl
merge_ok (MgSend TB w2) = Refl
merge_ok (MgSend TC w2) = Refl
merge_ok (MgRecvEq TA w2) = Refl
merge_ok (MgRecvEq TB w2) = Refl
merge_ok (MgRecvEq TC w2) = Refl
merge_ok (MgRecvNe TA TA pne) = void (tNeF pne)
merge_ok (MgRecvNe TA TB pne) = Refl
merge_ok (MgRecvNe TA TC pne) = Refl
merge_ok (MgRecvNe TB TA pne) = Refl
merge_ok (MgRecvNe TB TB pne) = void (tNeF pne)
merge_ok (MgRecvNe TB TC pne) = Refl
merge_ok (MgRecvNe TC TA pne) = Refl
merge_ok (MgRecvNe TC TB pne) = Refl
merge_ok (MgRecvNe TC TC pne) = void (tNeF pne)
merge_ok (MgSel TA TA wA wB) = Refl
merge_ok (MgSel TA TB wA wB) = Refl
merge_ok (MgSel TA TC wA wB) = Refl
merge_ok (MgSel TB TA wA wB) = Refl
merge_ok (MgSel TB TB wA wB) = Refl
merge_ok (MgSel TB TC wA wB) = Refl
merge_ok (MgSel TC TA wA wB) = Refl
merge_ok (MgSel TC TB wA wB) = Refl
merge_ok (MgSel TC TC wA wB) = Refl
merge_ok (MgBra TA TA wA wB) = Refl
merge_ok (MgBra TA TB wA wB) = Refl
merge_ok (MgBra TA TC wA wB) = Refl
merge_ok (MgBra TB TA wA wB) = Refl
merge_ok (MgBra TB TB wA wB) = Refl
merge_ok (MgBra TB TC wA wB) = Refl
merge_ok (MgBra TC TA wA wB) = Refl
merge_ok (MgBra TC TB wA wB) = Refl
merge_ok (MgBra TC TC wA wB) = Refl

data WF : Global -> Type where
  WFEnd : WF GEnd
  WFAB : (t : Tag) -> WF k -> WF (GMsg RA RB t k)
  WFBA : (t : Tag) -> WF k -> WF (GMsg RB RA t k)
  WFBC : (t : Tag) -> WF k -> WF (GMsg RB RC t k)
  WFAC : (t : Tag) -> WF k -> WF (GMsg RA RC t k)
  WFCho : (tL : Tag) -> WF gL -> (tR : Tag) -> WF gR -> Mergeable (project gL RC) (project gR RC) -> WF (GCho RA RB tL gL tR gR)

bystander_defined : WF g -> is_err (project g RC) = F
bystander_defined WFEnd = Refl
bystander_defined (WFAB t w2) = bystander_defined w2
bystander_defined (WFBA t w2) = bystander_defined w2
bystander_defined (WFBC t w2) = Refl
bystander_defined (WFAC t w2) = Refl
bystander_defined (WFCho tL wL tR wR mg) = merge_ok mg

data Sub : Local -> Local -> Type where
  SubEnd : Sub LEnd LEnd
  SubSend : (t : Tag) -> Sub k1 k2 -> Sub (LSend t k1) (LSend t k2)
  SubRecv : (t : Tag) -> Sub k1 k2 -> Sub (LRecv t k1) (LRecv t k2)
  SubSel : (a : Tag) -> (b : Tag) -> Sub pa1 pa2 -> Sub pb1 pb2 -> Sub (LSel a pa1 b pb1) (LSel a pa2 b pb2)
  SubBra : (a : Tag) -> (b : Tag) -> Sub pa1 pa2 -> Sub pb1 pb2 -> Sub (LBra a pa1 b pb1) (LBra a pa2 b pb2)
  SubBraL : Sub (LBra a k b kb) (LRecv a k)
  SubBraR : Sub (LBra a ka b k) (LRecv b k)
  SubBraLcov : Sub k k2 -> Sub (LBra a k b kb) (LRecv a k2)
  SubBraRcov : Sub k k2 -> Sub (LBra a ka b k) (LRecv b k2)
  SubErr : Sub LErr LErr

sub_refl : (l : Local) -> Sub l l
sub_refl LEnd = SubEnd
sub_refl (LSend t k) = SubSend t (sub_refl k)
sub_refl (LRecv t k) = SubRecv t (sub_refl k)
sub_refl (LSel a la b lb) = SubSel a b (sub_refl la) (sub_refl lb)
sub_refl (LBra a la b lb) = SubBra a b (sub_refl la) (sub_refl lb)
sub_refl LErr = SubErr

merge_sub_l : Mergeable x y -> Sub (merge x y) x
merge_sub_l MgEnd = SubEnd
merge_sub_l (MgSend TA w2) = SubSend TA (merge_sub_l w2)
merge_sub_l (MgSend TB w2) = SubSend TB (merge_sub_l w2)
merge_sub_l (MgSend TC w2) = SubSend TC (merge_sub_l w2)
merge_sub_l (MgRecvEq TA w2) = SubRecv TA (merge_sub_l w2)
merge_sub_l (MgRecvEq TB w2) = SubRecv TB (merge_sub_l w2)
merge_sub_l (MgRecvEq TC w2) = SubRecv TC (merge_sub_l w2)
merge_sub_l (MgRecvNe TA TA pne) = void (tNeF pne)
merge_sub_l (MgRecvNe TA TB pne) = SubBraL
merge_sub_l (MgRecvNe TA TC pne) = SubBraL
merge_sub_l (MgRecvNe TB TA pne) = SubBraL
merge_sub_l (MgRecvNe TB TB pne) = void (tNeF pne)
merge_sub_l (MgRecvNe TB TC pne) = SubBraL
merge_sub_l (MgRecvNe TC TA pne) = SubBraL
merge_sub_l (MgRecvNe TC TB pne) = SubBraL
merge_sub_l (MgRecvNe TC TC pne) = void (tNeF pne)
merge_sub_l (MgSel TA TA wA wB) = SubSel TA TA (merge_sub_l wA) (merge_sub_l wB)
merge_sub_l (MgSel TA TB wA wB) = SubSel TA TB (merge_sub_l wA) (merge_sub_l wB)
merge_sub_l (MgSel TA TC wA wB) = SubSel TA TC (merge_sub_l wA) (merge_sub_l wB)
merge_sub_l (MgSel TB TA wA wB) = SubSel TB TA (merge_sub_l wA) (merge_sub_l wB)
merge_sub_l (MgSel TB TB wA wB) = SubSel TB TB (merge_sub_l wA) (merge_sub_l wB)
merge_sub_l (MgSel TB TC wA wB) = SubSel TB TC (merge_sub_l wA) (merge_sub_l wB)
merge_sub_l (MgSel TC TA wA wB) = SubSel TC TA (merge_sub_l wA) (merge_sub_l wB)
merge_sub_l (MgSel TC TB wA wB) = SubSel TC TB (merge_sub_l wA) (merge_sub_l wB)
merge_sub_l (MgSel TC TC wA wB) = SubSel TC TC (merge_sub_l wA) (merge_sub_l wB)
merge_sub_l (MgBra TA TA wA wB) = SubBra TA TA (merge_sub_l wA) (merge_sub_l wB)
merge_sub_l (MgBra TA TB wA wB) = SubBra TA TB (merge_sub_l wA) (merge_sub_l wB)
merge_sub_l (MgBra TA TC wA wB) = SubBra TA TC (merge_sub_l wA) (merge_sub_l wB)
merge_sub_l (MgBra TB TA wA wB) = SubBra TB TA (merge_sub_l wA) (merge_sub_l wB)
merge_sub_l (MgBra TB TB wA wB) = SubBra TB TB (merge_sub_l wA) (merge_sub_l wB)
merge_sub_l (MgBra TB TC wA wB) = SubBra TB TC (merge_sub_l wA) (merge_sub_l wB)
merge_sub_l (MgBra TC TA wA wB) = SubBra TC TA (merge_sub_l wA) (merge_sub_l wB)
merge_sub_l (MgBra TC TB wA wB) = SubBra TC TB (merge_sub_l wA) (merge_sub_l wB)
merge_sub_l (MgBra TC TC wA wB) = SubBra TC TC (merge_sub_l wA) (merge_sub_l wB)

merge_sub_r : Mergeable x y -> Sub (merge x y) y
merge_sub_r MgEnd = SubEnd
merge_sub_r (MgSend TA w2) = SubSend TA (merge_sub_r w2)
merge_sub_r (MgSend TB w2) = SubSend TB (merge_sub_r w2)
merge_sub_r (MgSend TC w2) = SubSend TC (merge_sub_r w2)
merge_sub_r (MgRecvEq TA w2) = SubRecv TA (merge_sub_r w2)
merge_sub_r (MgRecvEq TB w2) = SubRecv TB (merge_sub_r w2)
merge_sub_r (MgRecvEq TC w2) = SubRecv TC (merge_sub_r w2)
merge_sub_r (MgRecvNe TA TA pne) = void (tNeF pne)
merge_sub_r (MgRecvNe TA TB pne) = SubBraR
merge_sub_r (MgRecvNe TA TC pne) = SubBraR
merge_sub_r (MgRecvNe TB TA pne) = SubBraR
merge_sub_r (MgRecvNe TB TB pne) = void (tNeF pne)
merge_sub_r (MgRecvNe TB TC pne) = SubBraR
merge_sub_r (MgRecvNe TC TA pne) = SubBraR
merge_sub_r (MgRecvNe TC TB pne) = SubBraR
merge_sub_r (MgRecvNe TC TC pne) = void (tNeF pne)
merge_sub_r (MgSel TA TA wA wB) = SubSel TA TA (merge_sub_r wA) (merge_sub_r wB)
merge_sub_r (MgSel TA TB wA wB) = SubSel TA TB (merge_sub_r wA) (merge_sub_r wB)
merge_sub_r (MgSel TA TC wA wB) = SubSel TA TC (merge_sub_r wA) (merge_sub_r wB)
merge_sub_r (MgSel TB TA wA wB) = SubSel TB TA (merge_sub_r wA) (merge_sub_r wB)
merge_sub_r (MgSel TB TB wA wB) = SubSel TB TB (merge_sub_r wA) (merge_sub_r wB)
merge_sub_r (MgSel TB TC wA wB) = SubSel TB TC (merge_sub_r wA) (merge_sub_r wB)
merge_sub_r (MgSel TC TA wA wB) = SubSel TC TA (merge_sub_r wA) (merge_sub_r wB)
merge_sub_r (MgSel TC TB wA wB) = SubSel TC TB (merge_sub_r wA) (merge_sub_r wB)
merge_sub_r (MgSel TC TC wA wB) = SubSel TC TC (merge_sub_r wA) (merge_sub_r wB)
merge_sub_r (MgBra TA TA wA wB) = SubBra TA TA (merge_sub_r wA) (merge_sub_r wB)
merge_sub_r (MgBra TA TB wA wB) = SubBra TA TB (merge_sub_r wA) (merge_sub_r wB)
merge_sub_r (MgBra TA TC wA wB) = SubBra TA TC (merge_sub_r wA) (merge_sub_r wB)
merge_sub_r (MgBra TB TA wA wB) = SubBra TB TA (merge_sub_r wA) (merge_sub_r wB)
merge_sub_r (MgBra TB TB wA wB) = SubBra TB TB (merge_sub_r wA) (merge_sub_r wB)
merge_sub_r (MgBra TB TC wA wB) = SubBra TB TC (merge_sub_r wA) (merge_sub_r wB)
merge_sub_r (MgBra TC TA wA wB) = SubBra TC TA (merge_sub_r wA) (merge_sub_r wB)
merge_sub_r (MgBra TC TB wA wB) = SubBra TC TB (merge_sub_r wA) (merge_sub_r wB)
merge_sub_r (MgBra TC TC wA wB) = SubBra TC TC (merge_sub_r wA) (merge_sub_r wB)

active_a_defined : WF g -> is_err (project g RA) = F
active_a_defined WFEnd = Refl
active_a_defined (WFAB t w2) = Refl
active_a_defined (WFBA t w2) = Refl
active_a_defined (WFBC t w2) = active_a_defined w2
active_a_defined (WFAC t w2) = Refl
active_a_defined (WFCho tL wL tR wR mg) = Refl

active_b_defined : WF g -> is_err (project g RB) = F
active_b_defined WFEnd = Refl
active_b_defined (WFAB t w2) = Refl
active_b_defined (WFBA t w2) = Refl
active_b_defined (WFBC t w2) = Refl
active_b_defined (WFAC t w2) = active_b_defined w2
active_b_defined (WFCho tL wL tR wR mg) = Refl

data AllDefined : Global -> Type where
  MkAllDefined : is_err (project g RA) = F -> is_err (project g RB) = F -> is_err (project g RC) = F -> AllDefined g

all_projections_defined : WF g -> AllDefined g
all_projections_defined w = MkAllDefined (active_a_defined w) (active_b_defined w) (bystander_defined w)

data GStep : Global -> Global -> Type where
  GStMsg  : GStep (GMsg from to t k) k
  GStChoL : GStep (GCho from to tL gL tR gR) gL
  GStChoR : GStep (GCho from to tL gL tR gR) gR

gstep_preserves : WF g -> GStep g g2 -> WF g2
gstep_preserves (WFAB t w2) GStMsg = w2
gstep_preserves (WFBA t w2) GStMsg = w2
gstep_preserves (WFBC t w2) GStMsg = w2
gstep_preserves (WFAC t w2) GStMsg = w2
gstep_preserves (WFCho tL wL tR wR mg) GStChoL = wL
gstep_preserves (WFCho tL wL tR wR mg) GStChoR = wR

data GRun : Global -> Global -> Type where
  GRDone : GRun g g
  GRStep : GStep g gm -> GRun gm g2 -> GRun g g2

branch_terminates : WF g -> GRun g GEnd
branch_terminates WFEnd = GRDone
branch_terminates (WFAB t w2) = GRStep GStMsg (branch_terminates w2)
branch_terminates (WFBA t w2) = GRStep GStMsg (branch_terminates w2)
branch_terminates (WFBC t w2) = GRStep GStMsg (branch_terminates w2)
branch_terminates (WFAC t w2) = GRStep GStMsg (branch_terminates w2)
branch_terminates (WFCho tL wL tR wR mg) = GRStep GStChoL (branch_terminates wL)

cstep_preserves : Coherent g -> GStep g g2 -> Coherent g2
cstep_preserves (CoAB t w2) GStMsg = w2
cstep_preserves (CoBA t w2) GStMsg = w2
cstep_preserves (CoCho tL wL tR wR) GStChoL = wL
cstep_preserves (CoCho tL wL tR wR) GStChoR = wR

duality_preserved : Coherent g -> GStep g g2 -> project g2 RA = dual (project g2 RB)
duality_preserved w st = choice_duality (cstep_preserves w st)

data LStep : Local -> Local -> Type where
  LStSend : LStep (LSend t k) k
  LStRecv : LStep (LRecv t k) k
  LStSelL : LStep (LSel tL kL tR kR) kL
  LStBraL : LStep (LBra tL kL tR kR) kL

proj_sender_steps : (fr : Role) -> (to : Role) -> (t : Tag) -> (k : Global) -> LStep (project (GMsg fr to t k) fr) (project k fr)
proj_sender_steps RA to t k = LStSend
proj_sender_steps RB to t k = LStSend
proj_sender_steps RC to t k = LStSend

proj_chooser_steps : (fr : Role) -> (to : Role) -> (tL : Tag) -> (gL : Global) -> (tR : Tag) -> (gR : Global) -> LStep (project (GCho fr to tL gL tR gR) fr) (project gL fr)
proj_chooser_steps RA to tL gL tR gR = LStSelL
proj_chooser_steps RB to tL gL tR gR = LStSelL
proj_chooser_steps RC to tL gL tR gR = LStSelL

proj_receiver_steps : (fr : Role) -> (to : Role) -> (t : Tag) -> (k : Global) -> role_eq fr to = F -> LStep (project (GMsg fr to t k) to) (project k to)
proj_receiver_steps RA RA t k Refl impossible
proj_receiver_steps RA RB t k neq = LStRecv
proj_receiver_steps RA RC t k neq = LStRecv
proj_receiver_steps RB RA t k neq = LStRecv
proj_receiver_steps RB RB t k Refl impossible
proj_receiver_steps RB RC t k neq = LStRecv
proj_receiver_steps RC RA t k neq = LStRecv
proj_receiver_steps RC RB t k neq = LStRecv
proj_receiver_steps RC RC t k Refl impossible

proj_offerer_steps : (fr : Role) -> (to : Role) -> (tL : Tag) -> (gL : Global) -> (tR : Tag) -> (gR : Global) -> role_eq fr to = F -> LStep (project (GCho fr to tL gL tR gR) to) (project gL to)
proj_offerer_steps RA RA tL gL tR gR Refl impossible
proj_offerer_steps RA RB tL gL tR gR neq = LStBraL
proj_offerer_steps RA RC tL gL tR gR neq = LStBraL
proj_offerer_steps RB RA tL gL tR gR neq = LStBraL
proj_offerer_steps RB RB tL gL tR gR Refl impossible
proj_offerer_steps RB RC tL gL tR gR neq = LStBraL
proj_offerer_steps RC RA tL gL tR gR neq = LStBraL
proj_offerer_steps RC RB tL gL tR gR neq = LStBraL
proj_offerer_steps RC RC tL gL tR gR Refl impossible

proj_bystander_msg : (fr : Role) -> (to : Role) -> (r : Role) -> (t : Tag) -> (k : Global) -> role_eq fr r = F -> role_eq to r = F -> project (GMsg fr to t k) r = project k r
proj_bystander_msg fr to r t k p1 p2 = rewrite p1 in rewrite p2 in Refl

bystander_cho_sub_left : WF (GCho RA RB tL gL tR gR) -> Sub (project (GCho RA RB tL gL tR gR) RC) (project gL RC)
bystander_cho_sub_left (WFCho tL2 wL tR2 wR mg) = merge_sub_l mg

bystander_cho_sub_right : WF (GCho RA RB tL gL tR gR) -> Sub (project (GCho RA RB tL gL tR gR) RC) (project gR RC)
bystander_cho_sub_right (WFCho tL2 wL tR2 wR mg) = merge_sub_r mg

sub_trans : Sub a b -> Sub b c -> Sub a c
sub_trans SubEnd SubEnd = SubEnd
sub_trans SubErr SubErr = SubErr
sub_trans (SubSend t p) (SubSend t q) = SubSend t (sub_trans p q)
sub_trans (SubRecv t p) (SubRecv t q) = SubRecv t (sub_trans p q)
sub_trans (SubSel a b pA pB) (SubSel a b qA qB) = SubSel a b (sub_trans pA qA) (sub_trans pB qB)
sub_trans (SubBra a b pA pB) (SubBra a b qA qB) = SubBra a b (sub_trans pA qA) (sub_trans pB qB)
sub_trans (SubBra a b pA pB) SubBraL = SubBraLcov pA
sub_trans (SubBra a b pA pB) (SubBraLcov qk) = SubBraLcov (sub_trans pA qk)
sub_trans (SubBra a b pA pB) SubBraR = SubBraRcov pB
sub_trans (SubBra a b pA pB) (SubBraRcov qk) = SubBraRcov (sub_trans pB qk)
sub_trans SubBraL (SubRecv t2 q) = SubBraLcov q
sub_trans (SubBraLcov pk) (SubRecv t2 q) = SubBraLcov (sub_trans pk q)
sub_trans SubBraR (SubRecv t2 q) = SubBraRcov q
sub_trans (SubBraRcov pk) (SubRecv t2 q) = SubBraRcov (sub_trans pk q)
