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

data TB2 = F | T
data Role = RA | RB
role_eq : Role -> Role -> TB2
role_eq RA RA = T
role_eq RA RB = F
role_eq RB RA = F
role_eq RB RB = T

mutual
  data Global = GEnd | GMsg Role Role Tag Global | GCho Role Role GBranches
  data GBranches = GBNil | GBCons Tag Global GBranches

mutual
  project : Global -> Role -> Local
  project GEnd r = LEnd
  project (GMsg from to t k) r = case role_eq from r of
    T => LSend t (project k r)
    F => case role_eq to r of
      T => LRecv t (project k r)
      F => LEnd
  project (GCho from to gbs) r = case role_eq from r of
    T => LSel (project_gbranches gbs r)
    F => case role_eq to r of
      T => LBra (project_gbranches gbs r)
      F => LEnd
  project_gbranches : GBranches -> Role -> Branches
  project_gbranches GBNil r = BNil
  project_gbranches (GBCons t g rest) r = BCons t (project g r) (project_gbranches rest r)

mutual
  data Coherent : Global -> Type where
    CoEnd : Coherent GEnd
    CoAB : (t : Tag) -> Coherent k -> Coherent (GMsg RA RB t k)
    CoBA : (t : Tag) -> Coherent k -> Coherent (GMsg RB RA t k)
    CoCho : CoherentB gbs -> Coherent (GCho RA RB gbs)
  data CoherentB : GBranches -> Type where
    CoBNil : CoherentB GBNil
    CoBCons : (t : Tag) -> Coherent g -> CoherentB rest -> CoherentB (GBCons t g rest)

mutual
  projection_duality : Coherent g -> project g RA = dual (project g RB)
  projection_duality CoEnd = Refl
  projection_duality (CoAB t w2) = cong (LSend t) (projection_duality w2)
  projection_duality (CoBA t w2) = cong (LRecv t) (projection_duality w2)
  projection_duality (CoCho wb) = cong LSel (projection_gbranches_duality wb)
  projection_gbranches_duality : CoherentB gbs -> project_gbranches gbs RA = dual_branches (project_gbranches gbs RB)
  projection_gbranches_duality CoBNil = Refl
  projection_gbranches_duality (CoBCons t wg wrest) = rewrite projection_duality wg in rewrite projection_gbranches_duality wrest in Refl
