%default total

data Role = RA | RB
data Tag = TA | TB | TC
data B = F | T

role_eq : Role -> Role -> B
role_eq RA RA = T
role_eq RA RB = F
role_eq RB RA = F
role_eq RB RB = T

data Global = GEnd | GMsg Role Role Tag Global
data Local = LEnd | LSend Tag Local | LRecv Tag Local

dual : Local -> Local
dual LEnd = LEnd
dual (LSend t k) = LRecv t (dual k)
dual (LRecv t k) = LSend t (dual k)

project : Global -> Role -> Local
project GEnd r = LEnd
project (GMsg from to t k) r = case role_eq from r of
  T => LSend t (project k r)
  F => case role_eq to r of
    T => LRecv t (project k r)
    F => project k r

data TwoParty : Global -> Type where
  TPEnd : TwoParty GEnd
  TPAB : (t : Tag) -> TwoParty k -> TwoParty (GMsg RA RB t k)
  TPBA : (t : Tag) -> TwoParty k -> TwoParty (GMsg RB RA t k)

projection_duality : TwoParty g -> project g RA = dual (project g RB)
projection_duality TPEnd = Refl
projection_duality (TPAB t wf2) = cong (LSend t) (projection_duality wf2)
projection_duality (TPBA t wf2) = cong (LRecv t) (projection_duality wf2)
