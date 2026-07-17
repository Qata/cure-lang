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

data GStep : Global -> Global -> Type where
  GFire : GStep (GMsg from to t k) k

twoparty_preserved : TwoParty g -> GStep g g2 -> TwoParty g2
twoparty_preserved wf GFire = case wf of
  TPAB t wf2 => wf2
  TPBA t wf2 => wf2

data GProgress : Global -> Type where
  GPDone : GProgress GEnd
  GPFire : GProgress (GMsg from to t k)

global_progress : TwoParty g -> GProgress g
global_progress TPEnd = GPDone
global_progress (TPAB t wf2) = GPFire
global_progress (TPBA t wf2) = GPFire

data GRun : Global -> Global -> Type where
  GRDone : GRun g g
  GRStep : GStep g gm -> GRun gm g2 -> GRun g g2

grun_fire : (from : Role) -> (to : Role) -> (t : Tag) -> GRun k GEnd -> GRun (GMsg from to t k) GEnd
grun_fire from to t tail = GRStep GFire tail

twoparty_terminates : TwoParty g -> GRun g GEnd
twoparty_terminates TPEnd = GRDone
twoparty_terminates (TPAB t wf2) = grun_fire RA RB t (twoparty_terminates wf2)
twoparty_terminates (TPBA t wf2) = grun_fire RB RA t (twoparty_terminates wf2)
