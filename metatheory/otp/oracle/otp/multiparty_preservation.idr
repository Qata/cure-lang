%default total

data Role = RA | RB | RC
data Tag = TA | TB | TC
data B = F | T
data Global = GEnd | GMsg Role Role Tag Global
data Local = LEnd | LSend Tag Local | LRecv Tag Local

role_eq : Role -> Role -> B
role_eq RA RA = T
role_eq RA RB = F
role_eq RA RC = F
role_eq RB RA = F
role_eq RB RB = T
role_eq RB RC = F
role_eq RC RA = F
role_eq RC RB = F
role_eq RC RC = T

project : Global -> Role -> Local
project GEnd r = LEnd
project (GMsg from to t k) r = case role_eq from r of
  T => LSend t (project k r)
  F => case role_eq to r of
    T => LRecv t (project k r)
    F => project k r

lstep : Local -> Local
lstep LEnd = LEnd
lstep (LSend t c) = c
lstep (LRecv t c) = c

after_step : Global -> Role -> Local
after_step GEnd r = LEnd
after_step (GMsg from to t k) r = case role_eq from r of
  T => lstep (project (GMsg from to t k) r)
  F => case role_eq to r of
    T => lstep (project (GMsg from to t k) r)
    F => project (GMsg from to t k) r

subject_reduction : (p : Role) -> (q : Role) -> (t : Tag) -> (k : Global) -> (r : Role) -> after_step (GMsg p q t k) r = project k r
subject_reduction RA RA t k RA = Refl
subject_reduction RA RA t k RB = Refl
subject_reduction RA RA t k RC = Refl
subject_reduction RA RB t k RA = Refl
subject_reduction RA RB t k RB = Refl
subject_reduction RA RB t k RC = Refl
subject_reduction RA RC t k RA = Refl
subject_reduction RA RC t k RB = Refl
subject_reduction RA RC t k RC = Refl
subject_reduction RB RA t k RA = Refl
subject_reduction RB RA t k RB = Refl
subject_reduction RB RA t k RC = Refl
subject_reduction RB RB t k RA = Refl
subject_reduction RB RB t k RB = Refl
subject_reduction RB RB t k RC = Refl
subject_reduction RB RC t k RA = Refl
subject_reduction RB RC t k RB = Refl
subject_reduction RB RC t k RC = Refl
subject_reduction RC RA t k RA = Refl
subject_reduction RC RA t k RB = Refl
subject_reduction RC RA t k RC = Refl
subject_reduction RC RB t k RA = Refl
subject_reduction RC RB t k RB = Refl
subject_reduction RC RB t k RC = Refl
subject_reduction RC RC t k RA = Refl
subject_reduction RC RC t k RB = Refl
subject_reduction RC RC t k RC = Refl
