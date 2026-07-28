%default total

data Role = RA | RB | RC
data Tag = TA | TB | TC
data B = F | T

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

lsend_cong : (t : Tag) -> a = b -> LSend t a = LSend t b
lsend_cong t prf = cong (LSend t) prf

lrecv_cong : (t : Tag) -> a = b -> LRecv t a = LRecv t b
lrecv_cong t prf = cong (LRecv t) prf

data Bilateral : Global -> Type where
  BiEnd : Bilateral GEnd
  BiAB : (t : Tag) -> Bilateral k -> Bilateral (GMsg RA RB t k)
  BiBA : (t : Tag) -> Bilateral k -> Bilateral (GMsg RB RA t k)

bystander_ab : Bilateral g -> project g RC = LEnd
bystander_ab BiEnd = Refl
bystander_ab (BiAB t w2) = bystander_ab w2
bystander_ab (BiBA t w2) = bystander_ab w2

bilateral_duality : Bilateral g -> project g RA = dual (project g RB)
bilateral_duality BiEnd = Refl
bilateral_duality (BiAB t w2) = lsend_cong t (bilateral_duality w2)
bilateral_duality (BiBA t w2) = lrecv_cong t (bilateral_duality w2)
