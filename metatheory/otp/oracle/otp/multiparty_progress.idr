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

teq : Tag -> Tag -> B
teq TA TA = T
teq TA TB = F
teq TA TC = F
teq TB TA = F
teq TB TB = T
teq TB TC = F
teq TC TA = F
teq TC TB = F
teq TC TC = T

teq_refl : (t : Tag) -> teq t t = T
teq_refl TA = Refl
teq_refl TB = Refl
teq_refl TC = Refl

project : Global -> Role -> Local
project GEnd r = LEnd
project (GMsg from to t k) r = case role_eq from r of
  T => LSend t (project k r)
  F => case role_eq to r of
    T => LRecv t (project k r)
    F => project k r

tmatches : Local -> Local -> B
tmatches LEnd r = F
tmatches (LSend t k) LEnd = F
tmatches (LSend t k) (LSend t2 k2) = F
tmatches (LSend t k) (LRecv t2 k2) = teq t t2
tmatches (LRecv t k) r = F

sender_ready : (p : Role) -> (q : Role) -> (t : Tag) -> (k : Global) -> project (GMsg p q t k) p = LSend t (project k p)
sender_ready RA q t k = Refl
sender_ready RB q t k = Refl
sender_ready RC q t k = Refl

receiver_ready : (p : Role) -> (q : Role) -> (t : Tag) -> (k : Global) -> role_eq p q = F -> project (GMsg p q t k) q = LRecv t (project k q)
receiver_ready RA RA t k Refl impossible
receiver_ready RA RB t k neq = Refl
receiver_ready RA RC t k neq = Refl
receiver_ready RB RA t k neq = Refl
receiver_ready RB RB t k Refl impossible
receiver_ready RB RC t k neq = Refl
receiver_ready RC RA t k neq = Refl
receiver_ready RC RB t k neq = Refl
receiver_ready RC RC t k Refl impossible

bystander_transparent : (p : Role) -> (q : Role) -> (t : Tag) -> (k : Global) -> (r : Role) -> role_eq p r = F -> role_eq q r = F -> project (GMsg p q t k) r = project k r
bystander_transparent RA RA t k RA Refl nqr impossible
bystander_transparent RA RA t k RB npr nqr = Refl
bystander_transparent RA RA t k RC npr nqr = Refl
bystander_transparent RA RB t k RA Refl nqr impossible
bystander_transparent RA RB t k RB npr Refl impossible
bystander_transparent RA RB t k RC npr nqr = Refl
bystander_transparent RA RC t k RA Refl nqr impossible
bystander_transparent RA RC t k RB npr nqr = Refl
bystander_transparent RA RC t k RC npr Refl impossible
bystander_transparent RB RA t k RA npr Refl impossible
bystander_transparent RB RA t k RB Refl nqr impossible
bystander_transparent RB RA t k RC npr nqr = Refl
bystander_transparent RB RB t k RA npr nqr = Refl
bystander_transparent RB RB t k RB Refl nqr impossible
bystander_transparent RB RB t k RC npr nqr = Refl
bystander_transparent RB RC t k RA npr nqr = Refl
bystander_transparent RB RC t k RB Refl nqr impossible
bystander_transparent RB RC t k RC npr Refl impossible
bystander_transparent RC RA t k RA npr Refl impossible
bystander_transparent RC RA t k RB npr nqr = Refl
bystander_transparent RC RA t k RC Refl nqr impossible
bystander_transparent RC RB t k RA npr nqr = Refl
bystander_transparent RC RB t k RB npr Refl impossible
bystander_transparent RC RB t k RC Refl nqr impossible
bystander_transparent RC RC t k RA npr nqr = Refl
bystander_transparent RC RC t k RB npr nqr = Refl
bystander_transparent RC RC t k RC Refl nqr impossible

progress : (p : Role) -> (q : Role) -> (t : Tag) -> (k : Global) -> role_eq p q = F -> tmatches (project (GMsg p q t k) p) (project (GMsg p q t k) q) = T
progress p q t k neq = rewrite sender_ready p q t k in rewrite receiver_ready p q t k neq in teq_refl t
