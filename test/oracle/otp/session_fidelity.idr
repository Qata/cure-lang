%default total

data Role = RA | RB | RC
data Tag = TA | TB | TC
data B = F | T
data Global = GEnd | GMsg Role Role Tag Global
data Local = LEnd | LSend Role Tag Local | LRecv Role Tag Local
data Config = MkCfg Local Local Local

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
  T => LSend to t (project k r)
  F => case role_eq to r of
    T => LRecv from t (project k r)
    F => project k r

config : Global -> Config
config g = MkCfg (project g RA) (project g RB) (project g RC)

perform_send : Local -> Local
perform_send LEnd = LEnd
perform_send (LSend to t k) = k
perform_send (LRecv fr t k) = LRecv fr t k

perform_recv : Local -> Local
perform_recv LEnd = LEnd
perform_recv (LSend to t k) = LSend to t k
perform_recv (LRecv fr t k) = k

sender_forced : (p : Role) -> (q : Role) -> (t : Tag) -> (k : Global) -> project (GMsg p q t k) p = LSend q t (project k p)
sender_forced RA q t k = Refl
sender_forced RB q t k = Refl
sender_forced RC q t k = Refl

receiver_forced : (p : Role) -> (q : Role) -> (t : Tag) -> (k : Global) -> role_eq p q = F -> project (GMsg p q t k) q = LRecv p t (project k q)
receiver_forced RA RA t k Refl impossible
receiver_forced RA RB t k neq = Refl
receiver_forced RA RC t k neq = Refl
receiver_forced RB RA t k neq = Refl
receiver_forced RB RB t k Refl impossible
receiver_forced RB RC t k neq = Refl
receiver_forced RC RA t k neq = Refl
receiver_forced RC RB t k neq = Refl
receiver_forced RC RC t k Refl impossible

bystander_idle : (p : Role) -> (q : Role) -> (t : Tag) -> (k : Global) -> (r : Role) -> role_eq p r = F -> role_eq q r = F -> project (GMsg p q t k) r = project k r
bystander_idle RA RA t k RA Refl nq impossible
bystander_idle RA RA t k RB np nq = Refl
bystander_idle RA RA t k RC np nq = Refl
bystander_idle RA RB t k RA Refl nq impossible
bystander_idle RA RB t k RB np Refl impossible
bystander_idle RA RB t k RC np nq = Refl
bystander_idle RA RC t k RA Refl nq impossible
bystander_idle RA RC t k RB np nq = Refl
bystander_idle RA RC t k RC np Refl impossible
bystander_idle RB RA t k RA np Refl impossible
bystander_idle RB RA t k RB Refl nq impossible
bystander_idle RB RA t k RC np nq = Refl
bystander_idle RB RB t k RA np nq = Refl
bystander_idle RB RB t k RB Refl nq impossible
bystander_idle RB RB t k RC np nq = Refl
bystander_idle RB RC t k RA np nq = Refl
bystander_idle RB RC t k RB Refl nq impossible
bystander_idle RB RC t k RC np Refl impossible
bystander_idle RC RA t k RA np Refl impossible
bystander_idle RC RA t k RB np nq = Refl
bystander_idle RC RA t k RC Refl nq impossible
bystander_idle RC RB t k RA np nq = Refl
bystander_idle RC RB t k RB np Refl impossible
bystander_idle RC RB t k RC Refl nq impossible
bystander_idle RC RC t k RA np nq = Refl
bystander_idle RC RC t k RB np nq = Refl
bystander_idle RC RC t k RC Refl nq impossible

sender_lands : (p : Role) -> (q : Role) -> (t : Tag) -> (k : Global) -> perform_send (project (GMsg p q t k) p) = project k p
sender_lands p q t k = rewrite sender_forced p q t k in Refl

receiver_lands : (p : Role) -> (q : Role) -> (t : Tag) -> (k : Global) -> role_eq p q = F -> perform_recv (project (GMsg p q t k) q) = project k q
receiver_lands p q t k neq = rewrite receiver_forced p q t k neq in Refl

fidelity_ab : (t : Tag) -> (k : Global) -> MkCfg (perform_send (project (GMsg RA RB t k) RA)) (perform_recv (project (GMsg RA RB t k) RB)) (project (GMsg RA RB t k) RC) = config k
fidelity_ab t k = rewrite sender_lands RA RB t k in rewrite receiver_lands RA RB t k Refl in rewrite bystander_idle RA RB t k RC Refl Refl in Refl
