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

role_after : Global -> Role -> Role -> Role -> Local
role_after g p q r = case role_eq p r of
  T => perform_send (project g r)
  F => case role_eq q r of
    T => perform_recv (project g r)
    F => project g r

step_config : Global -> Role -> Role -> Config
step_config g p q = MkCfg (role_after g p q RA) (role_after g p q RB) (role_after g p q RC)

role_fidelity : (p : Role) -> (q : Role) -> (t : Tag) -> (k : Global) -> (r : Role) -> role_after (GMsg p q t k) p q r = project k r
role_fidelity RA RA t k RA = Refl
role_fidelity RA RA t k RB = Refl
role_fidelity RA RA t k RC = Refl
role_fidelity RA RB t k RA = Refl
role_fidelity RA RB t k RB = Refl
role_fidelity RA RB t k RC = Refl
role_fidelity RA RC t k RA = Refl
role_fidelity RA RC t k RB = Refl
role_fidelity RA RC t k RC = Refl
role_fidelity RB RA t k RA = Refl
role_fidelity RB RA t k RB = Refl
role_fidelity RB RA t k RC = Refl
role_fidelity RB RB t k RA = Refl
role_fidelity RB RB t k RB = Refl
role_fidelity RB RB t k RC = Refl
role_fidelity RB RC t k RA = Refl
role_fidelity RB RC t k RB = Refl
role_fidelity RB RC t k RC = Refl
role_fidelity RC RA t k RA = Refl
role_fidelity RC RA t k RB = Refl
role_fidelity RC RA t k RC = Refl
role_fidelity RC RB t k RA = Refl
role_fidelity RC RB t k RB = Refl
role_fidelity RC RB t k RC = Refl
role_fidelity RC RC t k RA = Refl
role_fidelity RC RC t k RB = Refl
role_fidelity RC RC t k RC = Refl

mkcfg_cong : a1 = b1 -> a2 = b2 -> a3 = b3 -> MkCfg a1 a2 a3 = MkCfg b1 b2 b3
mkcfg_cong e1 e2 e3 = rewrite e1 in rewrite e2 in rewrite e3 in Refl

config_fidelity : (p : Role) -> (q : Role) -> (t : Tag) -> (k : Global) -> step_config (GMsg p q t k) p q = config k
config_fidelity p q t k = mkcfg_cong (role_fidelity p q t k RA) (role_fidelity p q t k RB) (role_fidelity p q t k RC)
