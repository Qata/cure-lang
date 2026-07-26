%default total

data Tag = TA | TB
data Role = RA | RB | RC
data Local = LEnd | LSendTo Role Tag Local | LRecvFrom Role Tag Local
data Buf = BEmpty | BFull Role Role Tag
data Config = MkConfig Local Local Local Buf

data AStep : Config -> Config -> Type where
  ASendA : AStep (MkConfig (LSendTo to t ka) lb lc BEmpty) (MkConfig ka lb lc (BFull RA to t))
  ASendB : AStep (MkConfig la (LSendTo to t kb) lc BEmpty) (MkConfig la kb lc (BFull RB to t))
  ASendC : AStep (MkConfig la lb (LSendTo to t kc) BEmpty) (MkConfig la lb kc (BFull RC to t))
  ARecvA : AStep (MkConfig (LRecvFrom from t ka) lb lc (BFull from RA t)) (MkConfig ka lb lc BEmpty)
  ARecvB : AStep (MkConfig la (LRecvFrom from t kb) lc (BFull from RB t)) (MkConfig la kb lc BEmpty)
  ARecvC : AStep (MkConfig la lb (LRecvFrom from t kc) (BFull from RC t)) (MkConfig la lb kc BEmpty)

data ARun : Config -> Config -> Type where
  ARDone : ARun c c
  ARStep : AStep c cm -> ARun cm c2 -> ARun c c2

data Global = GEnd | GAB Tag Global | GBA Tag Global | GAC Tag Global | GCA Tag Global | GBC Tag Global | GCB Tag Global

project : Global -> Role -> Local
project GEnd r = LEnd
project (GAB t k) RA = LSendTo RB t (project k RA)
project (GAB t k) RB = LRecvFrom RA t (project k RB)
project (GAB t k) RC = project k RC
project (GBA t k) RA = LRecvFrom RB t (project k RA)
project (GBA t k) RB = LSendTo RA t (project k RB)
project (GBA t k) RC = project k RC
project (GAC t k) RA = LSendTo RC t (project k RA)
project (GAC t k) RB = project k RB
project (GAC t k) RC = LRecvFrom RA t (project k RC)
project (GCA t k) RA = LRecvFrom RC t (project k RA)
project (GCA t k) RB = project k RB
project (GCA t k) RC = LSendTo RA t (project k RC)
project (GBC t k) RA = project k RA
project (GBC t k) RB = LSendTo RC t (project k RB)
project (GBC t k) RC = LRecvFrom RB t (project k RC)
project (GCB t k) RA = project k RA
project (GCB t k) RB = LRecvFrom RC t (project k RB)
project (GCB t k) RC = LSendTo RB t (project k RC)

config : Global -> Config
config g = MkConfig (project g RA) (project g RB) (project g RC) BEmpty

async_global_terminates : (g : Global) -> ARun (config g) (config GEnd)
async_global_terminates GEnd = ARDone
async_global_terminates (GAB t k) = ARStep ASendA (ARStep ARecvB (async_global_terminates k))
async_global_terminates (GBA t k) = ARStep ASendB (ARStep ARecvA (async_global_terminates k))
async_global_terminates (GAC t k) = ARStep ASendA (ARStep ARecvC (async_global_terminates k))
async_global_terminates (GCA t k) = ARStep ASendC (ARStep ARecvA (async_global_terminates k))
async_global_terminates (GBC t k) = ARStep ASendB (ARStep ARecvC (async_global_terminates k))
async_global_terminates (GCB t k) = ARStep ASendC (ARStep ARecvB (async_global_terminates k))
