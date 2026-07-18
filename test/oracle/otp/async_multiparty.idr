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

exchange_ac : (lb : Local) -> (t : Tag) -> (ka : Local) -> (kc : Local) ->
              ARun (MkConfig (LSendTo RC t ka) lb (LRecvFrom RA t kc) BEmpty) (MkConfig ka lb kc BEmpty)
exchange_ac lb t ka kc = ARStep ASendA (ARStep ARecvC ARDone)
