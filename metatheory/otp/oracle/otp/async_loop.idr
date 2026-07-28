%default total

data Msg = MGet | MPut | MVal | MAck
data Local = LEnd | LSend Msg Local | LRecv Msg Local | LMu Local | LVar

subst : Local -> Local -> Local
subst LEnd s = LEnd
subst (LSend m k) s = LSend m (subst k s)
subst (LRecv m k) s = LRecv m (subst k s)
subst (LMu body) s = LMu body
subst LVar s = s

data Buf = BEmpty | BFull Msg
data Config = MkConfig Local Local Buf Buf

data AStep : Config -> Config -> Type where
  ASendA   : AStep (MkConfig (LSend t ka) b BEmpty ba) (MkConfig ka b (BFull t) ba)
  ARecvB   : AStep (MkConfig a (LRecv t kb) (BFull t) ba) (MkConfig a kb BEmpty ba)
  ASendB   : AStep (MkConfig a (LSend t kb) ab BEmpty) (MkConfig a kb ab (BFull t))
  ARecvA   : AStep (MkConfig (LRecv t ka) b ab (BFull t)) (MkConfig ka b ab BEmpty)
  AUnfoldA : AStep (MkConfig (LMu body) b ab ba) (MkConfig (subst body (LMu body)) b ab ba)
  AUnfoldB : AStep (MkConfig a (LMu body) ab ba) (MkConfig a (subst body (LMu body)) ab ba)

data ARun : Config -> Config -> Type where
  ARDone : ARun c c
  ARStep : AStep c cm -> ARun cm c2 -> ARun c c2

Srv : Local
Srv = LMu (LRecv MGet (LSend MVal LVar))
Clt : Local
Clt = LMu (LSend MGet (LRecv MVal LVar))

loops_n : (n : Nat) -> ARun (MkConfig Clt Srv BEmpty BEmpty) (MkConfig Clt Srv BEmpty BEmpty)
loops_n Z = ARDone
loops_n (S m) = ARStep AUnfoldA (ARStep AUnfoldB (ARStep ASendA (ARStep ARecvB (ARStep ASendB (ARStep ARecvA (loops_n m))))))
