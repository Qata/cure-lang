%default total

data Tag = TA | TB
data Local = LEnd | LSend Tag Local | LRecv Tag Local
data Buf = BEmpty | BFull Tag
data Config = MkConfig Local Local Buf Buf

data AStep : Config -> Config -> Type where
  ASendA : AStep (MkConfig (LSend t ka) b BEmpty ba) (MkConfig ka b (BFull t) ba)
  ARecvB : AStep (MkConfig a (LRecv t kb) (BFull t) ba) (MkConfig a kb BEmpty ba)
  ASendB : AStep (MkConfig a (LSend t kb) ab BEmpty) (MkConfig a kb ab (BFull t))
  ARecvA : AStep (MkConfig (LRecv t ka) b ab (BFull t)) (MkConfig ka b ab BEmpty)

data ARun : Config -> Config -> Type where
  ARDone : ARun c c
  ARStep : AStep c cm -> ARun cm c2 -> ARun c c2

exchange_ab : (t : Tag) -> (ka : Local) -> (kb : Local) ->
              ARun (MkConfig (LSend t ka) (LRecv t kb) BEmpty BEmpty) (MkConfig ka kb BEmpty BEmpty)
exchange_ab t ka kb = ARStep ASendA (ARStep ARecvB ARDone)

exchange_ba : (t : Tag) -> (ka : Local) -> (kb : Local) ->
              ARun (MkConfig (LRecv t ka) (LSend t kb) BEmpty BEmpty) (MkConfig ka kb BEmpty BEmpty)
exchange_ba t ka kb = ARStep ASendB (ARStep ARecvA ARDone)
